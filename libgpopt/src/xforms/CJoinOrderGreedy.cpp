//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2018 Pivotal Software Inc.
//
//	@filename:
//		CJoinOrderGreedy.cpp
//
//	@doc:
//		Implementation of cardinality-based join order generation with
//		delayed cross joins
//---------------------------------------------------------------------------

#include "gpos/base.h"

#include "gpos/io/COstreamString.h"
#include "gpos/string/CWStringDynamic.h"

#include "gpos/common/clibwrapper.h"
#include "gpos/common/CBitSet.h"

#include "gpopt/base/CDrvdPropScalar.h"
#include "gpopt/base/CColRefSetIter.h"
#include "gpopt/base/CUtils.h"
#include "gpopt/operators/ops.h"
#include "gpopt/operators/CPredicateUtils.h"
#include "gpopt/operators/CNormalizer.h"
#include "gpopt/xforms/CJoinOrderGreedy.h"

using namespace gpopt;


//---------------------------------------------------------------------------
//	@function:
//		CJoinOrderGreedy::CJoinOrderGreedy
//
//	@doc:
//		Ctor
//
//---------------------------------------------------------------------------
CJoinOrderGreedy::CJoinOrderGreedy
	(
	IMemoryPool *pmp,
	CExpressionArray *pdrgpexprComponents,
	CExpressionArray *pdrgpexprConjuncts
	)
	:
	CJoinOrder(pmp, pdrgpexprComponents, pdrgpexprConjuncts),
	m_pcompResult(NULL)
{
	m_ulNumEdgesRemaining = m_ulEdges;
#ifdef GPOS_DEBUG
	for (ULONG ul = 0; ul < m_ulComps; ul++)
	{
		GPOS_ASSERT(NULL != m_rgpcomp[ul]->m_pexpr->Pstats() &&
				"stats were not derived on input component");
	}
#endif // GPOS_DEBUG
}


//---------------------------------------------------------------------------
//	@function:
//		CJoinOrderGreedy::~CJoinOrderGreedy
//
//	@doc:
//		Dtor
//
//---------------------------------------------------------------------------
CJoinOrderGreedy::~CJoinOrderGreedy()
{
	CRefCount::SafeRelease(m_pcompResult);
}


//---------------------------------------------------------------------------
//	@function:
//		CJoinOrder::MarkUsedEdges
//
//	@doc:
//		Mark edges used by result component
//
//---------------------------------------------------------------------------
void
CJoinOrderGreedy::MarkUsedEdges()
{
	GPOS_ASSERT(NULL != m_pcompResult);

	CExpression *pexpr = m_pcompResult->m_pexpr;
	COperator::EOperatorId eopid = pexpr->Pop()->Eopid();
	if (0 == pexpr->Arity() ||
		(COperator::EopLogicalSelect != eopid && COperator::EopLogicalInnerJoin != eopid))
	{
		// result component does not have a scalar child, e.g. a Get node
		return;
	}

	CExpression *pexprScalar = (*pexpr) [pexpr->Arity() - 1];
	CExpressionArray *pdrgpexpr = CPredicateUtils::PdrgpexprConjuncts(m_mp, pexprScalar);
	const ULONG ulSize = pdrgpexpr->Size();

	for (ULONG ulEdge = 0; ulEdge < m_ulEdges; ulEdge++)
	{
		SEdge *pedge = m_rgpedge[ulEdge];
		if (pedge->m_fUsed)
		{
			continue;
		}

		for (ULONG ulPred = 0; ulPred < ulSize; ulPred++)
		{
			if ((*pdrgpexpr)[ulPred] == pedge->m_pexpr)
			{
				pedge->m_fUsed = true;
				m_ulNumEdgesRemaining--;
			}
		}
	}
	pdrgpexpr->Release();
}


// function to get the minimal cardinality join pair as the starting pair
CJoinOrder::SComponent *
CJoinOrderGreedy::GetStartingJoins()
{

	CDouble dMinRows(0.0);
	ULONG ul1Counter = 0;
	ULONG ul2Counter = 0;
	CJoinOrder::SComponent *pcompBest = GPOS_NEW(m_mp) SComponent(m_mp, NULL /*pexpr*/);

	for (ULONG ul1 = 0; ul1 < m_ulComps; ul1++)
	{
		for (ULONG ul2 = ul1+1; ul2 < m_ulComps; ul2++)
		{
			CJoinOrder::SComponent *pcompTemp = PcompCombine(m_rgpcomp[ul1], m_rgpcomp[ul2]);
			// exclude cross joins to be considered as late as possible in the join order
			if(CUtils::FCrossJoin(pcompTemp->m_pexpr))
			{
				pcompTemp->Release();
				continue;
			}
			DeriveStats(pcompTemp->m_pexpr);
			CDouble dRows = pcompTemp->m_pexpr->Pstats()->Rows();
			if (dMinRows <= 0 || dRows < dMinRows)
			{
				ul1Counter = ul1;
				ul2Counter = ul2;
				dMinRows = dRows;
				pcompTemp->AddRef();
				CRefCount::SafeRelease(pcompBest);
				pcompBest = pcompTemp;
			}
			pcompTemp->Release();
		}
	}

	if((ul1Counter == 0) && (ul2Counter==0))
	{
		pcompBest->Release();
		return NULL;
	}

	SComponent *comp1 = m_rgpcomp[ul1Counter];
	comp1->m_fUsed = true;
	SComponent *comp2 = m_rgpcomp[ul2Counter];
	comp2->m_fUsed = true;
	pcompBest->m_fUsed = true;

	return pcompBest;

}

//---------------------------------------------------------------------------
//	@function:
//		CJoinOrderGreedy::PexprExpand
//
//	@doc:
//		Create join order
//
//---------------------------------------------------------------------------
CExpression *
CJoinOrderGreedy::PexprExpand()
{
	GPOS_ASSERT(NULL == m_pcompResult && "join order is already expanded");

	ULONG ulCoveredComps = 0;
	m_pcompResult = GetStartingJoins();

	if(NULL != m_pcompResult)
	{
		ulCoveredComps = 2;
		MarkUsedEdges();
	}
	else
	{
		m_pcompResult = GPOS_NEW(m_mp) SComponent(m_mp, NULL /*pexpr*/);
	}

	while (ulCoveredComps < m_ulComps)
	{
		CDouble dMinRows(0.0);
		SComponent *pcompBest = NULL; // best component to be added to current result
		SComponent *pcompBestResult = NULL; // result after adding best component

		CBitSetIter edge_iter(*(m_pcompResult->m_edge_set));
		CBitSet *b = GPOS_NEW(m_mp) CBitSet(m_mp);

		//GetConnectedNodes();

		// Compute list of connected nodes of current join graph
		while (edge_iter.Advance())
		{
			SEdge *edge = m_rgpedge[edge_iter.Bit()];
			if (!edge->m_fUsed)
			{
				b->Union(edge->m_pbs);
				b->Difference(m_pcompResult->m_pbs);
			}
		}

		SComponent *pcompTemp = NULL;
		SComponent *pcompCurrent = NULL;
		ULONG best_comp_idx;

		// If candidate nodes set is non empty
		if (b->Size() > 0)
		{
			// Until we use all the candidate nodes in the join graph
			while (b->Size() > 0)
			{
				// Pick the node which will give the lowest cardinality when joined with the resultant join graph
				CBitSetIter comp_iter(*b);
				pcompBestResult = NULL;
				pcompBest = NULL;
				while (comp_iter.Advance())
				{
					pcompCurrent = m_rgpcomp[comp_iter.Bit()];
					pcompTemp = PcompCombine(m_pcompResult, pcompCurrent);

					//GetBestComponent()
					DeriveStats(pcompTemp->m_pexpr);
					CDouble dRows = pcompTemp->m_pexpr->Pstats()->Rows();

					if (NULL == pcompBestResult || dRows < dMinRows)
					{
						dMinRows = dRows;
						best_comp_idx = comp_iter.Bit();
						pcompTemp->AddRef();
						CRefCount::SafeRelease(pcompBestResult);
						pcompBest = pcompCurrent;
						pcompBestResult = pcompTemp;
					}
					pcompTemp->Release();
				}

				GPOS_ASSERT(NULL != pcompBestResult);

				//MarBestComponentAsUsed()
				// mark best component as used
				pcompBest->m_fUsed = true;
				m_pcompResult->Release();
				m_pcompResult = pcompBestResult;

				MarkUsedEdges();
				ulCoveredComps++;

				b->ExchangeClear(best_comp_idx);
			}
		}
		else
		{
			// Pick any cross joins if they exist
			pcompBestResult = NULL;
			pcompBest = NULL;
			for (ULONG ul = 0; ul < m_ulComps; ul++)
			{
				pcompCurrent = m_rgpcomp[ul];
				if (!pcompCurrent->m_fUsed)
				{
					//GetBestComponent()
					pcompTemp = PcompCombine(m_pcompResult, pcompCurrent);

					DeriveStats(pcompTemp->m_pexpr);
					CDouble dRows = pcompTemp->m_pexpr->Pstats()->Rows();

					if (NULL == pcompBestResult || dRows < dMinRows)
					{
						dMinRows = dRows;
						best_comp_idx = ul;
						pcompTemp->AddRef();
						CRefCount::SafeRelease(pcompBestResult);
						pcompBest = pcompCurrent;
						pcompBestResult = pcompTemp;
					}
					pcompTemp->Release();
				}
			}

			//MarBestComponentAsUsed()
			pcompBest->m_fUsed = true;
			m_pcompResult->Release();
			m_pcompResult = pcompBestResult;
			// mark used edges to avoid including them multiple times
			MarkUsedEdges();
			ulCoveredComps++;
		}
		b->Release();

	}
	GPOS_ASSERT(NULL != m_pcompResult->m_pexpr);

	CExpression *pexprResult = m_pcompResult->m_pexpr;
	pexprResult->AddRef();

	return pexprResult;
}

// EOF
