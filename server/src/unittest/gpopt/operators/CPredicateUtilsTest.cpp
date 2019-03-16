//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2011 EMC Corp.
//
//	@filename:
//		CPredicateUtilsTest.cpp
//
//	@doc:
//		Test for predicate utilities
//---------------------------------------------------------------------------
#include "gpopt/base/CColRefSetIter.h"
#include "gpopt/base/CUtils.h"
#include "gpopt/eval/CConstExprEvaluatorDefault.h"
#include "gpopt/operators/CExpressionPreprocessor.h"
#include "gpopt/operators/CLogicalInnerJoin.h"
#include "gpopt/operators/CPredicateUtils.h"

#include "unittest/base.h"
#include "unittest/gpopt/operators/CPredicateUtilsTest.h"
#include "unittest/gpopt/CTestUtils.h"

#include "naucrates/md/CMDIdGPDB.h"


//---------------------------------------------------------------------------
//	@function:
//		CPredicateUtilsTest::EresUnittest
//
//	@doc:
//		Unittest for predicate utilities
//
//---------------------------------------------------------------------------
GPOS_RESULT
CPredicateUtilsTest::EresUnittest()
{

	CUnittest rgut[] =
		{
		GPOS_UNITTEST_FUNC(CPredicateUtilsTest::EresUnittest_Conjunctions),
		GPOS_UNITTEST_FUNC(CPredicateUtilsTest::EresUnittest_Disjunctions),
		GPOS_UNITTEST_FUNC(CPredicateUtilsTest::EresUnittest_PlainEqualities)
		};

	return CUnittest::EresExecute(rgut, GPOS_ARRAY_SIZE(rgut));
}


//---------------------------------------------------------------------------
//	@function:
//		CPredicateUtilsTest::EresUnittest_Conjunctions
//
//	@doc:
//		Test extraction and construction of conjuncts
//
//---------------------------------------------------------------------------
GPOS_RESULT
CPredicateUtilsTest::EresUnittest_Conjunctions()
{
	CAutoMemoryPool amp;
	IMemoryPool *mp = amp.Pmp();

	// setup a file-based provider
	CMDProviderMemory *pmdp = CTestUtils::m_pmdpf;
	pmdp->AddRef();
	CMDAccessor mda(mp, CMDCache::Pcache(), CTestUtils::m_sysidDefault, pmdp);

	// install opt context in TLS
	CAutoOptCtxt aoc
					(
					mp,
					&mda,
					NULL,  /* pceeval */
					CTestUtils::GetCostModel(mp)
					);

	// build conjunction
	CExpressionArray *pdrgpexpr = GPOS_NEW(mp) CExpressionArray(mp);
	const ULONG ulConjs = 3;
	for (ULONG ul = 0; ul < ulConjs; ul++)
	{
		pdrgpexpr->Append(CUtils::PexprScalarConstBool(mp, true /*fValue*/));
	}
	CExpression *pexprConjunction = CUtils::PexprScalarBoolOp(mp, CScalarBoolOp::EboolopAnd, pdrgpexpr);
	
	// break into conjuncts
	CExpressionArray *pdrgpexprExtract = CPredicateUtils::PdrgpexprConjuncts(mp, pexprConjunction);
	GPOS_ASSERT(pdrgpexprExtract->Size() == ulConjs);
	
	// collapse into single conjunct
	CExpression *pexpr = CPredicateUtils::PexprConjunction(mp, pdrgpexprExtract);
	GPOS_ASSERT(NULL != pexpr);
	GPOS_ASSERT(CUtils::FScalarConstTrue(pexpr));
	pexpr->Release();
	
	// collapse empty input array to conjunct
	CExpression *pexprSingleton = CPredicateUtils::PexprConjunction(mp, NULL /*pdrgpexpr*/);
	GPOS_ASSERT(NULL != pexprSingleton);
	pexprSingleton->Release();

	pexprConjunction->Release();

	// conjunction on scalar comparisons
	CExpression *pexprGet = CTestUtils::PexprLogicalGet(mp);
	CColRefSet *pcrs = CDrvdPropRelational::GetRelationalProperties(pexprGet->PdpDerive())->PcrsOutput();
	CColRef *pcr1 = pcrs->PcrAny();
	CColRef *pcr2 = pcrs->PcrFirst();
	CExpression *pexprCmp1 = CUtils::PexprScalarCmp(mp, pcr1, pcr2, IMDType::EcmptEq);
	CExpression *pexprCmp2 = CUtils::PexprScalarCmp(mp, pcr1, CUtils::PexprScalarConstInt4(mp, 1 /*val*/), IMDType::EcmptEq);

	CExpression *pexprConj = CPredicateUtils::PexprConjunction(mp, pexprCmp1, pexprCmp2);
	pdrgpexprExtract = CPredicateUtils::PdrgpexprConjuncts(mp, pexprConj);
	GPOS_ASSERT(2 == pdrgpexprExtract->Size());
	pdrgpexprExtract->Release();

	pexprCmp1->Release();
	pexprCmp2->Release();
	pexprConj->Release();
	pexprGet->Release();

	return GPOS_OK;
}


//---------------------------------------------------------------------------
//	@function:
//		CPredicateUtilsTest::EresUnittest_Disjunctions
//
//	@doc:
//		Test extraction and construction of disjuncts
//
//---------------------------------------------------------------------------
GPOS_RESULT
CPredicateUtilsTest::EresUnittest_Disjunctions()
{
	CAutoMemoryPool amp;
	IMemoryPool *mp = amp.Pmp();

	// setup a file-based provider
	CMDProviderMemory *pmdp = CTestUtils::m_pmdpf;
	pmdp->AddRef();
	CMDAccessor mda(mp, CMDCache::Pcache(), CTestUtils::m_sysidDefault, pmdp);

	// install opt context in TLS
	CAutoOptCtxt aoc
					(
					mp,
					&mda,
					NULL,  /* pceeval */
					CTestUtils::GetCostModel(mp)
					);

	// build disjunction
	CExpressionArray *pdrgpexpr = GPOS_NEW(mp) CExpressionArray(mp);
	const ULONG ulDisjs = 3;
	for (ULONG ul = 0; ul < ulDisjs; ul++)
	{
		pdrgpexpr->Append(CUtils::PexprScalarConstBool(mp, false /*fValue*/));
	}
	CExpression *pexprDisjunction = CUtils::PexprScalarBoolOp(mp, CScalarBoolOp::EboolopOr, pdrgpexpr);

	// break into disjuncts
	CExpressionArray *pdrgpexprExtract = CPredicateUtils::PdrgpexprDisjuncts(mp, pexprDisjunction);
	GPOS_ASSERT(pdrgpexprExtract->Size() == ulDisjs);

	// collapse into single disjunct
	CExpression *pexpr = CPredicateUtils::PexprDisjunction(mp, pdrgpexprExtract);
	GPOS_ASSERT(NULL != pexpr);
	GPOS_ASSERT(CUtils::FScalarConstFalse(pexpr));
	pexpr->Release();

	// collapse empty input array to disjunct
	CExpression *pexprSingleton = CPredicateUtils::PexprDisjunction(mp, NULL /*pdrgpexpr*/);
	GPOS_ASSERT(NULL != pexprSingleton);
	pexprSingleton->Release();

	pexprDisjunction->Release();

	// disjunction on scalar comparisons
	CExpression *pexprGet = CTestUtils::PexprLogicalGet(mp);
	CColRefSet *pcrs = CDrvdPropRelational::GetRelationalProperties(pexprGet->PdpDerive())->PcrsOutput();
	CColRefSetIter crsi(*pcrs);

#ifdef GPOS_DEBUG
	BOOL fAdvance =
#endif
	crsi.Advance();
	GPOS_ASSERT(fAdvance);
	CColRef *pcr1 = crsi.Pcr();

#ifdef GPOS_DEBUG
	fAdvance =
#endif
	crsi.Advance();
	GPOS_ASSERT(fAdvance);
	CColRef *pcr2 = crsi.Pcr();

#ifdef GPOS_DEBUG
	fAdvance =
#endif
	crsi.Advance();
	GPOS_ASSERT(fAdvance);
	CColRef *pcr3 = crsi.Pcr();

	CExpression *pexprCmp1 = CUtils::PexprScalarCmp(mp, pcr1, pcr2, IMDType::EcmptEq);
	CExpression *pexprCmp2 = CUtils::PexprScalarCmp(mp, pcr1, CUtils::PexprScalarConstInt4(mp, 1 /*val*/), IMDType::EcmptEq);

	{
		CExpression *pexprDisj = CPredicateUtils::PexprDisjunction(mp, pexprCmp1, pexprCmp2);
		pdrgpexprExtract = CPredicateUtils::PdrgpexprDisjuncts(mp, pexprDisj);
		GPOS_ASSERT(2 == pdrgpexprExtract->Size());
		pdrgpexprExtract->Release();
		pexprDisj->Release();
	}


	{
		CExpressionArray *pdrgpexpr = GPOS_NEW(mp) CExpressionArray(mp);
		CExpression *pexprCmp3 = CUtils::PexprScalarCmp(mp, pcr2, pcr1, IMDType::EcmptG);
		CExpression *pexprCmp4 = CUtils::PexprScalarCmp(mp, CUtils::PexprScalarConstInt4(mp, 200 /*val*/), pcr3, IMDType::EcmptL);
		pexprCmp1->AddRef();
		pexprCmp2->AddRef();

		pdrgpexpr->Append(pexprCmp3);
		pdrgpexpr->Append(pexprCmp4);
		pdrgpexpr->Append(pexprCmp1);
		pdrgpexpr->Append(pexprCmp2);

		CExpression *pexprDisj = CPredicateUtils::PexprDisjunction(mp, pdrgpexpr);
		pdrgpexprExtract = CPredicateUtils::PdrgpexprDisjuncts(mp, pexprDisj);
		GPOS_ASSERT(4 == pdrgpexprExtract->Size());
		pdrgpexprExtract->Release();
		pexprDisj->Release();
	}

	pexprCmp1->Release();
	pexprCmp2->Release();
	pexprGet->Release();

	return GPOS_OK;
}


//---------------------------------------------------------------------------
//	@function:
//		CPredicateUtilsTest::EresUnittest_PlainEqualities
//
//	@doc:
//		Test the extraction of equality predicates between scalar identifiers
//
//---------------------------------------------------------------------------
GPOS_RESULT
CPredicateUtilsTest::EresUnittest_PlainEqualities()
{
	CAutoMemoryPool amp;
	IMemoryPool *mp = amp.Pmp();

	// setup a file-based provider
	CMDProviderMemory *pmdp = CTestUtils::m_pmdpf;
	pmdp->AddRef();
	CMDAccessor mda(mp, CMDCache::Pcache(), CTestUtils::m_sysidDefault, pmdp);

	// install opt context in TLS
	CAutoOptCtxt aoc
					(
					mp,
					&mda,
					NULL,  /* pceeval */
					CTestUtils::GetCostModel(mp)
					);

	CExpression *pexprLeft = CTestUtils::PexprLogicalGet(mp);
	CExpression *pexprRight = CTestUtils::PexprLogicalGet(mp);

	CExpressionArray *pdrgpexprOriginal = GPOS_NEW(mp) CExpressionArray(mp);

	CColRefSet *pcrsLeft = CDrvdPropRelational::GetRelationalProperties(pexprLeft->PdpDerive())->PcrsOutput();
	CColRefSet *pcrsRight = CDrvdPropRelational::GetRelationalProperties(pexprRight->PdpDerive())->PcrsOutput();

	CColRef *pcrLeft = pcrsLeft->PcrAny();
	CColRef *pcrRight = pcrsRight->PcrAny();

	// generate an equality predicate between two column reference
	CExpression *pexprScIdentEquality =
		CUtils::PexprScalarEqCmp(mp, pcrLeft, pcrRight);

	pexprScIdentEquality->AddRef();
	pdrgpexprOriginal->Append(pexprScIdentEquality);

	// generate a non-equality predicate between two column reference
	CExpression *pexprScIdentInequality =
		CUtils::PexprScalarCmp(mp, pcrLeft, pcrRight, CWStringConst(GPOS_WSZ_LIT("<")), GPOS_NEW(mp) CMDIdGPDB(GPDB_INT4_LT_OP));

	pexprScIdentInequality->AddRef();
	pdrgpexprOriginal->Append(pexprScIdentInequality);

	// generate an equality predicate between a column reference and a constant value
	CExpression *pexprScalarConstInt4 = CUtils::PexprScalarConstInt4(mp, 10 /*fValue*/);
	CExpression *pexprScIdentConstEquality = CUtils::PexprScalarEqCmp(mp, pexprScalarConstInt4, pcrRight);

	pdrgpexprOriginal->Append(pexprScIdentConstEquality);

	GPOS_ASSERT(3 == pdrgpexprOriginal->Size());

	CExpressionArray *pdrgpexprResult = CPredicateUtils::PdrgpexprPlainEqualities(mp, pdrgpexprOriginal);

	GPOS_ASSERT(1 == pdrgpexprResult->Size());

	// clean up
	pdrgpexprOriginal->Release();
	pdrgpexprResult->Release();
	pexprLeft->Release();
	pexprRight->Release();
	pexprScIdentEquality->Release();
	pexprScIdentInequality->Release();

	return GPOS_OK;
}

// EOF
