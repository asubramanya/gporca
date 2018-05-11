//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2012 EMC Corp.
//
//	@filename:
//		CCTEMap.cpp
//
//	@doc:
//		Implementation of CTE map
//---------------------------------------------------------------------------

#include "gpos/base.h"

#include "gpopt/base/CCTEMap.h"
#include "gpopt/base/CCTEReq.h"

using namespace gpopt;

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::CCTEMap
//
//	@doc:
//		Ctor
//
//---------------------------------------------------------------------------
CCTEMap::CCTEMap
	(
	IMemoryPool *pmp
	)
	:
	m_pmp(pmp),
	m_phmcm(NULL)
{
	GPOS_ASSERT(NULL != pmp);

	m_phmcm = GPOS_NEW(m_pmp) HMCteMap(m_pmp);
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::~CCTEMap
//
//	@doc:
//		Dtor
//
//---------------------------------------------------------------------------
CCTEMap::~CCTEMap()
{
	m_phmcm->Release();
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::Insert
//
//	@doc:
//		Insert a new map entry. No entry with the same id can already exist
//
//---------------------------------------------------------------------------
void
CCTEMap::Insert
	(
	ULONG ulCteId,
	ECteType ect,
	CDrvdPropPlan *pdpplan
	)
{
	GPOS_ASSERT(EctSentinel > ect);

	if (NULL != pdpplan)
	{
		pdpplan->AddRef();
	}

	CCTEMapEntry *pcme = GPOS_NEW(m_pmp) CCTEMapEntry(ulCteId, ect, pdpplan);
#ifdef GPOS_DEBUG
	BOOL fSuccess =
#endif // GPOS_DEBUG
	m_phmcm->FInsert(GPOS_NEW(m_pmp) ULONG(ulCteId), pcme);
	GPOS_ASSERT(fSuccess);
}


//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::PdpplanProducer
//
//	@doc:
//		At any point in a query plan, derived plan properties must contain
//		at most one CTE producer;
//		this function returns plan properties of that producer if found, otherwise
//		return NULL;
//		the function also asserts that map has no other producer entries
//
//
//---------------------------------------------------------------------------
CDrvdPropPlan *
CCTEMap::PdpplanProducer
	(
	ULONG *pulId // output: CTE producer Id, set to ULONG_MAX if no producer found
	)
	const
{
	GPOS_ASSERT(NULL != pulId);

	CDrvdPropPlan *pdpplanProducer = NULL;
	*pulId = ULONG_MAX;
	HMCteMapIter hmcmi(m_phmcm);
	while (NULL == pdpplanProducer && hmcmi.FAdvance())
	{
		const CCTEMapEntry *pcme = hmcmi.Pt();
		CCTEMap::ECteType ect = pcme->Ect();
		CDrvdPropPlan *pdpplan = pcme->Pdpplan();
		if (CCTEMap::EctProducer == ect)
		{
			GPOS_ASSERT(NULL != pdpplan);
			pdpplanProducer = pdpplan;
			*pulId = pcme->UlId();
		}
	}

#ifdef GPOS_DEBUG
	while (hmcmi.FAdvance())
	{
		const CCTEMapEntry *pcme = hmcmi.Pt();
		CCTEMap::ECteType ect = pcme->Ect();
		GPOS_ASSERT(CCTEMap::EctConsumer == ect &&
					"CTE map has properties of more than one producer");
	}
#endif // GPOS_DEBUG

	return pdpplanProducer;
}


//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::AddUnresolved
//
//	@doc:
//		Helper to add entries found in the first map and are
//		unresolved based on the second map
//
//---------------------------------------------------------------------------
void
CCTEMap::AddUnresolved
	(
	const CCTEMap &cmFirst,
	const CCTEMap &cmSecond,
	CCTEMap* pcmResult
	)
{
	GPOS_ASSERT(NULL != pcmResult);
	// iterate on first map and lookup entries in second map
	HMCteMapIter hmcmi(cmFirst.m_phmcm);
	while (hmcmi.FAdvance())
	{
		const CCTEMapEntry *pcme = hmcmi.Pt();
		ULONG ulId = pcme->UlId();
		ECteType ectFirst = pcme->Ect();
		CDrvdPropPlan *pdpplanFirst = pcme->Pdpplan();

		if (NULL != pcmResult->PcmeLookup(ulId))
		{
			// skip entries already in the result map
			continue;
		}

		// check if entry exists in second map
		CCTEMapEntry *pcmeSecond = cmSecond.PcmeLookup(ulId);

		// if entry does not exist in second map, or exists with the same cte type
		// then it should be in the result
		if (NULL == pcmeSecond || ectFirst == pcmeSecond->Ect())
		{
			pcmResult->Insert(ulId, ectFirst, pdpplanFirst);
		}
	}
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::PcmeLookup
//
//	@doc:
//		Lookup info for given cte id
//
//---------------------------------------------------------------------------
CCTEMap::CCTEMapEntry *
CCTEMap::PcmeLookup
	(
	ULONG ulCteId
	)
	const
{
	return m_phmcm->PtLookup(&ulCteId);
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::FSubset
//
//	@doc:
//		Check if the current map is a subset of the given one
//
//---------------------------------------------------------------------------
BOOL
CCTEMap::FSubset
	(
	const CCTEMap *pcm
	)
	const
{
	GPOS_ASSERT(NULL != pcm);

	if (m_phmcm->UlEntries() > pcm->m_phmcm->UlEntries())
	{
		return false;
	}

	HMCteMapIter hmcmi(m_phmcm);
	while (hmcmi.FAdvance())
	{
		const CCTEMapEntry *pcme = hmcmi.Pt();
		CCTEMapEntry *pcmeOther = pcm->PcmeLookup(pcme->UlId());
		if (NULL == pcmeOther || pcmeOther->Ect() != pcme->Ect())
		{
			return false;
		}
	}

	return true;
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::UlHash
//
//	@doc:
//		Hash of components
//
//---------------------------------------------------------------------------
ULONG
CCTEMap::UlHash() const
{
	ULONG ulHash = 0;

	// how many map entries to use for hash computation
	ULONG ulMaxEntries = 5;
	ULONG ul = 0;

	HMCteMapIter hmcmi(m_phmcm);
	while (hmcmi.FAdvance() && ul < ulMaxEntries)
	{
		const CCTEMapEntry *pcme = hmcmi.Pt();
		ulHash = gpos::UlCombineHashes(ulHash, pcme->UlHash());
		ul++;
	}

	return ulHash;
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::Ect
//
//	@doc:
//		Return the CTE type associated with the given ID in the derived map
//
//---------------------------------------------------------------------------
CCTEMap::ECteType
CCTEMap::Ect
	(
	const ULONG ulId
	)
	const
{
	CCTEMapEntry *pcme = PcmeLookup(ulId);
	if (NULL == pcme)
	{
		return EctSentinel;
	}

	return pcme->Ect();
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::PcmCombine
//
//	@doc:
//		Combine the two given maps and return the result
//
//---------------------------------------------------------------------------
CCTEMap *
CCTEMap::PcmCombine
	(
	IMemoryPool *pmp,
	const CCTEMap &cmFirst,
	const CCTEMap &cmSecond
	)
{
	CCTEMap *pcmResult = GPOS_NEW(pmp) CCTEMap(pmp);

	// add entries from first map that are not resolvable based on second map
	AddUnresolved(cmFirst, cmSecond, pcmResult);

	// add entries from second map that are not resolvable based on first map
	AddUnresolved(cmSecond, cmFirst, pcmResult);

	return pcmResult;
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::FSatisfies
//
//	@doc:
//		Check whether the current CTE map satisfies the given CTE requirements
//
//---------------------------------------------------------------------------
BOOL
CCTEMap::FSatisfies
	(
	const CCTEReq *pcter
	)
	const
{
	GPOS_ASSERT(NULL != pcter);
	// every CTE marked as "Required" must be in the current map
	DrgPul *pdrgpul = pcter->PdrgpulRequired();
	const ULONG ulReqd = pdrgpul->Size();
	for (ULONG ul = 0; ul < ulReqd; ul++)
	{
		ULONG *pulId = (*pdrgpul)[ul];
		ECteType ect = pcter->Ect(*pulId);

		CCTEMapEntry *pcme = this->PcmeLookup(*pulId);
		if (NULL == pcme || pcme->Ect() != ect)
		{
			return false;
		}
	}

	// every CTE consumer in the current map must be in the requirements (does not
	// matter whether it is marked as required or optional)
	HMCteMapIter hmcmi(m_phmcm);
	while (hmcmi.FAdvance())
	{
		const CCTEMapEntry *pcme = hmcmi.Pt();
		ECteType ect = pcme->Ect();
		if (CCTEMap::EctConsumer == ect && !pcter->FContainsRequirement(pcme->UlId(), ect))
		{
			return false;
		}
	}

	return true;
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::PdrgpulAdditionalProducers
//
//	@doc:
//		Return producer ids that are in this map but not in the given requirement
//
//---------------------------------------------------------------------------
DrgPul *
CCTEMap::PdrgpulAdditionalProducers
	(
	IMemoryPool *pmp,
	const CCTEReq *pcter
	)
	const
{
	GPOS_ASSERT(NULL != pcter);
	DrgPul *pdrgpul = GPOS_NEW(pmp) DrgPul(pmp);

	HMCteMapIter hmcmi(m_phmcm);
	while (hmcmi.FAdvance())
	{
		const CCTEMapEntry *pcme = hmcmi.Pt();
		ULONG ulId = pcme->UlId();
		ECteType ect = pcme->Ect();

		if (CCTEMap::EctProducer == ect && !pcter->FContainsRequirement(ulId, ect))
		{
			pdrgpul->Append(GPOS_NEW(pmp) ULONG(ulId));
		}
	}

	return pdrgpul;
}

//---------------------------------------------------------------------------
//	@function:
//		CCTEMap::OsPrint
//
//	@doc:
//		debug print
//
//---------------------------------------------------------------------------
IOstream &
CCTEMap::OsPrint
	(
	IOstream &os
	)
	const
{
	HMCteMapIter hmcmi(m_phmcm);
	while (hmcmi.FAdvance())
	{
		CCTEMapEntry *pcme = const_cast<CCTEMapEntry *>(hmcmi.Pt());
		pcme->OsPrint(os);
		os << " ";
	}

	return os;
}

namespace gpopt {

  IOstream &operator << (IOstream &os, CCTEMap &cm)
  {
    return cm.OsPrint(os);
  }

}

// EOF
