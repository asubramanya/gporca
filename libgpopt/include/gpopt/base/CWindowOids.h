//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2017 Pivotal Inc.
//
//	@filename:
//		CWindowOids.h
//
//	@doc:
//		System specific oids for window operations
//---------------------------------------------------------------------------
#ifndef GPOPT_CWindowOids_H
#define GPOPT_CWindowOids_H

#include "gpos/base.h"
#include "gpos/common/CRefCount.h"
#include "naucrates/dxl/gpdb_types.h"

#define DUMMY_ROW_NUMBER_OID OID(7000)
#define DUMMY_WIN_RANK OID(7001)
#define DUMMY_WIN_FIRST_VALUE OID(7029)
#define DUMMY_WIN_LAST_VALUE OID(7012)


namespace gpopt
{

	//---------------------------------------------------------------------------
	//	@class:
	//		CWindowOids
	//
	//	@doc:
	//		GPDB specific oids
	//
	//---------------------------------------------------------------------------
	class CWindowOids : public CRefCount
	{
		private:

			// oid of window operation "row_number" function
			OID m_oidRowNumber;

			// oid of window operation "rank" function
			OID m_oidRank;

		public:

			CWindowOids(OID oidRowNumber, OID oidRank)
			{
				m_oidRowNumber = oidRowNumber;
				m_oidRank = oidRank;
			}

			// accessor of oid value of "row_number" function
			virtual
			OID OidRowNumber() const
			{
				return m_oidRowNumber;
			}

			// accessor of oid value of "rank" function
			virtual
			OID OidRank() const
			{
				return m_oidRank;
			}

			// generate default window oids
			static
			CWindowOids *Pwindowoids(IMemoryPool *pmp)
			{
				return GPOS_NEW(pmp) CWindowOids(DUMMY_ROW_NUMBER_OID, DUMMY_WIN_RANK);
			}

	}; // class CWindowOids
}

#endif // !GPOPT_CWindowOids_H

// EOF
