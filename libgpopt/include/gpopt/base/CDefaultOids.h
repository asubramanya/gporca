//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2017 Pivotal Inc.
//
//	@filename:
//		CDefaultOids.h
//
//	@doc:
//		GPDB specific oids
//---------------------------------------------------------------------------
#ifndef GPOPT_CDefaultOids_H
#define GPOPT_CDefaultOids_H

#include "gpos/base.h"
#include "gpos/common/CRefCount.h"
#include "naucrates/dxl/gpdb_types.h"

#define DUMMY_ROW_NUMBER_OID OID(7000)

namespace gpopt
{

	//---------------------------------------------------------------------------
	//	@class:
	//		CDefaultOids
	//
	//	@doc:
	//		GPDB specific oids
	//
	//---------------------------------------------------------------------------
	class CDefaultOids : public CRefCount
	{
		private:

			// oid of window operation "row_number"
			OID m_oidRowNumber;

		public:

			CDefaultOids(OID oidRowNumber)
			{
				m_oidRowNumber = oidRowNumber;
			}

			// accessor of oid value
			virtual
			OID OidRowNumber() const
			{
				return m_oidRowNumber;
			}

			// generate default oids
			static
			CDefaultOids *PdefOids(IMemoryPool *pmp)
			{
				return GPOS_NEW(pmp) CDefaultOids(DUMMY_ROW_NUMBER_OID);
			}

	}; // class CDefaultOids
}

#endif // !GPOPT_CDefaultOids_H

// EOF
