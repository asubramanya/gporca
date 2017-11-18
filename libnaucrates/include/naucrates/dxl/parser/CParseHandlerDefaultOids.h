//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2016 Pivotal Software, Inc.
//
//	@filename:
//		CParseHandlerDefaultOids.h
//
//	@doc:
//		SAX parse handler class for parsing default oids
//---------------------------------------------------------------------------

#ifndef GPDXL_CParseHandlerDefaultOids_H
#define GPDXL_CParseHandlerDefaultOids_H

#include "gpos/base.h"
#include "naucrates/dxl/parser/CParseHandlerBase.h"
#include "gpopt/base/CDefaultOids.h"

namespace gpdxl
{
	using namespace gpos;

	XERCES_CPP_NAMESPACE_USE

	//---------------------------------------------------------------------------
	//	@class:
	//		CParseHandlerDefaultOids
	//
	//	@doc:
	//		SAX parse handler class for parsing default oids
	//
	//---------------------------------------------------------------------------
	class CParseHandlerDefaultOids : public CParseHandlerBase
	{
		private:

			// deafult oids
			CDefaultOids *m_pdefoids;

			// private copy ctor
			CParseHandlerDefaultOids(const CParseHandlerDefaultOids&);

			// process the start of an element
			void StartElement
				(
					const XMLCh* const xmlszUri, 		// URI of element's namespace
 					const XMLCh* const xmlszLocalname,	// local part of element's name
					const XMLCh* const xmlszQname,		// element's qname
					const Attributes& attr				// element's attributes
				);

			// process the end of an element
			void EndElement
				(
					const XMLCh* const xmlszUri, 		// URI of element's namespace
					const XMLCh* const xmlszLocalname,	// local part of element's name
					const XMLCh* const xmlszQname		// element's qname
				);

		public:
			// ctor
			CParseHandlerDefaultOids
				(
				IMemoryPool *pmp,
				CParseHandlerManager *pphm,
				CParseHandlerBase *pphRoot
				);

			// dtor
			virtual
			~CParseHandlerDefaultOids();

			// type of the parse handler
			virtual
			EDxlParseHandlerType Edxlphtype() const;

			// default oids
			CDefaultOids *Pdefoids() const;
	};
}

#endif // !GPDXL_CParseHandlerDefaultOids_H

// EOF
