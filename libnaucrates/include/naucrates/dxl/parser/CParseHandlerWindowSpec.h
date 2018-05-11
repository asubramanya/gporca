//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2012 EMC Corp.
//
//	@filename:
//		CParseHandlerWindowSpec.h
//
//	@doc:
//		SAX parse handler class for parsing the window specification
//---------------------------------------------------------------------------

#ifndef GPDXL_CParseHandlerWindowSpec_H
#define GPDXL_CParseHandlerWindowSpec_H

#include "gpos/base.h"
#include "naucrates/dxl/operators/CDXLWindowSpec.h"
#include "naucrates/dxl/parser/CParseHandlerBase.h"
#include "naucrates/dxl/xml/dxltokens.h"

namespace gpdxl
{
	using namespace gpos;

	XERCES_CPP_NAMESPACE_USE

	//---------------------------------------------------------------------------
	//	@class:
	//		CParseHandlerWindowSpec
	//
	//	@doc:
	//		SAX parse handler class for parsing the window specification
	//
	//---------------------------------------------------------------------------
	class CParseHandlerWindowSpec : public CParseHandlerBase
	{
		private:

			// array of partition-by column identifiers used by the window functions
			ULongPtrArray *m_pdrgpulPartCols;

			// window specification generated by the parser
			CDXLWindowSpec *m_pdxlws;

			// name of window specification
			CMDName *m_pmdname;

			// does the window spec have a frame definition
			BOOL m_fHasWindowFrame;

			// private copy ctor
			CParseHandlerWindowSpec(const CParseHandlerWindowSpec&);

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
			CParseHandlerWindowSpec
				(
				IMemoryPool *pmp,
				CParseHandlerManager *pphm,
				CParseHandlerBase *pphRoot
				);

			// window specification generated by the parse handler
			CDXLWindowSpec *Pdxlws() const
			{
				return m_pdxlws;
			}
	};
}

#endif // !GPDXL_CParseHandlerWindowSpec_H

// EOF
