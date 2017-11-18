//---------------------------------------------------------------------------
//	Greenplum Database
//	Copyright (C) 2017 Pivotal Software, Inc.
//
//	@filename:
//		CParseHandlerDefaultOids.cpp
//
//	@doc:
//		Implementation of the SAX parse handler class for parsing default oids
//---------------------------------------------------------------------------

#include "naucrates/dxl/parser/CParseHandlerManager.h"
#include "naucrates/dxl/parser/CParseHandlerFactory.h"
#include "naucrates/dxl/parser/CParseHandlerDefaultOids.h"

#include "naucrates/dxl/operators/CDXLOperatorFactory.h"

#include "naucrates/dxl/xml/dxltokens.h"

using namespace gpdxl;
using namespace gpopt;

XERCES_CPP_NAMESPACE_USE

CParseHandlerDefaultOids::CParseHandlerDefaultOids
	(
	IMemoryPool *pmp,
	CParseHandlerManager *pphm,
	CParseHandlerBase *pphRoot
	)
	:
	CParseHandlerBase(pmp, pphm, pphRoot),
	m_pdefoids(NULL)
{
}

CParseHandlerDefaultOids::~CParseHandlerDefaultOids()
{
	CRefCount::SafeRelease(m_pdefoids);
}

void
CParseHandlerDefaultOids::StartElement
	(
	const XMLCh* const , //xmlszUri,
	const XMLCh* const xmlszLocalname,
	const XMLCh* const , //xmlszQname,
	const Attributes& attrs
	)
{
	if (0 != XMLString::compareString(CDXLTokens::XmlstrToken(EdxltokenDefaultOids), xmlszLocalname))
	{
		CWStringDynamic *pstr = CDXLUtils::PstrFromXMLCh(m_pphm->Pmm(), xmlszLocalname);
		GPOS_RAISE(gpdxl::ExmaDXL, gpdxl::ExmiDXLUnexpectedTag, pstr->Wsz());
	}

	// parse default oids
	OID oidRowNumber = CDXLOperatorFactory::OidValueFromAttrs(m_pphm->Pmm(), attrs, EdxltokenOidRowNumber, EdxltokenDefaultOids);

	m_pdefoids = GPOS_NEW(m_pmp) CDefaultOids(oidRowNumber);
}

// invoked by Xerces to process a closing tag
void
CParseHandlerDefaultOids::EndElement
	(
	const XMLCh* const, // xmlszUri,
	const XMLCh* const xmlszLocalname,
	const XMLCh* const // xmlszQname
	)
{
	if (0 != XMLString::compareString(CDXLTokens::XmlstrToken(EdxltokenDefaultOids), xmlszLocalname))
	{
		CWStringDynamic *pstr = CDXLUtils::PstrFromXMLCh(m_pphm->Pmm(), xmlszLocalname);
		GPOS_RAISE( gpdxl::ExmaDXL, gpdxl::ExmiDXLUnexpectedTag, pstr->Wsz());
	}

	GPOS_ASSERT(NULL != m_pdefoids);
	GPOS_ASSERT(0 == this->UlLength());

	// deactivate handler
	m_pphm->DeactivateHandler();
}

// return the type of the parse handler.
EDxlParseHandlerType
CParseHandlerDefaultOids::Edxlphtype() const
{
	return EdxlphDefaultOids;
}

CDefaultOids *
CParseHandlerDefaultOids::Pdefoids() const
{
	return m_pdefoids;
}

// EOF
