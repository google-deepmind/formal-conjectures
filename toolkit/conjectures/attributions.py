"""Optional self-reported reviewer context, bound to the existing request and evidence."""
from . import report as rr


def validate(value, request_id, read):
    rr.obj(value,'schema_version request_id reviewers','reviewer attribution')
    rr.require(value['schema_version']=='fc.reviewer-attribution.v1','Unsupported reviewer attribution')
    rr.require(value['request_id']==request_id,'Reviewer attribution names another request')
    rr.array(value['reviewers'],'reviewers')
    for reviewer in value['reviewers']:
        rr.obj(reviewer,'kind name method scope independence shared_dependencies evidence','reviewer')
        rr.require(reviewer['kind'] in ('human','ai'),'Invalid reviewer kind')
        for field in ('name','method'):rr.text(reviewer[field],field)
        rr.require(reviewer['independence'] in ('independent','shared_dependencies','not_assessed'),'Invalid independence claim')
        for field in ('scope','shared_dependencies'):
            rr.array(reviewer[field],field)
            for item in reviewer[field]:rr.text(item,field)
        rr.require(bool(reviewer['scope']),'Reviewer scope is empty')
        if reviewer['independence']=='shared_dependencies':
            rr.require(bool(reviewer['shared_dependencies']),'Name the shared dependencies')
        rr.validate_descriptors(reviewer['evidence'],'reviewer evidence')
        rr.require(bool(reviewer['evidence']),'Reviewer evidence is empty')
        for item in reviewer['evidence']:
            try:raw=read(item['path'])
            except (KeyError,OSError) as error:raise rr.InputError('Reviewer evidence unavailable: '+item['path']) from error
            rr.require(rr.digest(raw)==item['sha256'],'Reviewer evidence digest mismatch')
    return value
