"""Shared interpretation of Comparator structured results; never parse log text."""
from . import report as rr
from .core import Failure

def typed_result(raw,code):
    value=rr.parse(raw)
    if value.get('schemaVersion')!=1 or value.get('outcome') not in ('pass','rejected','error'):
        raise Failure('invalid_verifier_result','Comparator did not produce a recognized typed result',3)
    if value['outcome']=='pass' and (code!=0 or value.get('stage')!='complete' or value.get('reason')!='verified'):
        raise Failure('inconsistent_verifier_result','Comparator success is inconsistent with process completion',3)
    return value

