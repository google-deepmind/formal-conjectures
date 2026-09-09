"""Read schema-2 native metadata without reinterpreting Lean declarations."""
import json

def metadata_rows(data):
    if not isinstance(data,dict) or data.get('schemaVersion')!=2:
        raise ValueError('Expected native schemaVersion 2')
    rows=data.get('problems',data.get('conjectures'))
    if not isinstance(rows,list):raise ValueError('Metadata rows must be a list')
    for index,row in enumerate(rows):
        if not isinstance(row,dict):raise ValueError(f'Row {index} must be an object')
        if any(k in row for k in ('formalProofKind','formalProofLink','proofConditions')):
            raise ValueError('Legacy proof fields are not valid in current metadata')
        proofs=row.get('formalProofs',[])
        if not isinstance(proofs,list):raise ValueError('formalProofs must be a list')
        for proof in proofs:
            if not isinstance(proof,dict):raise ValueError('Proof reference must be an object')
            if proof.get('kind') not in ('formal_conjectures','lean4','other_system'):
                raise ValueError('Unknown formal proof kind')
            if not isinstance(proof.get('link'),str):raise ValueError('Proof link must be a string')
            if not isinstance(proof.get('conditions'),list) or not all(isinstance(c,str) for c in proof['conditions']):
                raise ValueError('Proof conditions must be a list of strings')
    return rows

def unconditional_proof(row):
    return any(not proof['conditions'] for proof in row.get('formalProofs',[]))

def proof_links(data):
    return sorted({proof['link'] for row in metadata_rows(data) for proof in row.get('formalProofs',[]) if proof['link']})
