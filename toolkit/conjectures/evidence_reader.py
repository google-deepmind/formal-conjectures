"""Validate public evidence at the read boundary. No model or proof execution."""
import re
import urllib.request
import urllib.error
from pathlib import Path
from urllib.parse import quote
from . import report as rr
from .core import github, now, user_cache, save, Failure
from .catalog_data import repository_name

MAX_FILE = 8*1024*1024
MAX_TOTAL = 64*1024*1024


def validate_index(index, read, origin=None):
    """Resolve index entries only through digest-bound artifacts at one source revision."""
    rr.require(isinstance(index,dict) and index.get('schema_version')=='fc.evidence-index.v1','Unsupported evidence index')
    rr.array(index.get('runs'),'evidence runs')
    rr.require(len(index['runs'])<=100,'Evidence index exceeds 100-run read limit')
    records=[];seen=set()
    for entry in index['runs']:
        rr.require(isinstance(entry,dict),'Invalid index entry')
        identity=entry.get('id')
        rr.require(isinstance(identity,str) and re.fullmatch(r'[0-9]{8}T[0-9]{6}Z-[a-f0-9]{12}',identity),'Invalid evidence run ID')
        rr.require(identity not in seen,'Duplicate evidence run');seen.add(identity)
        prefix='runs/'+identity
        rr.require(entry.get('path')==prefix,'Unexpected evidence bundle path')
        raw=read(prefix+'/manifest.json')
        rr.require(rr.digest(raw)==entry.get('manifest_sha256'),'Evidence manifest digest mismatch')
        manifest=rr.parse(raw)
        rr.require(manifest.get('schema_version')=='fc.evidence-bundle.v1' and manifest.get('run_id')==identity,'Invalid bundle identity')
        descriptors=manifest.get('artifacts');rr.validate_descriptors(descriptors,'bundle artifacts')
        rr.require(len(descriptors)<=100,'Too many bundle artifacts')
        files={}
        for item in descriptors:
            content=read(prefix+'/'+item['path'])
            rr.require(rr.digest(content)==item['sha256'],'Evidence artifact digest mismatch: '+item['path'])
            files[item['path']]=content
        rr.require('run.json' in files,'Bundle has no run record')
        record=rr.parse(files['run.json'])
        rr.require(record.get('schema_version')=='fc.toolkit.run.v1' and record.get('status')=='completed','Invalid completed run')
        for key in ('id','kind','outcome','target','created_at'):
            rr.require(record.get(key)==entry.get(key),'Index/run mismatch: '+key)
        rr.require(record['kind']==manifest.get('kind') and record.get('producer')==manifest.get('producer')==entry.get('producer'),'Producer or kind mismatch')
        rr.require(record['outcome'] in ('pass','fail','error','incomplete','cancelled'),'Invalid run outcome')
        target=record.get('target');rr.require(isinstance(target,dict),'Missing evidence target')
        if record['kind']=='review':
            rr.require({'report.json','request.json','review.json'}<=files.keys(),'Missing review artifacts')
            report=rr.parse(files['report.json']);request=rr.parse(files['request.json']);review=rr.parse(files['review.json'])
            rr.require(report.get('schema_version')==rr.REPORT_VERSION,'Unsupported review report')
            rr.require(report.get('request')==request and report.get('review')==review,'Review artifact binding mismatch')
            rr.require(review.get('request_id')==request.get('id'),'Review request mismatch')
            rr.require(target.get('head')==request.get('head_commit') and repository_name(target.get('repository'))==repository_name(request.get('repository')),'Review target mismatch')
            rr.require(entry.get('scope')==request.get('scope'),'Review scope mismatch')
            if request.get('base_tip'):rr.require(target.get('base')==request['base_tip'],'Review base mismatch')
            rr.require(report.get('semantic_verdict') in ('CLEAN','ACCEPT WITH NITS','NEEDS REVISION','INCOMPLETE'),'Unknown semantic verdict')
            if record['outcome']=='pass':
                rr.require(report['semantic_verdict'] in ('CLEAN','ACCEPT WITH NITS') and report['completeness']=='complete' and not report['gaps'] and all(c['status']=='pass' for c in report['checks']),'Passing run contradicts retained review')
            summary={k:report[k] for k in ('semantic_verdict','completeness','checks','gaps')}
            summary.update({k:review.get(k,[]) for k in ('findings','questions','coverage','reconciliations','reviewer')})
            if 'reviewer-attributions.json' in files:
                attribution=rr.parse(files['reviewer-attributions.json'])
                rr.require(attribution.get('request_id')==request['id'],'Attribution request mismatch')
                summary['reviewer_attributions']={'record':attribution,'evidence_availability':'retained_locally',
                                                'attribution':'self_reported'}
        elif record['kind']=='verify':
            rr.require('verification.json' in files,'Missing verification artifact')
            summary=rr.parse(files['verification.json']);request=summary.get('request') or {}
            rr.require(summary.get('schema_version')=='fc.proof-verification.v1' and request.get('run_id')==identity,'Verification run mismatch')
            rr.require(summary.get('outcome')==record['outcome'],'Verification outcome mismatch')
            if summary['outcome'] in ('pass','fail') and summary.get('comparator'):
                from .verifier_result import typed_result
                try:typed=typed_result(rr.encode(summary['comparator']),summary.get('exit_code'))
                except Failure as error:raise rr.InputError(str(error)) from error
                rr.require({'pass':'pass','rejected':'fail','error':'error'}[typed['outcome']]==summary['outcome'],'Inconsistent proof policy outcome')
            if summary['outcome']=='pass':rr.require(bool(summary.get('comparator')),'Proof pass lacks typed result')
            rr.require(request.get('source_commit')==target.get('commit') and request.get('declaration')==target.get('declaration') and repository_name(request.get('source_repository'))==repository_name(target.get('repository')),'Verification target mismatch')
        else:raise ValueError('Unsupported evidence kind')
        # URLs in an index are not trusted. Derive links from the verified archive locator.
        url=None
        if origin and origin.get('repository') and origin.get('commit'):
            url=f"https://github.com/{origin['repository']}/tree/{origin['commit']}/{prefix}"
        records.append({**entry,'url':url,'summary':summary,'validation':'validated_bundle',
                        'validation_scope':'Artifact integrity and bindings; not producer authentication or mathematical correctness.'})
    return {'schema_version':'fc.evidence-index.v1','runs':records,'status':'available' if records else 'no_records',
            'observed_at':now(),'origin':origin or {},'authority_effect':'none'}


def unavailable(status,message):
    return {'schema_version':'fc.evidence-index.v1','runs':[],'status':status,'message':message,
            'observed_at':now(),'authority_effect':'none'}


def load(root=None, destination=None, *, offline=False):
    local=Path(root)/'.conjectures/evidence-index.json' if root else None
    cache=user_cache()/('evidence-'+rr.digest(rr.encode(destination))+'.json') if destination else None
    blobs={};total=0
    def bounded(read):
        def fetch(path):
            nonlocal total
            rr.relative(path)
            if path in blobs:return blobs[path].encode()
            rr.require(len(blobs)<512,'Evidence request limit exceeded')
            raw=read(path);total+=len(raw)
            rr.require(len(raw)<=MAX_FILE and total<=MAX_TOTAL,'Evidence size limit exceeded')
            blobs[path]=raw.decode('utf-8');return raw
        return fetch
    try:
        if local and local.is_file():
            def disk(path):
                p=local.parent/path
                rr.require(not p.is_symlink() and p.resolve().is_relative_to(local.parent.resolve()),'Evidence path escapes local archive')
                with p.open('rb') as stream:return stream.read(MAX_FILE+1)
            read=bounded(disk)
            return validate_index(rr.parse(read('evidence-index.json')),read,{'path':str(local)})
        if not destination:return unavailable('not_configured','Configure a source with conjectures setup evidence.')
        repo=destination.get('repository');branch=destination.get('branch')
        rr.require(isinstance(repo,str) and re.fullmatch(r'[\w.-]+/[\w.-]+',repo) and isinstance(branch,str) and branch,'Invalid evidence destination')
        if offline:
            if not cache.is_file():return unavailable('unavailable','No retained evidence. Refresh online before using --offline.')
            envelope=rr.read_json(cache)
            rr.require(envelope['origin'].get('repository')==repo and re.fullmatch('[0-9a-f]{40}',envelope['origin'].get('commit','')),'Cached evidence origin mismatch')
            read=bounded(lambda p:envelope['files'][p].encode())
            result=validate_index(rr.parse(read('toolkit-index.json')),read,envelope['origin'])
            return {**result,'cache_state':'offline','retrieved_at':envelope['retrieved_at']}
        revision=github(f'repos/{repo}/commits/{quote(branch,safe="")}')['sha']
        rr.require(re.fullmatch('[0-9a-f]{40}',revision),'Invalid evidence commit')
        origin={'repository':repo,'commit':revision}
        def download(path):
            url=f'https://raw.githubusercontent.com/{repo}/{revision}/{quote(path,safe="/")}'
            with urllib.request.urlopen(url,timeout=10) as response:return response.read(MAX_FILE+1)
        read=bounded(download)
        result=validate_index(rr.parse(read('toolkit-index.json')),read,origin)
        save(cache,{'origin':origin,'retrieved_at':result['observed_at'],'files':blobs})
        return result
    except (OSError,Failure) as error:
        return unavailable('unavailable','Evidence could not be retrieved: '+str(error))
    except (ValueError,KeyError,TypeError,AttributeError) as error:
        return unavailable('invalid','Evidence validation failed: '+str(error))
