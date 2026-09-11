"""Real Linux qualification of standalone initialization and local verification.

Run on a dedicated credential-free verifier account after tools are built.
No model is invoked. All positive and negative results are retained.
"""
import argparse
import json
import os
import time
from pathlib import Path
from types import SimpleNamespace
from conjectures import core, proof, linux_executor, remote


def main():
    p=argparse.ArgumentParser()
    for name in ('toolkit','tools','out'):p.add_argument('--'+name,type=Path,required=True)
    args=p.parse_args();root=args.toolkit.resolve();out=args.out.resolve();out.mkdir(parents=True,exist_ok=True)
    revision=core.git(root,'rev-parse','HEAD').decode().strip()
    executor=linux_executor.profile(root,args.tools)
    catalog=out/'catalog.json'
    core.save(catalog,{'schemaVersion':2,'provenance':{'source':{'repository':'williamjblair/formal-conjectures','commit':revision}},
        'problems':[{'theorem':'PackageExportFixture.plain','module':'FormalConjecturesTest.PackageExport',
                     'statement':'Qualification fixture; exact signature is checked by the native exporter.'}]})
    initialization=proof.initialize(None,SimpleNamespace(target='PackageExportFixture.plain',catalog=catalog,
        repository=None,source_ref=None,out=out/'proof'),{})
    candidate=Path(initialization['workspace']);submission=candidate/'Submission.lean';original=submission.read_text()
    results=[]
    for label,body,expected in [('unfinished',original,'fail'),
                                ('imported_assumption',original.replace('sorry','exact PackageExportFixture.plain'),'fail'),
                                ('valid',original.replace('sorry','decide'),'pass')]:
        started=time.monotonic()
        print('Starting qualification case: '+label,flush=True)
        submission.write_text(body)
        value=proof.verify(candidate,candidate,{'executor':executor})
        comparator=value.get('result',{}).get('comparator') or {}
        results.append({'case':label,'expected':expected,'actual':value['outcome'],'run_id':value['id'],
                        'seconds':round(time.monotonic()-started,1),'policy_reason':comparator.get('reason'),
                        'policy_stage':comparator.get('stage')})
        core.save(out/'qualification.json',{'client_commit':revision,'executor':executor,'cases':results})
        print(json.dumps(results[-1]),flush=True)
        assert value['outcome']==expected,value
        if label in ('unfinished','imported_assumption'):
            assert comparator.get('reason')=='disallowed_axiom' and comparator.get('stage')=='axiom_policy',value
    broken={**executor,'ref':'0'*40}
    value=proof.verify(candidate,candidate,{'executor':broken})
    assert value['outcome']=='error' and value['policy_outcome']=='not_evaluated',value
    results.append({'case':'changed_executor','expected':'error','actual':value['outcome'],'run_id':value['id']})
    # Target edits are rejected before any candidate execution.
    provenance=candidate/'fc-provenance.json';original_provenance=provenance.read_bytes()
    modified=json.loads(original_provenance);modified['source']['declaration']='Different.target'
    core.save(provenance,modified)
    try:
        proof.verify(candidate,candidate,{'executor':executor})
    except core.Failure as error:
        assert (error.code,error.reason)==(1,'changed_target'),error
        results.append({'case':'changed_target','expected':'fail','actual':'fail','reason':error.reason})
    else:raise AssertionError('Changed target accepted')
    finally:provenance.write_bytes(original_provenance)
    # Real failed processes without a result must not turn diagnostic text into a verdict.
    for label,program in [('verifier_crash','import os,signal; os.kill(os.getpid(),signal.SIGKILL)'),
                          ('missing_result','print("disallowed_axiom is diagnostic text only")')]:
        logs=out/label;logs.mkdir()
        try:remote.invoke_comparator(['python3','-c',program],out,logs)
        except core.Failure as error:
            assert (error.code,error.reason)==(3,'missing_verifier_result'),error
            results.append({'case':label,'expected':'error','actual':'error','reason':error.reason,
                            'policy_outcome':'not_evaluated'})
        else:raise AssertionError('Missing verifier result accepted')
    # Exercise the actual submission traversal before invoking the verifier.
    submission.unlink();submission.symlink_to('/etc/passwd')
    value=proof.verify(candidate,candidate,{'executor':executor})
    assert value['outcome']=='fail' and value['reason']=='disallowed_submission',value
    results.append({'case':'submission_symlink','expected':'fail','actual':value['outcome'],'run_id':value['id']})
    submission.unlink();submission.write_text(original.replace('sorry','decide'))
    core.save(out/'qualification.json',{'client_commit':revision,'executor':executor,'cases':results})
    # Separate process so this probe does not change the caller's systemd transport.
    core.command(['python3','-c','from conjectures.unix_restriction import restrict; restrict(); print("AF_UNIX filter passed")'])
    print(json.dumps(results,indent=2))


if __name__=='__main__':main()
