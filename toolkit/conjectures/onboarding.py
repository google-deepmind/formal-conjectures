"""Capability diagnostics and explicit setup of existing execution destinations."""
from .ui import stage, log_location
import base64
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from urllib.parse import quote
from . import report as rr
from .core import Failure, command, config, config_path, github, save, run_lock, logged_command, user_cache

UPSTREAM='google-deepmind/formal-conjectures'
RESOURCES=Path(__file__).parent/'resources'


def probe(argv):
    try:command(argv,timeout=10);return True
    except (Failure,OSError,subprocess.SubprocessError):return False


def doctor(root,cfg,capability=None, catalog_url=None):
    from .review import skill_path
    import os
    tools={name:shutil.which(name) for name in ('git','gh','uv','lake','lean','docker','pdftotext')}
    github_cli=os.environ.get('CONJECTURES_GH','gh');tools['gh']=shutil.which(github_cli)
    authenticated=bool(tools['gh']) and probe([github_cli,'auth','status'])
    docker=bool(tools['docker']) and probe(['docker','info'])
    image=cfg.get('image')
    image_ready=False
    if image:
        from .execution import container_args
        try:
            container_args(image,root or Path.cwd())
            image_ready=docker and probe(['docker','image','inspect',image])
        except (ValueError,TypeError):pass
    review=[];verify=[];evidence=[]
    if not root:
        review.append('Enter an FC checkout or pass --repo PATH.')
        evidence.append('Enter the FC checkout containing the run, or pass --repo PATH.')
    if not docker:review.append('Start Docker; installation: https://docs.docker.com/get-started/get-docker/')
    if not image_ready:review.append('Run conjectures setup review to build/select the pinned review image.')
    if not authenticated:
        review.append('For PR access, run gh auth login (or select your existing CONJECTURES_GH wrapper). Local changes can still be prepared.')
        if (cfg.get('executor') or {}).get('kind')!='linux':verify.append('Run gh auth login or select your existing CONJECTURES_GH wrapper.')
        evidence.append('Run gh auth login or select your existing CONJECTURES_GH wrapper.')
    if not cfg.get('executor'):verify.append('Run conjectures setup verify --repository OWNER/REPO --ref COMMIT.')
    elif cfg['executor'].get('kind')=='linux':
        try:
            from .linux_executor import validate
            validate(cfg['executor'])
        except (Failure,OSError,subprocess.SubprocessError) as error:verify.append(str(error))
    if not cfg.get('evidence'):evidence.append('Run conjectures setup evidence --repository OWNER/REPO --branch BRANCH.')
    if not tools['lake'] or not tools['lean']:verify.append('Install the checkout’s Lean toolchain with elan before initializing a proof workspace.')
    from .catalog import load
    try:
        data=load(root,offline=capability!='browse',url=catalog_url)
        source=data['provenance']['source']
        browse={'status':'ready','gaps':[],'note':f"Catalog: {source['repository']} @ {source['commit'][:12]} ({data['catalog_origin']['state']})."}
    except Failure as error:
        browse={'status':'unavailable' if capability=='browse' else 'not checked',
                'gaps':[str(error)] if capability=='browse' else [],
                'note':'Check publication and connectivity with conjectures doctor --for browse.'}
    caps={'browse':browse,'review':{'status':'needs setup' if review else 'ready','gaps':review},
          'verify':{'status':'needs setup' if verify else 'experimental','gaps':verify},
          'evidence':{'status':'needs setup' if evidence else 'experimental','gaps':evidence}}
    selected=caps[capability] if capability else caps['browse']
    gaps=[g for c in caps.values() for g in c['gaps']]
    return {'outcome':'incomplete' if selected['gaps'] else 'pass','capabilities':caps,'tools':tools,
            'configuration':cfg,'gaps':gaps,'review_skill':str(skill_path()/'SKILL.md'),
            'lean_toolchain':(root/'lean-toolchain').read_text().strip() if root and (root/'lean-toolchain').exists() else None,
            'agent':'Use your existing agent session. No AI credentials are needed.',
            'experimental':'Proof verification and public evidence still require the release acceptance journeys.'}


def public_repo(name):
    if not re.fullmatch(r'[\w.-]+/[\w.-]+',name):raise Failure('invalid_repository','Use OWNER/REPO.')
    value=github('repos/'+name)
    if value.get('private'):raise Failure('public_repository_required','Use an explicitly public repository; private work needs a separately qualified executor.',4)
    return value


def contents(repo,path,ref):
    value=github(f'repos/{repo}/contents/{path}?ref={quote(ref,safe="")}')
    if value.get('encoding')!='base64':raise Failure('invalid_resource','Expected a GitHub file resource.',3)
    return base64.b64decode(value['content'],validate=False)


def review_image(source_ref, image=None):
    from .execution import container_args
    if not probe(['docker','info']):raise Failure('docker_unavailable','Start Docker, then retry. https://docs.docker.com/get-started/get-docker/',4)
    if image:
        container_args(image,Path.cwd())
        info=rr.parse(command(['docker','image','inspect',image]))[0]
        if info.get('Os')!='linux':raise Failure('image_platform','The review image must run Linux.',4)
        for name in ('lean-toolchain','lakefile.toml','lake-manifest.json'):
            command(['docker','run','--rm','--network=none','--read-only','--cap-drop=ALL','--security-opt=no-new-privileges','--user=65534:65534','--entrypoint=cat',image,'/opt/review-cache/'+name])
        return image,{'method':'existing_image','image':image,'qualification':'operator_selected; target compatibility checked for every build'}
    commit=github(f'repos/{UPSTREAM}/commits/{quote(source_ref,safe="")}')['sha']
    comparison=github(f'repos/{UPSTREAM}/compare/{commit}...main')
    if comparison.get('status') not in ('ahead','identical'):
        raise Failure('untrusted_source','Review setup only builds a revision already on upstream main.',4)
    toolchain=contents(UPSTREAM,'lean-toolchain',commit).decode().strip()
    match=re.fullmatch(r'leanprover/lean4:(v[0-9]+\.[0-9]+\.[0-9]+)',toolchain)
    if not match:raise Failure('unsupported_toolchain','The production recipe requires a released Lean version.',4)
    version=match[1]
    release=github('repos/leanprover/lean4/releases/tags/'+version)
    asset=next((a for a in release['assets'] if a['name']==f'lean-{version[1:]}-linux.tar.zst'),None)
    if not asset or not re.fullmatch(r'sha256:[0-9a-f]{64}',asset.get('digest') or ''):
        raise Failure('missing_tool_digest','Lean release has no verifiable archive digest; select an existing qualified image with --image.',4)
    stage('Downloading base image and building trusted Lean dependencies (this can take several minutes)…')
    import uuid
    build_log=user_cache()/'setup'/('review-'+uuid.uuid4().hex+'.log')
    logged_command(['docker','pull','--platform','linux/amd64','ubuntu:24.04'],build_log,timeout=1200)
    base=rr.parse(command(['docker','image','inspect','ubuntu:24.04']))[0]['RepoDigests'][0]
    recipe=(RESOURCES/'review.Dockerfile').read_bytes()
    with tempfile.TemporaryDirectory(prefix='fc-review-image-') as temp:
        directory=Path(temp);(directory/'Dockerfile').write_bytes(recipe)
        argv=['docker','build','--platform','linux/amd64','--iidfile',str(directory/'image.id')]
        for key,val in [('BASE_IMAGE',base),('FC_REV',commit),('LEAN_VERSION',version),('LEAN_SHA256',asset['digest'].split(':')[1])]:argv+=['--build-arg',key+'='+val]
        try:
            logged_command([*argv,str(directory)],build_log,timeout=3600)
        except subprocess.CalledProcessError as error:
            raise Failure('image_build_failed',
                'Docker image build failed. Inspect '+str(build_log)+'. Check Docker disk space and network access, then retry setup review. Existing configuration was preserved.',3) from error
        image=(directory/'image.id').read_text().strip();container_args(image,Path.cwd())
    return image,{'method':'trusted_recipe','source_repository':UPSTREAM,'source_commit':commit,'base_image':base,
                  'lean_archive_digest':asset['digest'],'recipe_sha256':rr.digest(recipe),'image':image,
                  'reproducibility':'Resulting image is digest pinned; rebuilds are not claimed byte-identical.'}


def setup(root,args):
    destination=config_path(None if args.global_config else root)
    if args.operation=='catalog':
        from .catalog import load, catalog_url
        url=catalog_url(args.url)
        data=load(root,refresh=True,url=url)
        if data['catalog_origin']['state']!='fresh':raise Failure('catalog_unavailable','Setup requires a freshly validated catalog; configuration was preserved.',4)
        update={'catalog_url':url}
        receipt={'catalog_origin':data['catalog_origin'],'provenance':data['provenance']}
    elif args.operation=='review':
        image,receipt=review_image(args.source_ref,args.image);update={'image':image}
    elif args.operation=='verify' and getattr(args,'local',False):
        if args.repository or args.ref or not args.toolkit or not args.tools:
            raise Failure('invalid_arguments','Use --local --toolkit PATH --tools PATH without --repository/--ref.')
        from .linux_executor import profile
        if args.build_tools:
            from .tool_acquisition import build
            build(args.toolkit,args.tools)
        update={'executor':profile(args.toolkit,args.tools)}
        receipt={'method':'local_linux','qualification':update['executor']['qualification']}
    else:
        if args.operation=='verify' and (not args.repository or not args.ref or getattr(args,'toolkit',None) or getattr(args,'tools',None) or getattr(args,'build_tools',False)):
            raise Failure('invalid_arguments','Use --repository OWNER/REPO --ref COMMIT, or --local --toolkit PATH --tools PATH.')
        public_repo(args.repository)
        if args.operation=='verify':
            import importlib.util
            if importlib.util.find_spec('conjectures.proof') is None:raise Failure('unavailable_command','Proof execution is not included in this revision.',4)
            if not re.fullmatch('[0-9a-f]{40}',args.ref):raise Failure('unpinned_executor','Use a full qualified commit SHA.',4)
            if github(f'repos/{args.repository}/commits/{args.ref}').get('sha')!=args.ref:raise Failure('unknown_executor','Executor commit is not retrievable.',4)
            remote=contents(args.repository,'.github/workflows/comparator-lean-4-33.yml',args.ref)
            expected=(RESOURCES/'verification-workflow.yml').read_bytes()
            if remote!=expected:raise Failure('executor_policy_mismatch','Executor workflow differs from this toolkit’s trusted policy.',4)
            from .proof import executor_ref
            executor_ref(args.repository,args.ref)
            update={'executor':{'kind':'github','repository':args.repository,'ref':args.ref}}
        else:
            command(['git','check-ref-format','refs/heads/'+args.branch])
            github(f'repos/{args.repository}/branches/{quote(args.branch,safe="")}')
            if args.branch==github(f'repos/{args.repository}')['default_branch']:
                raise Failure('not_evidence_branch','Choose an existing data-only branch, not the default code branch.',4)
            update={'evidence':{'repository':args.repository,'branch':args.branch}}
        receipt={'validated':update,'qualification':'Configuration validation does not establish completed release qualification.'}
    destination.parent.mkdir(parents=True,exist_ok=True)
    with run_lock(destination.parent):
        old=rr.read_json(destination) if destination.exists() else {}
        if not isinstance(old,dict):raise Failure('invalid_configuration','Configuration must be a JSON object.')
        save(destination,{**old,**update})
        save(destination.parent/('setup-'+args.operation+'.json'),receipt)
    return {'outcome':'pass','configuration_path':str(destination),'receipt':receipt,
            'image':receipt.get('image'),'next_action':'conjectures doctor --for '+('browse' if args.operation=='catalog' else args.operation),
            'experimental':'Proof and publication require end-to-end qualification.' if args.operation in ('verify','evidence') else None}
