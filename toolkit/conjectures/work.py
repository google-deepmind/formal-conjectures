"""Read published related work. Queue timing and classification stay with the board."""
from .catalog import read_url
from .core import user_cache, save
from . import report as rr
from .projections import work_context
from .catalog_data import repository_name

URL='https://google-deepmind.github.io/formal-conjectures/data/work.json'


def load(*, offline=False, url=None):
    from urllib.parse import urljoin
    endpoint=urljoin(url,'work.json') if url else URL
    cache=user_cache()/('work.json' if endpoint==URL else 'work-'+rr.digest(endpoint.encode())+'.json')
    try:
        if offline:
            if not cache.is_file():return {'status':'unavailable','pull_requests':[],'message':'No retained work snapshot.'}
            value=rr.read_json(cache)
        else:value=rr.parse(read_url(endpoint,8*1024*1024))
        if value.get('status')=='not_configured':return value
        value=work_context(value)
        if not offline:save(cache,value)
        return {**value,'status':'available','cache_state':'offline' if offline else 'fresh'}
    except (OSError,ValueError,KeyError,TypeError) as error:
        return {'status':'unavailable','pull_requests':[],'message':'Published work context unavailable: '+str(error)}


def related(problem, value, source):
    if not source or repository_name(source.get('repository'))!=repository_name(value.get('repository')):return []
    return [pr for pr in value.get('pull_requests',[]) if problem.get('githubPath') in pr['files']]
