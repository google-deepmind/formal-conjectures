"""Human-readable views of the same results returned to agents."""
import re


def clean(value):
    # Source text and logs may contain terminal escape/control sequences.
    text = re.sub(r'\x1b\][^\x07]*(?:\x07|\x1b\\)', '', str(value))
    text = re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]', '', text)
    return ''.join(c for c in text if c in '\n\t' or ord(c) >= 32 and not 127 <= ord(c) <= 159)


def table(headers, rows):
    rows = [[clean(c).replace('\n', ' ') for c in row] for row in rows]
    widths = [max([len(h), *[len(r[i]) for r in rows]]) for i, h in enumerate(headers)]
    return '\n'.join('  '.join(c.ljust(widths[i]) for i, c in enumerate(row)).rstrip()
                     for row in [headers, *rows])


def evidence_lines(p):
    lines=[]
    for proof in p.get('formalProofs', []):
        lines.append('Proof reference: '+proof['link'])
        if proof.get('conditions'): lines.append('Conditions: '+', '.join(proof['conditions']))
    for evidence in p.get('evidence', []):
        lines.append(f"Evidence: {evidence.get('outcome')} ({evidence.get('applicability')}) {evidence.get('url','')}")
    if not p.get('evidence'):
        state=p.get('evidence_availability','not_configured')
        labels={'not_configured':'not configured','available':'no matching records','no_records':'no published records',
                'unavailable':'retrieval unavailable','invalid':'invalid evidence; no outcome accepted'}
        lines.append('Published evidence: '+labels.get(state,state)+'.')
        if p.get('evidence_message'):lines.append(p['evidence_message'])
    if p.get('work_availability'):
        lines.append('Related work: '+p['work_availability']+((' (observed '+p['work_observed_at']+')') if p.get('work_observed_at') else ''))
        for pr in p.get('related_work',[]):lines.append(f"  #{pr['number']}: {pr['title']} (touches this module) {pr['url']}")
    return lines


def render(value, args):
    lines = []
    if 'capabilities' in value:
        lines += ['FC toolkit readiness', table(['Capability', 'Status'],
                  [[name, info['status']] for name, info in value['capabilities'].items()])]
        for name, info in value['capabilities'].items():
            for gap in info.get('gaps', []): lines.append(f'{name}: {gap}')
            if info.get('note'):lines.append(info['note'])
        lines.append('Your existing agent conducts semantic review; no AI login is required.')
    elif 'problems' in value:
        problems = value['problems']
        source=(value.get('catalog_provenance') or {}).get('source')
        origin=value.get('catalog_origin') or {}
        if source:lines.append(f"Catalog: {source['repository']} @ {source['commit'][:12]} ({origin.get('state','published')})")
        if not problems: lines.append('No matching problems. Try a collection or declaration name.')
        elif args.command == 'find':
            lines.append(table(['Declaration', 'Collection', 'Status'], [
                [p['theorem'], p.get('module','').removeprefix('FormalConjectures.'), p.get('category', 'unknown')]
                for p in problems]))
            lines.append(f"Showing {len(problems)} of {value.get('total', len(problems))} matches. Use conjectures show TARGET for details.")
        else:
            seen_modules=set()
            for p in problems:
                module=p.get('module','')
                if module not in seen_modules:
                    lines += [module.removeprefix('FormalConjectures.'), '']
                    source = value.get('moduleDocstrings', {}).get(module)
                    if source:lines += ['Sources:', source, '']
                    if p.get('source_url'):lines.append('Source revision: '+p['source_url'])
                    seen_modules.add(module)
                lines += ['', p['theorem'], 'Status: '+str(p.get('category','unknown')),
                          p.get('statement') or 'Statement text unavailable in this catalog.']
                if p.get('docstring'): lines.append(p['docstring'])
                lines += evidence_lines(p)
                lines.append('')
        lines += ['Coverage: '+g for g in value.get('coverage_gaps', [])]
    elif 'logs' in value:
        for log in value['logs']:
            lines += ['--- '+log['path']+' ---', log['text']]
        if not value['logs']: lines.append('No retained logs for this run yet.')
    elif 'runs' in value:
        records = value['runs']
        if 'outstanding' in value:lines.append(f"Runs needing attention: {value['outstanding']}; retained: {len(records)}.")
        lines.append(table(['Run', 'Target', 'Status', 'Outcome', 'Coverage gaps'],
            [[r['id'], (r.get('target') or {}).get('declaration') or
              ('PR #'+str(r['target']['pr']) if (r.get('target') or {}).get('pr') else r['kind']),
              r['status'],r.get('outcome') or 'pending',str(len(r.get('gaps',[])))] for r in records])
            if records else 'No runs in this checkout yet.')
    else:
        if value.get('status')=='awaiting_review':
            ready=value.get('build_status')=='pass' and value.get('source_coverage') in ('available','complete')
            lines += ['Prepared — semantic review pending' if ready else 'Preparation needs attention — semantic review pending', '']
        if value.get('id'): lines.append('Run: '+value['id'])
        if value.get('status'): lines.append('Status: '+value['status'])
        if value.get('outcome'): lines.append('Outcome: '+str(value['outcome']))
        for key in ('reason','message','build_status','current_applicability','report','workspace','url','public_export','configuration_path','image','detail'):
            if value.get(key) is not None: lines.append(key.replace('_',' ').capitalize()+': '+str(value[key]))
        target = value.get('target') or {}
        if target: lines.append('Target: '+' '.join(str(target[k]) for k in ('repository','pr','declaration','head','base','commit') if target.get(k)))
        for name, path in value.get('paths', {}).items(): lines.append(name.capitalize()+': '+str(path))
        if 'source_coverage' in value: lines.append('Source coverage: '+value['source_coverage'])
        if value.get('artifacts'): lines += ['Export files:']+[a['path'] for a in value['artifacts']]
        if value.get('destination'): lines.append('Destination: '+str(value['destination']))
        if value.get('omitted'): lines.append('Omitted: '+value['omitted'])
    if getattr(args,'command',None)=='eval':
        lines += ['Coverage: '+clean(gap) for gap in value.get('coverage_gaps',[])]
    summary=value.get('review_summary')
    if summary:
        lines += ['Semantic verdict: '+summary['semantic_verdict'], 'Coverage: '+str(summary['coverage'])]
        lines += ['Check: '+c['kind']+' — '+c['status'] for c in summary['checks']]
        lines += ['Finding: '+f['file']+':'+str(f['line'])+' — '+f['message'] for f in summary['findings']]
        lines += ['Question: '+q for q in summary['questions']]
        lines += ['Gap: '+str(g) for g in summary['gaps']]
        lines += ['Prior finding: '+r['status']+' — '+r['reason'] for r in summary['reconciliations']]
        lines.append('Reviewer: '+str(summary['reviewer']))
    for reviewer in (value.get('reviewer_attributions') or {}).get('reviewers',[]):
        lines.append('Attributed reviewer: '+reviewer['name']+' ('+reviewer['kind']+'); '+reviewer['independence']+' (self-reported)')
        if reviewer['shared_dependencies']:lines.append('Shared context: '+', '.join(reviewer['shared_dependencies']))
    verification=value.get('verification_summary')
    if verification:
        lines.append('Verification policy: '+str(verification['policy_outcome']))
        for key in ('stage','policy_reason','reason','detail'):
            if verification.get(key):lines.append(key.replace('_',' ').capitalize()+': '+str(verification[key]))
    observation=value.get('current_observation')
    if observation:
        lines.append('Applicability checked: '+observation['observed_at'])
        for key,expected in observation['expected'].items():
            actual=observation.get('actual',{}).get(key)
            if actual is not None and actual != expected:lines.append(f'{key}: reviewed {expected}; current {actual}')
        lines += ['Changed: '+change for change in observation['changes']]
        if observation.get('reason'):lines.append('Freshness: '+observation['reason'])
        lines.append(observation['scope'])
    if value.get('publisher'):
        publisher=value['publisher'];lines.append('Advisory publication: '+publisher['status'])
        if publisher.get('receipt',{}).get('comment_url'):lines.append('Comment: '+publisher['receipt']['comment_url'])
    if value.get('evidence_paths'):lines.append('Evidence: '+', '.join(value['evidence_paths']))
    if value.get('experimental'): lines.append('Experimental: '+str(value['experimental']))
    if getattr(args,'verbose',False):
        if value.get('catalog_origin'):lines.append('Catalog location: '+str(value['catalog_origin'].get('url') or value['catalog_origin'].get('path')))
        if value.get('created_at'):lines.append('Created: '+str(value['created_at']))
        for name,location in (value.get('tools') or {}).items():lines.append('Tool '+name+': '+str(location or 'not installed'))
    if value.get('next_action'): lines += ['', 'Next: '+value['next_action']]
    for action in value.get('next_actions', []): lines.append('Next: '+action)
    return clean('\n'.join(lines).rstrip())



def rich_table(headers, rows):
    from rich.table import Table
    from rich.text import Text
    result=Table(box=None, padding=(0,1), collapse_padding=True, expand=False,
                 header_style='bold', show_edge=False)
    for header in headers:result.add_column(header, overflow='fold')
    for row in rows:result.add_row(*(Text(clean(cell),overflow='fold') for cell in row))
    return result


def rich_view(value,args):
    """Width-aware terminal views. All external strings are literal text, never markup."""
    from rich.console import Group
    from rich.text import Text
    from rich.syntax import Syntax
    from rich.markdown import Markdown
    command=getattr(args,'command',None)
    if 'problems' in value and value['problems']:
        source=(value.get('catalog_provenance') or {}).get('source') or {}
        origin=value.get('catalog_origin') or {}
        heading='Catalog: '+source.get('repository','unknown')+' @ '+source.get('commit','unknown')[:12]
        items=[Text(heading+' ('+origin.get('state','published')+')',style='dim'),Text('')]
        if command=='find':
            items.append(rich_table(['Declaration','Collection','Status'],[
                [p['theorem'],p.get('module','').removeprefix('FormalConjectures.'),p.get('category','unknown')]
                for p in value['problems']]))
            items += [Text(''),Text(f"Showing {len(value['problems'])} of {value.get('total',len(value['problems']))} matches. Use conjectures show TARGET.")]
        else:
            modules=dict.fromkeys(p.get('module','') for p in value['problems'])
            for module in modules:
                problems=[p for p in value['problems'] if p.get('module','')==module]
                items += [Text(clean(module.removeprefix('FormalConjectures.')),style='bold cyan')]
                shared=value.get('moduleDocstrings',{}).get(module)
                if shared:items += [Text('Sources',style='bold'),Markdown(clean(shared),hyperlinks=False)]
                if problems[0].get('source_url'):items.append(Text(clean(problems[0]['source_url']),style='dim'))
                items.append(Text(''))
                for problem in problems:
                    items += [Text(clean(problem['theorem']),style='bold'),
                              Text('Status: '+clean(problem.get('category','unknown')))]
                    statement=problem.get('statement')
                    items.append(Syntax(clean(statement),'lean',background_color='default',word_wrap=True,padding=0)
                                 if statement else Text('Statement text unavailable in this catalog.',style='yellow'))
                    if problem.get('docstring'):items.append(Markdown(clean(problem['docstring']),hyperlinks=False))
                    items += [Text('\n'.join(evidence_lines(problem)),style='dim'),Text('')]
        items.extend(Text('Coverage: '+clean(gap),style='yellow') for gap in value.get('coverage_gaps',[]))
        if getattr(args,'verbose',False):items.append(Text('Catalog location: '+clean(origin.get('url') or origin.get('path') or 'unknown'),style='dim'))
        return Group(*items)
    if 'runs' in value and value['runs']:
        rows=[[r['id'],(r.get('target') or {}).get('declaration') or
               ('PR #'+str(r['target']['pr']) if (r.get('target') or {}).get('pr') else r['kind']),
               r['status'],r.get('outcome') or 'pending',str(len(r.get('gaps',[])))] for r in value['runs']]
        items=[Text(f"Runs needing attention: {value.get('outstanding',0)}; retained: {len(rows)}.",style='bold'),
               rich_table(['Run','Target','Status','Outcome','Gaps'],rows)]
        items.extend(Text('Next: '+clean(a)) for a in value.get('next_actions',[]))
        return Group(*items)
    text=Text(render(value,args),overflow='fold')
    # Style only our own line prefixes. Source strings cannot inject Rich markup.
    for prefix in ('FC toolkit readiness','Prepared — semantic review pending','Next:','Target:','Semantic verdict:','Verification policy:'):
        text.highlight_regex('(?m)^'+re.escape(prefix),style='bold cyan')
    return text
