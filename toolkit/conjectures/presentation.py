"""Human-readable views of the same results returned to agents."""
import re


def clean(value):
    # Source text and logs may contain terminal escape/control sequences.
    text = re.sub(r'\x1b\][^\x07]*(?:\x07|\x1b\\)', '', str(value))
    text = re.sub(r'\x1b\[[0-?]*[ -/]*[@-~]', '', text)
    return ''.join(c for c in text if c in '\n\t' or ord(c) >= 32 and ord(c) != 127)


def table(headers, rows):
    rows = [[clean(c).replace('\n', ' ')[:120] for c in row] for row in rows]
    widths = [max([len(h), *[len(r[i]) for r in rows]]) for i, h in enumerate(headers)]
    return '\n'.join('  '.join(c.ljust(widths[i]) for i, c in enumerate(row)).rstrip()
                     for row in [headers, *rows])


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
            for p in problems:
                lines += [p['theorem'], p.get('module', ''), 'Status: '+str(p.get('category','unknown')),
                          p.get('statement') or 'Statement text unavailable in this catalog.']
                if p.get('docstring'): lines.append(p['docstring'])
                if p.get('source_url'):lines.append('Source revision: '+p['source_url'])
                source = value.get('moduleDocstrings', {}).get(p.get('module'))
                if source: lines += ['Sources:', source]
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
        if value.get('id'): lines.append('Run: '+value['id'])
        if value.get('status'): lines.append('Status: '+value['status'])
        if value.get('outcome'): lines.append('Outcome: '+str(value['outcome']))
        for key in ('reason','message','build_status','current_applicability','report','workspace','url','public_export','configuration_path','image'):
            if value.get(key) is not None: lines.append(key.replace('_',' ').capitalize()+': '+str(value[key]))
        target = value.get('target') or {}
        if target: lines.append('Target: '+' '.join(str(target[k]) for k in ('repository','pr','declaration','head','commit') if target.get(k)))
        for name, path in value.get('paths', {}).items(): lines.append(name.capitalize()+': '+str(path))
        if 'source_coverage' in value: lines.append('Source coverage: '+value['source_coverage'])
        if value.get('artifacts'): lines += ['Export files:']+[a['path'] for a in value['artifacts']]
        if value.get('destination'): lines.append('Destination: '+str(value['destination']))
        if value.get('omitted'): lines.append('Omitted: '+value['omitted'])
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
        if verification.get('semantic_assessment_required'):
            lines.append('Semantic assessment: required for submitted definitions; not established by kernel verification.')
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
    if value.get('evidence_paths'):lines.append('Evidence: '+', '.join(value['evidence_paths']))
    if value.get('experimental'): lines.append('Experimental: '+str(value['experimental']))
    if value.get('next_action'): lines += ['', 'Next: '+value['next_action']]
    for action in value.get('next_actions', []): lines.append('Next: '+action)
    return clean('\n'.join(lines).rstrip())
