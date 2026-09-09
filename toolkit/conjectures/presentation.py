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
        lines.append('Your existing agent conducts semantic review; no AI login is required.')
    elif 'problems' in value:
        problems = value['problems']
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
                source = value.get('moduleDocstrings', {}).get(p.get('module'))
                if source: lines += ['Sources:', source]
                for proof in p.get('formalProofs', []):
                    lines.append('Proof reference: '+proof['link'])
                    if proof.get('conditions'): lines.append('Conditions: '+', '.join(proof['conditions']))
                for evidence in p.get('evidence', []):
                    lines.append(f"Evidence: {evidence.get('outcome')} ({evidence.get('applicability')}) {evidence.get('url','')}")
                if not p.get('evidence'): lines.append('Published evidence: unavailable or not configured.')
                lines.append('')
        lines += ['Coverage: '+g for g in value.get('coverage_gaps', [])]
    elif 'logs' in value:
        for log in value['logs']:
            lines += ['--- '+log['path']+' ---', log['text']]
        if not value['logs']: lines.append('No retained logs for this run yet.')
    elif 'runs' in value:
        records = value['runs']
        lines.append(table(['Run', 'Kind', 'Status', 'Outcome'], [[r['id'], r['kind'], r['status'], r.get('outcome') or 'pending'] for r in records]) if records else 'No runs in this checkout yet.')
    else:
        if value.get('id'): lines.append('Run: '+value['id'])
        if value.get('status'): lines.append('Status: '+value['status'])
        if value.get('outcome'): lines.append('Outcome: '+str(value['outcome']))
        for key in ('reason','message','build_status','current_applicability','report','workspace','url','public_export','configuration_path'):
            if value.get(key) is not None: lines.append(key.replace('_',' ').capitalize()+': '+str(value[key]))
        target = value.get('target') or {}
        if target: lines.append('Target: '+' '.join(str(target[k]) for k in ('repository','pr','declaration','head','commit') if target.get(k)))
        for name, path in value.get('paths', {}).items(): lines.append(name.capitalize()+': '+str(path))
        if 'source_coverage' in value: lines.append('Source coverage: '+value['source_coverage'])
        if value.get('artifacts'): lines += ['Export files:']+[a['path'] for a in value['artifacts']]
        if value.get('destination'): lines.append('Destination: '+str(value['destination']))
        if value.get('omitted'): lines.append('Omitted: '+value['omitted'])
    if value.get('experimental'): lines.append('Experimental: '+str(value['experimental']))
    if value.get('next_action'): lines += ['', 'Next: '+value['next_action']]
    for action in value.get('next_actions', []): lines.append('Next: '+action)
    return clean('\n'.join(lines).rstrip())
