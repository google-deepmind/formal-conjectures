/* Contribution evidence is advisory and bound to exact revisions. */
'use strict';
const FCEvidence = (() => {
  const labels = {pass:'Passed', fail:'Rejected or needs revision', error:'Execution error',
    incomplete:'Incomplete', cancelled:'Cancelled'};
  function safeURL(value) {
    try { const url = new URL(value); return url.protocol === 'https:' ? url.href : null; }
    catch { return null; }
  }
  function records(theorem, data) {
    return (data.runs || []).filter(run => run.kind === 'verify'
      ? run.target?.declaration === theorem.theorem && run.target?.module === theorem.module
      : (run.scope || []).includes(theorem.githubPath));
  }
  function render(theorem, data, escape) {
    if (data.status === 'unavailable') return '<p>Published evidence is unavailable. Try again later or inspect local runs with <code>conjectures status</code>.</p>';
    const entries = records(theorem, data);
    const list = entries.length ? '<ul>' + entries.map(run => {
      const revision = run.kind === 'verify' ? run.target.commit : run.target.head;
      const applicability = !data.source_revision ? 'Applicability unconfirmed' : revision === data.source_revision ? 'Current revision' : 'Historical revision';
      const link = safeURL(run.url);
      const label = run.kind === 'verify' ? 'Proof verification' : 'Contribution review';
      return `<li><strong>${escape(label)}: ${escape(labels[run.outcome] || 'Unknown result')}</strong>.
        ${escape(applicability)} <code>${escape((revision || '').slice(0, 12))}</code>.
        ${run.producer === 'github_actions' ? 'Hosted Linux result.' : 'Local operator report.'}
        ${link ? `<a href="${escape(link)}" target="_blank" rel="noopener">Inspect evidence</a>` : 'Evidence link unavailable.'}</li>`;
    }).join('') + '</ul>' : '<p>No published contribution evidence is linked to this statement yet.</p>';
    const prs = (data.pull_requests || []).filter(pr => (pr.files || []).includes(theorem.githubPath));
    const queue = prs.length ? '<p>Related open work:</p><ul>' + prs.map(pr => {
      const link = safeURL(pr.url);
      return link ? `<li><a href="${escape(link)}" target="_blank" rel="noopener">#${escape(String(pr.number))}: ${escape(pr.title)}</a></li>` : '';
    }).join('') + '</ul>' : '<p>No related open PRs in this published queue snapshot.</p>';
    const command = `conjectures show '${theorem.theorem.replaceAll("'", "'\\''")}'`;
    return list + '<p>These results do not change the problem’s mathematical status or indicate maintainer acceptance. A proof result does not transfer to a changed statement.</p>' + queue +
      `<p>Continue locally:</p><pre><code>${escape(command)}\nconjectures status</code></pre>`;
  }
  return {render, records, safeURL};
})();
if (typeof module !== 'undefined') module.exports = FCEvidence;
