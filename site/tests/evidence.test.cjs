const assert = require('node:assert/strict');
const test = require('node:test');
const evidence = require('../src/js/evidence.js');
const theorem = {theorem:'Erdos730.main',module:'FormalConjectures.ErdosProblems.«730»',githubPath:'FormalConjectures/ErdosProblems/730.lean'};
const escape = s => String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('"','&quot;');
for (const outcome of ['pass','fail','error','incomplete','cancelled']) {
  test(`renders ${outcome} without asserting acceptance`, () => {
    const html = evidence.render(theorem,{runs:[{kind:'verify',outcome,target:{declaration:theorem.theorem,module:theorem.module,commit:'abc'},producer:'github_actions'}],source_revision:'abc'},escape);
    assert.match(html,/Current revision/); assert.match(html,/maintainer acceptance/);
  });
}
test('changed targets are historical and variants do not inherit proofs', () => {
  const run = {kind:'verify',outcome:'pass',target:{declaration:theorem.theorem,module:theorem.module,commit:'old'}};
  assert.match(evidence.render(theorem,{runs:[run],source_revision:'new'},escape),/Historical revision/);
  assert.equal(evidence.records({...theorem,theorem:'Erdos730.variant'},{runs:[run]}).length,0);
});
test('missing records and missing transport have different messages', () => {
  assert.match(evidence.render(theorem,{runs:[]},escape),/No published contribution evidence/);
  assert.match(evidence.render(theorem,{status:'unavailable'},escape),/unavailable/);
});
test('untrusted links cannot execute script', () => {
  assert.equal(evidence.safeURL('javascript:alert(1)'),null);
});
