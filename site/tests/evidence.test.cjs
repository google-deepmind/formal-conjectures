const assert = require('node:assert/strict');
const test = require('node:test');
const evidence = require('../src/js/evidence.js');
const theorem = {theorem:'Erdos730.main',module:'FormalConjectures.ErdosProblems.«730»',githubPath:'FormalConjectures/ErdosProblems/730.lean'};
const escape = s => String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('"','&quot;');
for (const outcome of ['pass','fail','error','incomplete','cancelled']) {
  test(`renders ${outcome} without asserting acceptance`, () => {
    const html = evidence.render(theorem,{runs:[{kind:'verify',outcome,target:{declaration:theorem.theorem,module:theorem.module,commit:'abc',repository:'owner/fc'},producer:'github_actions'}],catalog_source:{repository:'owner/fc',commit:'abc'}},escape);
    assert.match(html,/Current revision/); assert.match(html,/maintainer acceptance/);
  });
}
test('changed targets are historical and variants do not inherit proofs', () => {
  const run = {kind:'verify',outcome:'pass',target:{declaration:theorem.theorem,module:theorem.module,commit:'old',repository:'owner/fc'}};
  assert.match(evidence.render(theorem,{runs:[run],catalog_source:{repository:'owner/fc',commit:'new'}},escape),/Historical revision/);
  assert.equal(evidence.records({...theorem,theorem:'Erdos730.variant'},{runs:[run]}).length,0);
});
test('missing records and missing transport have different messages', () => {
  assert.match(evidence.render(theorem,{runs:[]},escape),/No published contribution evidence/);
  assert.match(evidence.render(theorem,{status:'unavailable'},escape),/unavailable/);
});
test('untrusted links cannot execute script', () => {
  assert.equal(evidence.safeURL('javascript:alert(1)'),null);
});

test('evidence applicability uses catalog repository and revision', () => {
  const run = {kind:'verify',outcome:'pass',target:{repository:'other/fc',module:theorem.module,declaration:theorem.theorem,commit:'abc'}};
  assert.equal(evidence.records(theorem,{runs:[run],catalog_source:{repository:'owner/fc',commit:'abc'}}).length,0);
  assert.match(evidence.render(theorem,{runs:[run],source_revision:'abc'},escape),/Applicability unconfirmed/);
});

test('equivalent repository URLs and Lean quoted modules join the same target', () => {
  const run = {kind:'verify',target:{repository:'https://github.com/owner/fc.git',module:'«FormalConjectures».«ErdosProblems».«730»',declaration:theorem.theorem}};
  assert.equal(evidence.records(theorem,{runs:[run],catalog_source:{repository:'owner/fc'}}).length,1);
});
