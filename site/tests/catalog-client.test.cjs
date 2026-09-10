const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const crypto = require('node:crypto');
const catalog = require('../src/js/catalog.js');

function fixture() {
  return {schemaVersion:2,problems:[{theorem:'Example.test',module:'FormalConjectures.Example',
    category:'research solved',subjects:['11'],statement:'True',docstring:'A statement.',
    formalProofs:[{kind:'lean4',link:'https://example.org/proof',conditions:['Example.assumption']}],
    answerKinds:['proposition'],hasSorryFreeProof:false}],moduleDocstrings:{'FormalConjectures.Example':'Source'},
    provenance:{source:{repository:'owner/fc',commit:'a'.repeat(40)}}};
}
function client({corrupt=false, wrongModule=false}={}) {
  const data = fixture();
  const raw = Buffer.from(JSON.stringify(data));
  const digest = crypto.createHash('sha256').update(raw).digest('hex');
  const descriptor = {schema_version:'fc.catalog.v1',catalog:'catalog.json',sha256:digest,
    bytes:raw.length,problem_count:1,provenance:data.provenance};
  const urls = [];
  const context = {window:{location:{pathname:'/browse/'}},
    document:{documentElement:{dataset:{base:'/fc',renderBase:'https://example.org/fc'}},
      querySelectorAll:()=>[],getElementById:()=>null},
    FCCatalog:catalog, TextDecoder,crypto:crypto.webcrypto,
    fetch:async url => {
      urls.push(url);
      if (url.endsWith('catalog-manifest.json')) return {ok:true,json:async()=>descriptor};
      if (url.includes('catalog.json?')) return {ok:true,arrayBuffer:async()=>{
        const value = corrupt ? Buffer.concat([raw,Buffer.from(' ')]) : raw;
        return value.buffer.slice(value.byteOffset,value.byteOffset+value.byteLength);
      }};
      return {ok:true,json:async()=>({schema_version:'fc.website-rendering.v1',
        catalog_sha256:digest,module:wrongModule?'FormalConjectures.Other':'FormalConjectures.Example',
        moduleDocs:{},constLinks:{},contributors:[]})};
    }};
  vm.runInNewContext(fs.readFileSync(require.resolve('../src/js/main.js'),'utf8'),context);
  return {fc:context.window.FC,urls,digest};
}

test('browse coalesces catalog reads without fetching rendering; show loads only its module', async()=>{
  const {fc,urls,digest}=client();
  const [a,b]=await Promise.all([fc.loadData(),fc.loadData()]);
  assert.equal(a,b);
  assert.equal(urls.length,2);
  assert.equal(a.conjectures[0].statement,'True');
  assert.deepEqual(JSON.parse(JSON.stringify(a.conjectures[0].formalProofs)),fixture().problems[0].formalProofs);
  await Promise.all([fc.loadModule('FormalConjectures.Example'),fc.loadModule('FormalConjectures.Example')]);
  assert.equal(urls.length,3);
  assert.equal(urls[2],`https://example.org/fc/data/rendered/${digest}/FormalConjectures/Example.json`);
  await assert.rejects(fc.loadModule('FormalConjectures.Other'),/Unknown catalog module/);
  assert.equal(urls.length,3);
});

test('changed catalog bytes and mismatched module rendering are rejected',async()=>{
  await assert.rejects(client({corrupt:true}).fc.loadData(),/changed during download/);
  const {fc,urls}=client({wrongModule:true});
  await assert.rejects(fc.loadModule('FormalConjectures.Example'),/another catalog/);
  await assert.rejects(fc.loadModule('FormalConjectures.Example'),/another catalog/);
  assert.equal(urls.length,4); // failed renderings do not poison the retry cache
});

test('quoted names keep exact identity and conditional proof metadata',()=>{
  const source=fixture().provenance.source;
  const one=catalog.processEntry({...fixture().problems[0],theorem:'«A.B».C',module:'FormalConjectures.Arxiv.«0911.2077»'},source);
  const two=catalog.processEntry({...fixture().problems[0],theorem:'A.«B.C»'},source);
  assert.equal(one.githubUrl,`https://github.com/owner/fc/blob/${source.commit}/FormalConjectures/Arxiv/0911.2077.lean`);
  assert.equal(catalog.resolveTheorem([one,two],'«A.B».C'),one);
  assert.throws(()=>catalog.resolveTheorem([one,two],'A.B.C'),/Ambiguous/);
  const exact={...two,theorem:'A.B.C'};
  assert.equal(catalog.resolveTheorem([one,exact],'A.B.C'),exact);
  assert.deepEqual(one.formalProofs,fixture().problems[0].formalProofs);
});
