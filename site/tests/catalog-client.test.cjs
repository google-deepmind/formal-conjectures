const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const crypto = require('node:crypto');
const catalog = require('../src/js/catalog.js');

function fixture() { return structuredClone(require('./fixtures/catalog.json')); }
function client({corrupt=false, wrongModule=false, mutate=()=>{}}={}) {
  const data = fixture(); mutate(data);
  const raw = Buffer.from(JSON.stringify(data));
  const digest = crypto.createHash('sha256').update(raw).digest('hex');
  const descriptor = {schema_version:'fc.catalog.v1',catalog:'conjectures.json',sha256:digest,
    bytes:raw.length,problem_count:1,provenance:data.provenance};
  const urls = [];
  const context = {window:{location:{pathname:'/browse/'}},
    document:{documentElement:{dataset:{base:'/fc',renderBase:'https://example.org/fc'}},
      querySelectorAll:()=>[],getElementById:()=>null},
    FCCatalog:catalog, TextDecoder,crypto:crypto.webcrypto,
    fetch:async url => {
      urls.push(url);
      if (url.endsWith('catalog-manifest.json')) return {ok:true,json:async()=>descriptor};
      if (url.includes('conjectures.json?')) return {ok:true,arrayBuffer:async()=>{
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
  await assert.rejects(client({corrupt:true}).fc.loadData(),/publication descriptor/);
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

test('browse cards and sibling links navigate by exact quoted names',()=>{
  const {fc}=client();
  fc.setupStatementToggles=()=>{};fc.renderLatex=()=>{};
  const source=fixture().provenance.source;
  const rows=['«A.B».C','A.«B.C»'].map(theorem=>catalog.processEntry({...fixture().problems[0],theorem},source));
  function page(script) {
    const elements=new Map();
    const element=id=>{
      if(!elements.has(id)) elements.set(id,{innerHTML:'',setAttribute:()=>{}});
      return elements.get(id);
    };
    const context={FC:fc,FCCatalog:catalog,document:{documentElement:{dataset:{base:'/fc'}},
      getElementById:element,createElement:()=>({setAttribute:()=>{}})},window:{},URLSearchParams};
    // Render the real page functions without its asynchronous bootstrap.
    vm.runInNewContext(fs.readFileSync(require.resolve('../src/js/'+script),'utf8').replace(/\ninit\(\);\s*$/,''),context);
    return {context,element};
  }
  const browse=page('browse.js');
  for(const row of rows) {
    const html=browse.context.renderCard(row,0).innerHTML;
    const href=html.match(/<a href="([^"]+)"/)[1];
    assert.equal(new URL(href,'https://example.org').searchParams.get('name'),row.theorem);
  }
  const theorem=page('theorem.js');
  theorem.context.renderDetail(rows[0],rows,{moduleDocs:{},constLinks:{}},[]);
  const href=theorem.element('theorem-detail').innerHTML.match(/class="sibling-item__name" href="([^"]+)"/)[1];
  assert.equal(new URL(href,'https://example.org').searchParams.get('name'),rows[1].theorem);
});

test('browser rejects malformed native fields before assembling cards', async()=>{
  for (const change of require('./fixtures/catalog-invalid.json')) {
    const mutate = data => {
      const parent = change.path.slice(0,-1).reduce((v,k)=>v[k],data);
      const key = change.path.at(-1);
      if (change.remove) delete parent[key]; else parent[key] = change.value;
    };
    await assert.rejects(client({mutate}).fc.loadData(), /Invalid or missing catalog/, JSON.stringify(change));
  }
});
