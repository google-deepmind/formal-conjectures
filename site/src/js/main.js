/**
 * main.js — shared utilities for the Formal Conjectures website.
 *
 * This file is loaded on every page.  It handles:
 *   - Active nav link highlighting
 *   - Data fetching (with a simple in-memory cache)
 *   - Small shared helpers
 */

'use strict';

// ---------------------------------------------------------------------------
// Nav: mark the current page's link as active
// ---------------------------------------------------------------------------
(function highlightNav() {
  const path = window.location.pathname.replace(/\/$/, '') || '/';
  document.querySelectorAll('.site-nav__links a').forEach(link => {
    const href = link.getAttribute('href').replace(/\/$/, '') || '/';
    if (path === href || (href !== '' && href !== '/' && path.startsWith(href))) {
      link.classList.add('active');
    }
  });
})();

// ---------------------------------------------------------------------------
// Mobile nav toggle
// ---------------------------------------------------------------------------
(function setupNavToggle() {
  const btn = document.getElementById('nav-toggle');
  const links = document.getElementById('nav-links');
  if (!btn || !links) return;
  btn.addEventListener('click', () => {
    const open = links.classList.toggle('is-open');
    btn.setAttribute('aria-expanded', open);
  });
})();

// ---------------------------------------------------------------------------
// Mobile filter toggle (browse page only)
// ---------------------------------------------------------------------------
(function setupFilterToggle() {
  const btn = document.getElementById('filter-toggle');
  const panel = document.getElementById('filter-panel');
  if (!btn || !panel) return;
  btn.addEventListener('click', () => {
    panel.classList.toggle('is-open');
    btn.textContent = panel.classList.contains('is-open') ? 'Hide filters' : 'Filters';
  });
})();

// ---------------------------------------------------------------------------
// Data loading
// ---------------------------------------------------------------------------
let _dataCache = null;
const _moduleCache = new Map();

/** Read the canonical native catalog, checking its publication descriptor. */
async function loadData() {
  if (_dataCache) return _dataCache;
  _dataCache = (async () => {
    const base = document.documentElement.dataset.base || '';
    const manifestResponse = await fetch(`${base}/data/catalog-manifest.json`);
    if (!manifestResponse.ok) throw new Error(`Catalog descriptor unavailable: ${manifestResponse.status}`);
    const descriptor = await manifestResponse.json();
    if (descriptor.schema_version !== 'fc.catalog.v1' || descriptor.catalog !== 'catalog.json' ||
        !/^[a-f0-9]{64}$/.test(descriptor.sha256)) throw new Error('Invalid catalog descriptor');
    const response = await fetch(`${base}/data/catalog.json?sha256=${descriptor.sha256}`);
    if (!response.ok) throw new Error(`Catalog unavailable: ${response.status}`);
    const bytes = await response.arrayBuffer();
    const digest = Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', bytes)), b => b.toString(16).padStart(2, '0')).join('');
    if (bytes.byteLength !== descriptor.bytes || digest !== descriptor.sha256) throw new Error('Catalog changed during download. Reload to obtain one consistent snapshot.');
    const catalog = JSON.parse(new TextDecoder('utf-8', {fatal:true}).decode(bytes));
    if (catalog.schemaVersion !== 2 || !Array.isArray(catalog.problems) ||
        catalog.problems.length !== descriptor.problem_count ||
        catalog.problems.some(entry => typeof entry.statement !== 'string' || !entry.statement.trim()) ||
        !/^[\w.-]+\/[\w.-]+$/.test(catalog.provenance?.source?.repository || '') ||
        !/^[a-f0-9]{40}$/.test(catalog.provenance?.source?.commit || '') ||
        !FCCatalog.sameJSON(catalog.provenance, descriptor.provenance)) throw new Error('Catalog provenance mismatch');
    return {conjectures:catalog.problems.map(entry => FCCatalog.processEntry(entry, catalog.provenance.source)),
      catalogProvenance:catalog.provenance, catalogDigest:descriptor.sha256,
      moduleDocstrings:catalog.moduleDocstrings};
  })();
  try { return await _dataCache; }
  catch (error) { _dataCache = null; throw error; }
}

/** Load only this module's Verso rendering and contributor presentation. */
async function loadModule(moduleName) {
  const data = await loadData();
  if (!data.conjectures.some(entry => entry.module === moduleName)) throw new Error('Unknown catalog module');
  const key = data.catalogDigest + ':' + moduleName;
  if (!_moduleCache.has(key)) _moduleCache.set(key, (async () => {
    const base = document.documentElement.dataset.base || '';
    const renderBase = document.documentElement.dataset.renderBase || base;
    const relative = FCCatalog.moduleToGitHubPath(moduleName).replace(/\.lean$/, '.json').split('/').map(encodeURIComponent).join('/');
    const response = await fetch(`${renderBase}/data/rendered/${data.catalogDigest}/${relative}`);
    if (!response.ok) throw new Error(`Module rendering unavailable: ${response.status}`);
    const value = await response.json();
    if (value.schema_version !== 'fc.website-rendering.v1' || value.module !== moduleName ||
        value.catalog_sha256 !== data.catalogDigest) throw new Error('Module rendering belongs to another catalog');
    if (!value.moduleDocs || !value.constLinks || !Array.isArray(value.contributors)) throw new Error('Incomplete module rendering');
    return value;
  })());
  try { return await _moduleCache.get(key); }
  catch (error) { _moduleCache.delete(key); throw error; }
}

// ---------------------------------------------------------------------------
// Badge / category presentation
// ---------------------------------------------------------------------------
const getCategoryMeta = FCCatalog.getCategoryMeta;

/**
 * Render a category badge element.
 * @param {string} category - raw category string from JSON
 * @returns {HTMLElement}
 */
function makeBadge(category) {
  const meta = getCategoryMeta(category);
  const span = document.createElement('span');
  span.className = `badge ${meta.css}`;
  span.textContent = meta.label;
  return span;
}

/**
 * Render a subject pill element.
 */
function makeSubjectPill(subject) {
  const span = document.createElement('span');
  span.className = 'subject-pill';
  span.textContent = subject.name || `AMS ${subject.code}`;
  return span;
}

/**
 * Escape HTML to safely insert user-controlled strings into innerHTML.
 */
function escapeHTML(str) {
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/**
 * Find the Verso constant link for a theorem.
 * extract_names uses full module-qualified names, while Verso usually stores
 * theorem links under a shorter namespace suffix.
 */
function findVersoLink(theoremName, constLinks = {}) {
  const parts = String(theoremName || '').split('.');
  for (let i = 0; i < parts.length; i++) {
    const suffix = parts.slice(i).join('.');
    if (constLinks[suffix]) return constLinks[suffix];
  }
  return null;
}

/**
 * Return the best available informal statement HTML for a conjecture.
 */
function problemDocHTML(conjecture, versoFragments = {}) {
  const versoLink = findVersoLink(conjecture?.theorem, versoFragments.constLinks || {});
  if (versoLink && versoLink.docHtml) return versoLink.docHtml;
  return conjecture?.docstring ? '<div style="white-space:pre-wrap">' + escapeHTML(conjecture.docstring) + '</div>' : '';
}

/**
 * Wire all statement dropdown buttons below a root element.
 */
function setupStatementToggles(root = document) {
  root.querySelectorAll('.statement-toggle').forEach(button => {
    if (button.dataset.statementToggleBound === 'true') return;
    const target = document.getElementById(button.getAttribute('aria-controls'));
    const label = button.querySelector('.statement-toggle__text');
    if (!target || !label) return;

    const sync = () => {
      const isOpen = !target.hidden;
      button.setAttribute('aria-expanded', String(isOpen));
      label.textContent = isOpen ? 'Hide statement' : 'Show statement';
    };

    button.addEventListener('click', () => {
      target.hidden = !target.hidden;
      sync();
    });
    button.dataset.statementToggleBound = 'true';
    sync();
  });
}

/**
 * Render LaTeX in docstring containers when KaTeX auto-render is available.
 */
function renderLatex(selector = '.verso-doc-content, .problem-doc-content') {
  let attempts = 0;
  function doRender() {
    if (typeof renderMathInElement !== 'function') {
      if (attempts < 100) {
        attempts += 1;
        setTimeout(doRender, 100);
      }
      return;
    }
    for (const el of document.querySelectorAll(selector)) {
      renderMathInElement(el, {
        delimiters: [
          { left: '$$', right: '$$', display: true },
          { left: '$', right: '$', display: false },
        ],
        throwOnError: false,
      });
    }
  }
  doRender();
}

/**
 * Build a theorem detail URL for a given theorem name.
 */
function theoremURL(theoremName) {
  const base = document.documentElement.dataset.base || '';
  return `${base}/theorem/?name=${encodeURIComponent(theoremName)}`;
}

// Human-readable labels for formal proof kinds
const FORMAL_PROOF_LABELS = {
  'formal_conjectures': 'Formal Conjectures',
  'lean4':              'Lean 4 (external)',
  'other_system':       'Other system',
};

// Expose helpers as globals for the other scripts
window.FC = {
  FORMAL_PROOF_LABELS,
  loadData,
  loadModule,
  getCategoryMeta,
  makeBadge,
  makeSubjectPill,
  escapeHTML,
  findVersoLink,
  problemDocHTML,
  setupStatementToggles,
  renderLatex,
  theoremURL,
};
