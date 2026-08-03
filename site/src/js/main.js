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

/**
 * Fetch and cache the processed conjectures dataset.
 * Returns a Promise that resolves to { conjectures, stats, amsSubjects }.
 */
async function loadData() {
  if (_dataCache) return _dataCache;
  // Resolve the data URL relative to the site root (handles both local and
  // deployed environments where the page may be at different depths).
  const base = document.documentElement.dataset.base || '';
  const resp = await fetch(`${base}/data/conjectures.json`);
  if (!resp.ok) throw new Error(`Failed to load data: ${resp.status}`);
  _dataCache = await resp.json();
  return _dataCache;
}

// ---------------------------------------------------------------------------
// Badge / category helpers (duplicated from build.js for client-side use)
// ---------------------------------------------------------------------------
const CATEGORY_META = {
  'research open':    { label: 'Open',          css: 'cat-open' },
  'research solved':  { label: 'Solved',        css: 'cat-solved' },
  'textbook':         { label: 'Textbook',      css: 'cat-textbook' },
  'test':             { label: 'Test',          css: 'cat-test' },
  'API':              { label: 'API',           css: 'cat-api' },
};

function getCategoryMeta(category) {
  return CATEGORY_META[category] || { label: category, css: 'cat-unknown' };
}

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
  return '';
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

// Expose helpers as globals for the other scripts
window.FC = {
  loadData,
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
