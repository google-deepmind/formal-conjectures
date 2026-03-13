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
  'research open':            { label: 'Open',            css: 'cat-open' },
  'research solved':          { label: 'Solved',          css: 'cat-solved' },
  'research formally solved': { label: 'Formally Solved', css: 'cat-formal' },
  'graduate':                 { label: 'Graduate',        css: 'cat-graduate' },
  'undergraduate':            { label: 'Undergraduate',   css: 'cat-undergrad' },
  'high_school':              { label: 'High School',     css: 'cat-highschool' },
  'test':                     { label: 'Test',            css: 'cat-test' },
  'API':                      { label: 'API',             css: 'cat-api' },
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
  theoremURL,
};
