/**
 * browse.js — powers the /browse/ page.
 *
 * Loads conjectures.json, renders a filterable/searchable/paginated list.
 * All state is encoded in the URL query string so that links are shareable.
 */

'use strict';

const PAGE_SIZE = 50;

// ---------------------------------------------------------------------------
// State
// ---------------------------------------------------------------------------
let allConjectures = [];
let filtered       = [];
let currentPage    = 1;

// Active filter state (driven by URL ↔ UI)
const state = {
  query:       '',
  categories:  new Set(),
  collections: new Set(),
  subjects:    new Set(),
  sort:        'name',
};

// ---------------------------------------------------------------------------
// DOM references
// ---------------------------------------------------------------------------
const searchInput       = document.getElementById('search-input');
const categoryFilters   = document.getElementById('category-filters');
const collectionFilters = document.getElementById('collection-filters');
const subjectFilters    = document.getElementById('subject-filters');
const resetBtn          = document.getElementById('reset-filters');
const resultCount       = document.getElementById('result-count');
const sortSelect        = document.getElementById('sort-select');
const listEl            = document.getElementById('theorem-list');
const paginationEl      = document.getElementById('pagination');

// ---------------------------------------------------------------------------
// URL state helpers
// ---------------------------------------------------------------------------
function readURL() {
  const params = new URLSearchParams(window.location.search);
  state.query = params.get('q') || '';
  state.categories  = new Set(params.getAll('category'));
  state.collections = new Set(params.getAll('collection'));
  state.subjects    = new Set(params.getAll('subject'));
  state.sort        = params.get('sort') || 'name';
  currentPage       = parseInt(params.get('page') || '1', 10) || 1;
}

function writeURL() {
  const params = new URLSearchParams();
  if (state.query)        params.set('q', state.query);
  for (const c of state.categories)  params.append('category',   c);
  for (const c of state.collections) params.append('collection', c);
  for (const s of state.subjects)    params.append('subject',    s);
  if (state.sort !== 'name') params.set('sort', state.sort);
  if (currentPage > 1)       params.set('page', currentPage);
  const url = params.toString() ? `?${params}` : window.location.pathname;
  window.history.replaceState(null, '', url);
}

// ---------------------------------------------------------------------------
// Filter / sort
// ---------------------------------------------------------------------------
function applyFilters() {
  const q = state.query.toLowerCase();
  filtered = allConjectures.filter(c => {
    if (q && !c.theorem.toLowerCase().includes(q) && !c.displayName.toLowerCase().includes(q)) return false;
    if (state.categories.size  && !state.categories.has(c.category))   return false;
    if (state.collections.size && !state.collections.has(c.collection)) return false;
    if (state.subjects.size) {
      const cSubjects = new Set(c.subjects.map(s => s.name));
      if (![...state.subjects].some(s => cSubjects.has(s))) return false;
    }
    return true;
  });

  // Sort
  filtered.sort((a, b) => {
    if (state.sort === 'votes' && FC.voting) {
      const aVotes = FC.voting.getVote(a.theorem).count;
      const bVotes = FC.voting.getVote(b.theorem).count;
      return bVotes - aVotes || a.theorem.localeCompare(b.theorem);
    }
    if (state.sort === 'difficulty' && FC.voting) {
      const aDiff = FC.voting.getVote(a.theorem).avgDifficulty;
      const bDiff = FC.voting.getVote(b.theorem).avgDifficulty;
      // nulls sort last
      if (aDiff === null && bDiff === null) return a.theorem.localeCompare(b.theorem);
      if (aDiff === null) return 1;
      if (bDiff === null) return -1;
      return bDiff - aDiff || a.theorem.localeCompare(b.theorem);
    }
    if (state.sort === 'category')   return a.category.localeCompare(b.category) || a.theorem.localeCompare(b.theorem);
    if (state.sort === 'collection') return a.collection.localeCompare(b.collection) || a.theorem.localeCompare(b.theorem);
    return a.theorem.localeCompare(b.theorem);
  });

  currentPage = Math.min(currentPage, Math.ceil(filtered.length / PAGE_SIZE) || 1);
}

// ---------------------------------------------------------------------------
// Render helpers
// ---------------------------------------------------------------------------
function renderCard(c) {
  const catMeta = FC.getCategoryMeta(c.category);
  const subjectPills = c.subjects.slice(0, 3)
    .map(s => `<span class="subject-pill">${FC.escapeHTML(s.name)}</span>`)
    .join('');

  const article = document.createElement('article');
  article.className = 'theorem-card';
  article.setAttribute('role', 'listitem');
  article.innerHTML = `
    <div class="theorem-card__body">
      <div class="theorem-card__name">
        <a href="${FC.escapeHTML(FC.theoremURL(c.theorem))}" title="${FC.escapeHTML(c.theorem)}">
          ${FC.escapeHTML(c.displayName)}
        </a>
      </div>
      <div class="theorem-card__meta">
        ${FC.escapeHTML(c.collection)} &mdash;
        <code style="font-size:.78rem;color:var(--color-text-muted)">${FC.escapeHTML(c.module)}</code>
      </div>
      <div class="theorem-card__tags">
        ${subjectPills}
      </div>
    </div>
    <div class="theorem-card__badge">
      ${FC.voting ? FC.voting.renderCardVoteCount(c.theorem) : ''}
      ${FC.voting ? FC.voting.renderCardDifficulty(c.theorem) : ''}
      <span class="badge ${catMeta.css}">${FC.escapeHTML(catMeta.label)}</span>
    </div>
  `;
  return article;
}

function renderList() {
  listEl.innerHTML = '';

  if (filtered.length === 0) {
    listEl.innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#x1F50D;</div>
        <div class="empty-state__text">No results match your filters.</div>
      </div>`;
    resultCount.textContent = '0 results';
    paginationEl.innerHTML = '';
    return;
  }

  const start = (currentPage - 1) * PAGE_SIZE;
  const end   = Math.min(start + PAGE_SIZE, filtered.length);
  const page  = filtered.slice(start, end);

  for (const c of page) listEl.appendChild(renderCard(c));

  resultCount.textContent = `${filtered.length.toLocaleString()} result${filtered.length !== 1 ? 's' : ''}`;

  renderPagination();
}

function renderPagination() {
  const totalPages = Math.ceil(filtered.length / PAGE_SIZE);
  paginationEl.innerHTML = '';
  if (totalPages <= 1) return;

  const addBtn = (label, page, disabled = false) => {
    const btn = document.createElement('button');
    btn.className = 'page-btn' + (page === currentPage ? ' active' : '');
    btn.textContent = label;
    btn.disabled = disabled;
    btn.addEventListener('click', () => {
      currentPage = page;
      writeURL();
      renderList();
      listEl.scrollIntoView({ behavior: 'smooth', block: 'start' });
    });
    paginationEl.appendChild(btn);
  };

  addBtn('‹', currentPage - 1, currentPage === 1);

  // Show pages around the current page
  const WINDOW = 2;
  for (let p = 1; p <= totalPages; p++) {
    if (p === 1 || p === totalPages || Math.abs(p - currentPage) <= WINDOW) {
      addBtn(p, p);
    } else if (Math.abs(p - currentPage) === WINDOW + 1) {
      const ellipsis = document.createElement('span');
      ellipsis.textContent = '…';
      ellipsis.style.padding = '0 0.25rem';
      paginationEl.appendChild(ellipsis);
    }
  }

  addBtn('›', currentPage + 1, currentPage === totalPages);
}

// ---------------------------------------------------------------------------
// Build filter checkboxes
// ---------------------------------------------------------------------------
function buildCheckboxes(container, values, stateSet, onChange) {
  container.innerHTML = '';
  [...values].sort().forEach(value => {
    const id = `chk-${container.id}-${value.replace(/\s+/g, '_')}`;
    const label = document.createElement('label');
    label.htmlFor = id;
    const chk = document.createElement('input');
    chk.type = 'checkbox';
    chk.id = id;
    chk.value = value;
    chk.checked = stateSet.has(value);
    chk.addEventListener('change', () => {
      if (chk.checked) stateSet.add(value);
      else stateSet.delete(value);
      currentPage = 1;
      onChange();
    });
    label.appendChild(chk);
    label.appendChild(document.createTextNode(' ' + value));
    container.appendChild(label);
  });
}

function syncCheckboxes() {
  document.querySelectorAll('#category-filters input').forEach(chk => {
    chk.checked = state.categories.has(chk.value);
  });
  document.querySelectorAll('#collection-filters input').forEach(chk => {
    chk.checked = state.collections.has(chk.value);
  });
  document.querySelectorAll('#subject-filters input').forEach(chk => {
    chk.checked = state.subjects.has(chk.value);
  });
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------
async function init() {
  // Load data
  let data;
  try {
    data = await FC.loadData();
  } catch (e) {
    listEl.innerHTML = `<div class="empty-state"><div class="empty-state__text">Could not load data. ${FC.escapeHTML(e.message)}</div></div>`;
    return;
  }

  allConjectures = data.conjectures;

  // Handle OAuth callback and prefetch votes (disabled)
  // await FC.voting.handleOAuthCallback();
  // await FC.voting.fetchAllVotes();

  // Collect unique values for filters
  const categories  = new Set(allConjectures.map(c => c.category));
  const collections = new Set(allConjectures.map(c => c.collection));
  const subjects    = new Set(allConjectures.flatMap(c => c.subjects.map(s => s.name)));

  const update = () => {
    applyFilters();
    writeURL();
    renderList();
  };

  // Build filter UI
  buildCheckboxes(categoryFilters,   categories,  state.categories,  update);
  buildCheckboxes(collectionFilters, collections, state.collections, update);
  buildCheckboxes(subjectFilters,    subjects,    state.subjects,    update);

  // Read initial state from URL
  readURL();
  searchInput.value  = state.query;
  sortSelect.value   = state.sort;
  syncCheckboxes();

  // Wire events
  searchInput.addEventListener('input', () => {
    state.query = searchInput.value.trim();
    currentPage = 1;
    update();
  });

  sortSelect.addEventListener('change', () => {
    state.sort = sortSelect.value;
    currentPage = 1;
    update();
  });

  resetBtn.addEventListener('click', () => {
    state.query       = '';
    state.categories.clear();
    state.collections.clear();
    state.subjects.clear();
    state.sort        = 'name';
    currentPage       = 1;
    searchInput.value = '';
    sortSelect.value  = 'name';
    syncCheckboxes();
    update();
  });

  // Initial render
  applyFilters();
  renderList();
}

init();
