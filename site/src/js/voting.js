/**
 * voting.js — Cloudflare KV-backed voting and difficulty rating system.
 *
 * Votes and difficulty ratings (0–10) are stored in Cloudflare KV via the
 * worker. GitHub OAuth is used only for identity verification (zero
 * permissions required).
 *
 * Extends window.FC with a `voting` namespace.
 */

'use strict';

(function () {
  // ---------------------------------------------------------------------------
  // Configuration — change these for your deployment / testing
  // ---------------------------------------------------------------------------
  const WORKER_URL   = 'http://localhost:8787';
  const GH_CLIENT_ID = 'Iv23lid2mjCGp7EIKrJn';

  const GH_API = 'https://api.github.com';
  const LS_TOKEN_KEY = 'fc_gh_token';
  const LS_USER_KEY  = 'fc_gh_user';

  // ---------------------------------------------------------------------------
  // In-memory vote cache: Map<theoremName, { count, userVoted, avgDifficulty, numRatings, userDifficulty }>
  // ---------------------------------------------------------------------------
  let voteCache = null;

  // ---------------------------------------------------------------------------
  // Auth helpers
  // ---------------------------------------------------------------------------
  function isLoggedIn() {
    return !!localStorage.getItem(LS_TOKEN_KEY);
  }

  function getUser() {
    return {
      login: localStorage.getItem(LS_USER_KEY),
      token: localStorage.getItem(LS_TOKEN_KEY),
    };
  }

  function login() {
    const redirectUri = window.location.href.split('?')[0] + window.location.search;
    const params = new URLSearchParams({
      client_id: GH_CLIENT_ID,
      redirect_uri: redirectUri,
    });
    window.location.href = `https://github.com/login/oauth/authorize?${params}`;
  }

  function logout() {
    localStorage.removeItem(LS_TOKEN_KEY);
    localStorage.removeItem(LS_USER_KEY);
    voteCache = null;
    window.location.reload();
  }

  async function handleOAuthCallback() {
    const params = new URLSearchParams(window.location.search);
    const code = params.get('code');
    if (!code) return;

    // Strip the code from the URL immediately
    params.delete('code');
    params.delete('state');
    const clean = params.toString()
      ? `${window.location.pathname}?${params}`
      : window.location.pathname;
    window.history.replaceState(null, '', clean);

    try {
      // Exchange code for token via our worker
      const tokenResp = await fetch(`${WORKER_URL}/token`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ code }),
      });
      if (!tokenResp.ok) throw new Error('Token exchange failed');
      const { access_token } = await tokenResp.json();

      // Fetch GitHub user info
      const userResp = await fetch(`${GH_API}/user`, {
        headers: { Authorization: `Bearer ${access_token}` },
      });
      if (!userResp.ok) throw new Error('Failed to fetch user info');
      const user = await userResp.json();

      localStorage.setItem(LS_TOKEN_KEY, access_token);
      localStorage.setItem(LS_USER_KEY, user.login);
    } catch (e) {
      console.error('OAuth callback error:', e);
    }
  }

  // ---------------------------------------------------------------------------
  // Vote data fetching
  // ---------------------------------------------------------------------------
  async function fetchAllVotes() {
    if (voteCache) return voteCache;

    const map = new Map();
    const { login } = getUser();
    const userParam = login ? `?user=${encodeURIComponent(login)}` : '';

    try {
      const resp = await fetch(`${WORKER_URL}/votes${userParam}`);
      if (!resp.ok) throw new Error('Failed to fetch votes');
      const data = await resp.json();

      for (const [name, info] of Object.entries(data)) {
        map.set(name, {
          count: info.count,
          userVoted: info.userVoted,
          avgDifficulty: info.avgDifficulty ?? null,
          numRatings: info.numRatings || 0,
          userDifficulty: info.userDifficulty ?? null,
        });
      }
    } catch (e) {
      console.error('Failed to fetch votes:', e);
    }

    voteCache = map;
    return map;
  }

  function getVote(theoremName) {
    const defaults = { count: 0, userVoted: false, avgDifficulty: null, numRatings: 0, userDifficulty: null };
    if (!voteCache) return defaults;
    const data = voteCache.get(theoremName);
    return data ? { ...defaults, ...data } : defaults;
  }

  // ---------------------------------------------------------------------------
  // Voting actions
  // ---------------------------------------------------------------------------
  async function submitVote(theoremName) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const resp = await fetch(`${WORKER_URL}/vote/${encodeURIComponent(theoremName)}`, {
      method: 'POST',
      headers: { Authorization: `Bearer ${token}` },
    });

    if (!resp.ok) throw new Error('Failed to submit vote');
    const result = await resp.json();

    // Update cache (preserve difficulty fields)
    if (!voteCache) voteCache = new Map();
    const prev = voteCache.get(theoremName) || {};
    voteCache.set(theoremName, { ...prev, count: result.count, userVoted: true });
  }

  async function removeVote(theoremName) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const resp = await fetch(`${WORKER_URL}/vote/${encodeURIComponent(theoremName)}`, {
      method: 'DELETE',
      headers: { Authorization: `Bearer ${token}` },
    });

    if (!resp.ok) throw new Error('Failed to remove vote');
    const result = await resp.json();

    // Update cache (preserve difficulty fields)
    if (voteCache) {
      const prev = voteCache.get(theoremName) || {};
      if (result.count === 0 && !prev.numRatings) {
        voteCache.delete(theoremName);
      } else {
        voteCache.set(theoremName, { ...prev, count: result.count, userVoted: false });
      }
    }
  }

  // ---------------------------------------------------------------------------
  // Difficulty actions
  // ---------------------------------------------------------------------------
  async function submitDifficulty(theoremName, value) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const resp = await fetch(`${WORKER_URL}/difficulty/${encodeURIComponent(theoremName)}`, {
      method: 'POST',
      headers: { Authorization: `Bearer ${token}`, 'Content-Type': 'application/json' },
      body: JSON.stringify({ value }),
    });

    if (!resp.ok) throw new Error('Failed to submit difficulty');
    const result = await resp.json();

    if (!voteCache) voteCache = new Map();
    const prev = voteCache.get(theoremName) || {};
    voteCache.set(theoremName, { ...prev, avgDifficulty: result.avgDifficulty, numRatings: result.numRatings, userDifficulty: result.userDifficulty });
  }

  async function removeDifficulty(theoremName) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const resp = await fetch(`${WORKER_URL}/difficulty/${encodeURIComponent(theoremName)}`, {
      method: 'DELETE',
      headers: { Authorization: `Bearer ${token}` },
    });

    if (!resp.ok) throw new Error('Failed to remove difficulty');
    const result = await resp.json();

    if (voteCache) {
      const prev = voteCache.get(theoremName) || {};
      voteCache.set(theoremName, { ...prev, avgDifficulty: result.avgDifficulty, numRatings: result.numRatings, userDifficulty: null });
    }
  }

  // ---------------------------------------------------------------------------
  // UI helpers
  // ---------------------------------------------------------------------------
  function renderVoteButton(theoremName, container) {
    if (!container) return;

    const { count, userVoted } = getVote(theoremName);

    container.innerHTML = '';
    container.className = 'vote-widget';

    if (!isLoggedIn()) {
      container.innerHTML = `
        <button class="vote-btn" title="Sign in to vote" aria-label="Sign in to vote">
          <svg width="16" height="16" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">
            <path d="M8 2.748c-.702-.836-1.726-1.248-2.78-1.248C3.302 1.5 1.5 3.326 1.5 5.41c0 2.218 1.457 4.287 3.3 5.903C5.876 12.236 7.14 12.99 8 13.5c.86-.51 2.124-1.264 3.2-2.187C13.043 9.697 14.5 7.628 14.5 5.41c0-2.084-1.802-3.91-3.72-3.91-1.054 0-2.078.412-2.78 1.248z"/>
          </svg>
          <span class="vote-count">${count || 0}</span>
        </button>
        <a href="#" class="auth-prompt">Sign in to vote</a>
      `;
      container.querySelector('.auth-prompt').addEventListener('click', function (e) {
        e.preventDefault();
        login();
      });
      container.querySelector('.vote-btn').addEventListener('click', function () {
        login();
      });
      return;
    }

    const btn = document.createElement('button');
    btn.className = 'vote-btn' + (userVoted ? ' vote-btn--active' : '');
    btn.title = userVoted ? 'Remove vote' : 'Vote for this theorem';
    btn.setAttribute('aria-label', userVoted ? 'Remove vote' : 'Vote for this theorem');
    btn.innerHTML = `
      <svg width="16" height="16" viewBox="0 0 16 16" fill="${userVoted ? 'currentColor' : 'none'}" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round">
        <path d="M8 2.748c-.702-.836-1.726-1.248-2.78-1.248C3.302 1.5 1.5 3.326 1.5 5.41c0 2.218 1.457 4.287 3.3 5.903C5.876 12.236 7.14 12.99 8 13.5c.86-.51 2.124-1.264 3.2-2.187C13.043 9.697 14.5 7.628 14.5 5.41c0-2.084-1.802-3.91-3.72-3.91-1.054 0-2.078.412-2.78 1.248z"/>
      </svg>
      <span class="vote-count">${count}</span>
    `;

    let busy = false;
    btn.addEventListener('click', async function () {
      if (busy) return;
      busy = true;
      btn.disabled = true;

      try {
        if (userVoted) {
          await removeVote(theoremName);
        } else {
          await submitVote(theoremName);
        }
        renderVoteButton(theoremName, container);
      } catch (e) {
        console.error('Vote action failed:', e);
        showToast('Vote failed. Please try again.');
      } finally {
        busy = false;
        btn.disabled = false;
      }
    });

    container.appendChild(btn);
  }

  function renderCardVoteCount(theoremName) {
    const { count } = getVote(theoremName);
    if (count === 0) return '';
    return `<span class="theorem-card__votes" title="${count} vote${count !== 1 ? 's' : ''}">
      <svg width="12" height="12" viewBox="0 0 16 16" fill="currentColor" stroke="none">
        <path d="M8 2.748c-.702-.836-1.726-1.248-2.78-1.248C3.302 1.5 1.5 3.326 1.5 5.41c0 2.218 1.457 4.287 3.3 5.903C5.876 12.236 7.14 12.99 8 13.5c.86-.51 2.124-1.264 3.2-2.187C13.043 9.697 14.5 7.628 14.5 5.41c0-2.084-1.802-3.91-3.72-3.91-1.054 0-2.078.412-2.78 1.248z"/>
      </svg>
      ${count}</span>`;
  }

  function renderDifficultyWidget(theoremName, container) {
    if (!container) return;

    const { avgDifficulty, numRatings, userDifficulty } = getVote(theoremName);

    container.innerHTML = '';
    container.className = 'difficulty-widget';

    const avgText = avgDifficulty !== null
      ? `<span class="difficulty-display">Avg difficulty: <strong>${avgDifficulty}</strong>/10 (${numRatings} rating${numRatings !== 1 ? 's' : ''})</span>`
      : '<span class="difficulty-display">No ratings yet</span>';

    if (!isLoggedIn()) {
      container.innerHTML = `${avgText}<a href="#" class="auth-prompt">Sign in to rate</a>`;
      container.querySelector('.auth-prompt').addEventListener('click', function (e) {
        e.preventDefault();
        login();
      });
      return;
    }

    container.innerHTML = avgText;

    const select = document.createElement('select');
    select.className = 'difficulty-select';
    select.setAttribute('aria-label', 'Rate difficulty 0–10');
    const placeholder = document.createElement('option');
    placeholder.value = '';
    placeholder.textContent = 'Rate difficulty…';
    placeholder.disabled = true;
    placeholder.selected = userDifficulty === null;
    select.appendChild(placeholder);

    for (let i = 0; i <= 10; i++) {
      const opt = document.createElement('option');
      opt.value = i;
      opt.textContent = i;
      if (userDifficulty === i) opt.selected = true;
      select.appendChild(opt);
    }

    let busy = false;
    select.addEventListener('change', async function () {
      if (busy) return;
      busy = true;
      select.disabled = true;

      try {
        const val = parseInt(select.value, 10);
        await submitDifficulty(theoremName, val);
        renderDifficultyWidget(theoremName, container);
      } catch (e) {
        console.error('Difficulty rating failed:', e);
        showToast('Rating failed. Please try again.');
      } finally {
        busy = false;
        select.disabled = false;
      }
    });

    container.appendChild(select);

    if (userDifficulty !== null) {
      const removeBtn = document.createElement('button');
      removeBtn.className = 'vote-btn difficulty-clear-btn';
      removeBtn.textContent = 'Clear';
      removeBtn.title = 'Remove your difficulty rating';
      removeBtn.addEventListener('click', async function () {
        if (busy) return;
        busy = true;
        removeBtn.disabled = true;
        try {
          await removeDifficulty(theoremName);
          renderDifficultyWidget(theoremName, container);
        } catch (e) {
          console.error('Remove difficulty failed:', e);
          showToast('Failed to remove rating.');
        } finally {
          busy = false;
          removeBtn.disabled = false;
        }
      });
      container.appendChild(removeBtn);
    }
  }

  function renderCardDifficulty(theoremName) {
    const { avgDifficulty } = getVote(theoremName);
    if (avgDifficulty === null) return '';
    return `<span class="theorem-card__difficulty" title="Avg difficulty ${avgDifficulty}/10">
      <svg width="12" height="12" viewBox="0 0 16 16" fill="currentColor" stroke="none">
        <path d="M9 1L4 9h4l-1 6 5-8H8l1-6z"/>
      </svg>
      ${avgDifficulty}</span>`;
  }

  function showToast(message) {
    let toast = document.getElementById('vote-toast');
    if (!toast) {
      toast = document.createElement('div');
      toast.id = 'vote-toast';
      toast.style.cssText = 'position:fixed;bottom:1.5rem;left:50%;transform:translateX(-50%);background:#1a202c;color:white;padding:.6rem 1.2rem;border-radius:6px;font-size:.875rem;z-index:1000;opacity:0;transition:opacity .3s';
      document.body.appendChild(toast);
    }
    toast.textContent = message;
    toast.style.opacity = '1';
    setTimeout(() => { toast.style.opacity = '0'; }, 3000);
  }

  // ---------------------------------------------------------------------------
  // Expose on FC namespace
  // ---------------------------------------------------------------------------
  window.FC.voting = {
    isLoggedIn,
    getUser,
    login,
    logout,
    handleOAuthCallback,
    fetchAllVotes,
    getVote,
    submitVote,
    removeVote,
    submitDifficulty,
    removeDifficulty,
    renderVoteButton,
    renderCardVoteCount,
    renderDifficultyWidget,
    renderCardDifficulty,
  };
})();
