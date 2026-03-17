/**
 * voting.js — GitHub Discussions-backed voting, truth prediction, and difficulty rating system.
 *
 * Likes = HEART reactions, truth predictions = THUMBS_UP/THUMBS_DOWN reactions,
 * difficulty = any line matching /^difficulty [0-9]$/i in any comment (latest per user wins).
 * Writes go directly to GitHub GraphQL using the user's token.
 * Anonymous reads go through the App Engine proxy.
 *
 * Extends window.FC with a `voting` namespace.
 */

'use strict';

(function () {
  // ---------------------------------------------------------------------------
  // Configuration
  // ---------------------------------------------------------------------------
  const WORKER_URL   = 'REPLACE_WITH_PROXY_URL';   // e.g. 'http://localhost:8080' or 'https://PROJECT.REGION.r.appspot.com'
  const GH_CLIENT_ID = 'REPLACE_WITH_CLIENT_ID';   // GitHub App client ID
  const REPO_OWNER   = 'REPLACE_WITH_REPO_OWNER';  // e.g. 'google-deepmind'
  const REPO_NAME    = 'REPLACE_WITH_REPO_NAME';    // e.g. 'formal-conjectures'
  const REPO_ID      = 'REPLACE_WITH_REPO_ID';      // GraphQL node ID (gh api repos/OWNER/NAME --jq .node_id)

  const GH_GRAPHQL   = 'https://api.github.com/graphql';
  const GH_API       = 'https://api.github.com';

  const LS_TOKEN_KEY = 'fc_gh_token';
  const LS_USER_KEY  = 'fc_gh_user';
  const LS_CONSENT_KEY = 'fc_gh_consent_acknowledged';

  // ---------------------------------------------------------------------------
  // Caches
  // ---------------------------------------------------------------------------
  // Map<theoremName, { count, userVoted, thumbsUp, thumbsDown, userTruth, avgDifficulty, numRatings, userDifficulty, discussionId, discussionNumber }>
  let voteCache = null;
  // Map<theoremName, discussionId>
  const discussionIdCache = new Map();
  // Cached category ID for creating discussions
  let categoryIdCache = null;

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

  function hasConsented() {
    return localStorage.getItem(LS_CONSENT_KEY) === 'true';
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

  // ---------------------------------------------------------------------------
  // Consent modal
  // ---------------------------------------------------------------------------
  function showConsentModal() {
    return new Promise(function (resolve) {
      if (hasConsented()) {
        resolve(true);
        return;
      }

      const overlay = document.createElement('div');
      overlay.className = 'consent-overlay';

      const dialog = document.createElement('div');
      dialog.className = 'consent-dialog';
      dialog.setAttribute('role', 'dialog');
      dialog.setAttribute('aria-modal', 'true');
      dialog.setAttribute('aria-labelledby', 'consent-title');

      dialog.innerHTML = `
        <h2 id="consent-title" class="consent-dialog__title">Sign in with GitHub</h2>
        <div class="consent-dialog__body">
          <p>To vote, predict, or rate difficulty you need to sign in with GitHub.
          This uses GitHub OAuth with <strong>zero permissions</strong> &mdash; we only
          verify your identity.</p>
          <p><strong>All activity is public.</strong> Your votes, truth predictions,
          difficulty ratings, and any comments are stored as
          <a href="https://github.com/${FC.escapeHTML(REPO_OWNER)}/${FC.escapeHTML(REPO_NAME)}/discussions"
             target="_blank" rel="noopener">GitHub Discussions</a>
          on the Formal Conjectures repository. Anyone can see them, just like
          any other GitHub discussion or reaction.</p>
          <p>Specifically:</p>
          <ul>
            <li>Likes are stored as heart reactions</li>
            <li>Truth predictions are stored as thumbs-up/down reactions</li>
            <li>Difficulty ratings are stored as discussion comments</li>
          </ul>
        </div>
        <div class="consent-dialog__actions">
          <button class="btn btn-primary" id="consent-accept">Sign in with GitHub</button>
          <button class="btn btn-outline" id="consent-cancel">Cancel</button>
        </div>
      `;

      overlay.appendChild(dialog);
      document.body.appendChild(overlay);

      // Focus the accept button
      const acceptBtn = dialog.querySelector('#consent-accept');
      const cancelBtn = dialog.querySelector('#consent-cancel');
      acceptBtn.focus();

      function close(accepted) {
        document.removeEventListener('keydown', onKey);
        overlay.remove();
        if (accepted) {
          localStorage.setItem(LS_CONSENT_KEY, 'true');
        }
        resolve(accepted);
      }

      acceptBtn.addEventListener('click', function () { close(true); });
      cancelBtn.addEventListener('click', function () { close(false); });
      overlay.addEventListener('click', function (e) {
        if (e.target === overlay) close(false);
      });

      function onKey(e) {
        if (e.key === 'Escape') close(false);
      }
      document.addEventListener('keydown', onKey);
    });
  }

  /**
   * Show consent modal (if needed), then redirect to GitHub OAuth.
   * Returns false if the user cancelled the consent dialog.
   */
  async function loginWithConsent() {
    const accepted = await showConsentModal();
    if (!accepted) return false;
    login();
    return true; // page will redirect
  }

  async function handleOAuthCallback() {
    const params = new URLSearchParams(window.location.search);
    const code = params.get('code');
    if (!code) return;

    params.delete('code');
    params.delete('state');
    const clean = params.toString()
      ? `${window.location.pathname}?${params}`
      : window.location.pathname;
    window.history.replaceState(null, '', clean);

    try {
      const tokenResp = await fetch(`${WORKER_URL}/token`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ code }),
      });
      if (!tokenResp.ok) throw new Error('Token exchange failed');
      const { access_token } = await tokenResp.json();

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
  // GraphQL helper
  // ---------------------------------------------------------------------------
  async function graphql(query, variables, token) {
    const resp = await fetch(GH_GRAPHQL, {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${token}`,
        'Content-Type': 'application/json',
        'User-Agent': 'fc-voting-client',
      },
      body: JSON.stringify({ query, variables }),
    });
    if (!resp.ok) throw new Error(`GraphQL request failed: ${resp.status}`);
    const json = await resp.json();
    if (json.errors) throw new Error(json.errors[0].message);
    return json.data;
  }

  // ---------------------------------------------------------------------------
  // Discussion helpers
  // ---------------------------------------------------------------------------
  async function fetchCategoryId(token) {
    if (categoryIdCache) return categoryIdCache;
    const data = await graphql(`
      query($owner: String!, $name: String!) {
        repository(owner: $owner, name: $name) {
          discussionCategories(first: 1) {
            nodes { id }
          }
        }
      }
    `, { owner: REPO_OWNER, name: REPO_NAME }, token);
    const cats = data.repository.discussionCategories.nodes;
    if (cats.length === 0) throw new Error('No discussion categories found');
    categoryIdCache = cats[0].id;
    return categoryIdCache;
  }

  function updateCacheDiscussionNumber(theoremName, number) {
    if (!voteCache) voteCache = new Map();
    if (voteCache.has(theoremName)) {
      voteCache.get(theoremName).discussionNumber = number;
    } else {
      voteCache.set(theoremName, { ...getDefaults(), discussionNumber: number });
    }
  }

  async function ensureDiscussion(theoremName) {
    if (discussionIdCache.has(theoremName)) {
      return discussionIdCache.get(theoremName);
    }

    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    // Search for existing discussion
    const searchQuery = `repo:${REPO_OWNER}/${REPO_NAME} in:title "${theoremName}"`;
    const searchData = await graphql(`
      query($q: String!) {
        search(query: $q, type: DISCUSSION, first: 10) {
          nodes {
            ... on Discussion { id number title }
          }
        }
      }
    `, { q: searchQuery }, token);

    const match = searchData.search.nodes.find(n => n.title === theoremName);
    if (match) {
      discussionIdCache.set(theoremName, match.id);
      updateCacheDiscussionNumber(theoremName, match.number);
      return match.id;
    }

    // Create new discussion
    const categoryId = await fetchCategoryId(token);
    const shortName = theoremName.split('.').pop();
    const body = `Discussion for theorem **${shortName}**.\n\nFull Lean name: \`${theoremName}\``;

    const createData = await graphql(`
      mutation($repoId: ID!, $categoryId: ID!, $title: String!, $body: String!) {
        createDiscussion(input: { repositoryId: $repoId, categoryId: $categoryId, title: $title, body: $body }) {
          discussion { id number }
        }
      }
    `, { repoId: REPO_ID, categoryId, title: theoremName, body }, token);

    const created = createData.createDiscussion.discussion;
    discussionIdCache.set(theoremName, created.id);
    updateCacheDiscussionNumber(theoremName, created.number);
    return created.id;
  }

  // ---------------------------------------------------------------------------
  // Data fetching
  // ---------------------------------------------------------------------------
  function getDefaults() {
    return { count: 0, userVoted: false, thumbsUp: 0, thumbsDown: 0, userTruth: null, avgDifficulty: null, numRatings: 0, userDifficulty: null, discussionId: null, discussionNumber: null };
  }

  async function fetchAllVotes() {
    if (voteCache) return voteCache;

    const map = new Map();

    // Always fetch aggregates from the proxy (uses read-only PAT, cached)
    try {
      const resp = await fetch(`${WORKER_URL}/discussions?owner=${encodeURIComponent(REPO_OWNER)}&repo=${encodeURIComponent(REPO_NAME)}`);
      if (!resp.ok) throw new Error('Failed to fetch discussions');
      const data = await resp.json();

      for (const [name, info] of Object.entries(data)) {
        discussionIdCache.set(name, info.discussionId);
        map.set(name, {
          count: info.count,
          userVoted: false,
          thumbsUp: info.thumbsUp,
          thumbsDown: info.thumbsDown,
          userTruth: null,
          avgDifficulty: info.avgDifficulty ?? null,
          numRatings: info.numRatings || 0,
          userDifficulty: null,
          discussionId: info.discussionId,
          discussionNumber: info.discussionNumber,
        });
      }
    } catch (e) {
      console.error('Failed to fetch votes:', e);
    }

    // If logged in, overlay user-specific state
    const { token, login } = getUser();
    if (token && login) {
      try {
        let hasNextPage = true;
        let afterCursor = null;

        while (hasNextPage) {
          const data = await graphql(`
            query($owner: String!, $name: String!, $after: String) {
              repository(owner: $owner, name: $name) {
                discussions(first: 100, after: $after) {
                  pageInfo { hasNextPage endCursor }
                  nodes {
                    id
                    title
                    reactions(content: HEART) { viewerHasReacted }
                    thumbsUpReactions: reactions(content: THUMBS_UP) { viewerHasReacted }
                    thumbsDownReactions: reactions(content: THUMBS_DOWN) { viewerHasReacted }
                    comments(first: 100) {
                      pageInfo { hasNextPage endCursor }
                      nodes {
                        id
                        body
                        author { login }
                      }
                    }
                  }
                }
              }
            }
          `, { owner: REPO_OWNER, name: REPO_NAME, after: afterCursor }, token);

          const discussions = data.repository.discussions;

          for (const disc of discussions.nodes) {
            const existing = map.get(disc.title);
            if (!existing) continue;

            let allComments = [...disc.comments.nodes];
            let commentPage = disc.comments.pageInfo;
            while (commentPage.hasNextPage) {
              const cData = await graphql(`
                query($discId: ID!, $after: String) {
                  node(id: $discId) {
                    ... on Discussion {
                      comments(first: 100, after: $after) {
                        pageInfo { hasNextPage endCursor }
                        nodes {
                          id
                          body
                          author { login }
                        }
                      }
                    }
                  }
                }
              `, { discId: disc.id, after: commentPage.endCursor }, token);
              const more = cData.node.comments;
              allComments = allComments.concat(more.nodes);
              commentPage = more.pageInfo;
            }

            let userDifficulty = null;
            for (const comment of allComments) {
              if (!comment.author || comment.author.login !== login) continue;
              const lines = comment.body.split('\n');
              for (const line of lines) {
                const trimmed = line.trim();
                if (/^difficulty [0-9]$/i.test(trimmed)) {
                  userDifficulty = parseInt(trimmed.split(' ')[1], 10);
                }
              }
            }

            let userTruth = null;
            if (disc.thumbsUpReactions.viewerHasReacted) userTruth = 'up';
            else if (disc.thumbsDownReactions.viewerHasReacted) userTruth = 'down';

            existing.userVoted = disc.reactions.viewerHasReacted;
            existing.userTruth = userTruth;
            existing.userDifficulty = userDifficulty;
          }

          hasNextPage = discussions.pageInfo.hasNextPage;
          afterCursor = discussions.pageInfo.endCursor;
        }
      } catch (e) {
        if (e.message && e.message.includes('401')) {
          localStorage.removeItem(LS_TOKEN_KEY);
          localStorage.removeItem(LS_USER_KEY);
        } else {
          console.error('Failed to fetch user-specific vote state:', e);
        }
      }
    }

    voteCache = map;
    return map;
  }

  function getVote(theoremName) {
    const defaults = getDefaults();
    if (!voteCache) return defaults;
    const data = voteCache.get(theoremName);
    return data ? { ...defaults, ...data } : defaults;
  }

  // ---------------------------------------------------------------------------
  // Voting (HEART reaction)
  // ---------------------------------------------------------------------------
  async function submitVote(theoremName) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const discussionId = await ensureDiscussion(theoremName);
    await graphql(`
      mutation($subjectId: ID!) {
        addReaction(input: { subjectId: $subjectId, content: HEART }) {
          reaction { content }
        }
      }
    `, { subjectId: discussionId }, token);

    if (!voteCache) voteCache = new Map();
    const prev = voteCache.get(theoremName) || getDefaults();
    voteCache.set(theoremName, { ...prev, count: prev.count + 1, userVoted: true, discussionId });
  }

  async function removeVote(theoremName) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const prev = voteCache ? voteCache.get(theoremName) : null;
    const discussionId = prev?.discussionId || await ensureDiscussion(theoremName);

    await graphql(`
      mutation($subjectId: ID!) {
        removeReaction(input: { subjectId: $subjectId, content: HEART }) {
          reaction { content }
        }
      }
    `, { subjectId: discussionId }, token);

    if (voteCache && prev) {
      voteCache.set(theoremName, { ...prev, count: Math.max(0, prev.count - 1), userVoted: false });
    }
  }

  // ---------------------------------------------------------------------------
  // Truth prediction (THUMBS_UP / THUMBS_DOWN reactions)
  // ---------------------------------------------------------------------------
  async function submitTruth(theoremName, value) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const discussionId = await ensureDiscussion(theoremName);
    if (!voteCache) voteCache = new Map();
    const prev = voteCache.get(theoremName) || getDefaults();
    const content = value === 'up' ? 'THUMBS_UP' : 'THUMBS_DOWN';
    const opposite = value === 'up' ? 'THUMBS_DOWN' : 'THUMBS_UP';

    const oppositeValue = value === 'up' ? 'down' : 'up';
    if (prev.userTruth === oppositeValue) {
      try {
        await graphql(`
          mutation($subjectId: ID!, $content: ReactionContent!) {
            removeReaction(input: { subjectId: $subjectId, content: $content }) {
              reaction { content }
            }
          }
        `, { subjectId: discussionId, content: opposite }, token);
      } catch (e) {
        // May fail if reaction doesn't exist; that's ok
      }
    }

    await graphql(`
      mutation($subjectId: ID!, $content: ReactionContent!) {
        addReaction(input: { subjectId: $subjectId, content: $content }) {
          reaction { content }
        }
      }
    `, { subjectId: discussionId, content }, token);

    const upDelta = value === 'up' ? 1 : (prev.userTruth === 'up' ? -1 : 0);
    const downDelta = value === 'down' ? 1 : (prev.userTruth === 'down' ? -1 : 0);
    voteCache.set(theoremName, {
      ...prev,
      thumbsUp: Math.max(0, prev.thumbsUp + upDelta),
      thumbsDown: Math.max(0, prev.thumbsDown + downDelta),
      userTruth: value,
      discussionId,
    });
  }

  async function removeTruth(theoremName) {
    const { token } = getUser();
    if (!token) throw new Error('Not authenticated');

    const prev = voteCache ? voteCache.get(theoremName) : null;
    const discussionId = prev?.discussionId || await ensureDiscussion(theoremName);

    if (prev && prev.userTruth) {
      const content = prev.userTruth === 'up' ? 'THUMBS_UP' : 'THUMBS_DOWN';
      await graphql(`
        mutation($subjectId: ID!, $content: ReactionContent!) {
          removeReaction(input: { subjectId: $subjectId, content: $content }) {
            reaction { content }
          }
        }
      `, { subjectId: discussionId, content }, token);
    }

    if (voteCache && prev) {
      const upDelta = prev.userTruth === 'up' ? -1 : 0;
      const downDelta = prev.userTruth === 'down' ? -1 : 0;
      voteCache.set(theoremName, {
        ...prev,
        thumbsUp: Math.max(0, prev.thumbsUp + upDelta),
        thumbsDown: Math.max(0, prev.thumbsDown + downDelta),
        userTruth: null,
      });
    }
  }

  // ---------------------------------------------------------------------------
  // Difficulty (comments)
  // ---------------------------------------------------------------------------
  async function submitDifficulty(theoremName, value) {
    const { token, login } = getUser();
    if (!token) throw new Error('Not authenticated');
    if (!Number.isInteger(value) || value < 0 || value > 9) {
      throw new Error('Difficulty must be an integer 0-9');
    }

    const discussionId = await ensureDiscussion(theoremName);

    await deleteUserDifficultyComments(discussionId, login, token);

    await graphql(`
      mutation($discussionId: ID!, $body: String!) {
        addDiscussionComment(input: { discussionId: $discussionId, body: $body }) {
          comment { id }
        }
      }
    `, { discussionId, body: `difficulty ${value}` }, token);

    if (!voteCache) voteCache = new Map();
    const prev = voteCache.get(theoremName) || getDefaults();
    let totalRatings = prev.numRatings;
    let sum = (prev.avgDifficulty !== null ? prev.avgDifficulty * prev.numRatings : 0);
    if (prev.userDifficulty !== null) {
      sum -= prev.userDifficulty;
      totalRatings -= 1;
    }
    sum += value;
    totalRatings += 1;
    const avgDifficulty = Math.round((sum / totalRatings) * 10) / 10;
    voteCache.set(theoremName, { ...prev, avgDifficulty, numRatings: totalRatings, userDifficulty: value, discussionId });
  }

  async function removeDifficulty(theoremName) {
    const { token, login } = getUser();
    if (!token) throw new Error('Not authenticated');

    const prev = voteCache ? voteCache.get(theoremName) : null;
    const discussionId = prev?.discussionId || await ensureDiscussion(theoremName);

    await deleteUserDifficultyComments(discussionId, login, token);

    if (voteCache && prev) {
      let totalRatings = prev.numRatings;
      let sum = (prev.avgDifficulty !== null ? prev.avgDifficulty * prev.numRatings : 0);
      if (prev.userDifficulty !== null) {
        sum -= prev.userDifficulty;
        totalRatings -= 1;
      }
      const avgDifficulty = totalRatings > 0 ? Math.round((sum / totalRatings) * 10) / 10 : null;
      voteCache.set(theoremName, { ...prev, avgDifficulty, numRatings: totalRatings, userDifficulty: null });
    }
  }

  async function deleteUserDifficultyComments(discussionId, login, token) {
    let hasNextPage = true;
    let afterCursor = null;

    while (hasNextPage) {
      const data = await graphql(`
        query($discId: ID!, $after: String) {
          node(id: $discId) {
            ... on Discussion {
              comments(first: 100, after: $after) {
                pageInfo { hasNextPage endCursor }
                nodes {
                  id
                  body
                  author { login }
                }
              }
            }
          }
        }
      `, { discId: discussionId, after: afterCursor }, token);

      const comments = data.node.comments;
      for (const comment of comments.nodes) {
        if (!comment.author || comment.author.login !== login) continue;
        const body = comment.body.trim();
        if (/^difficulty [0-9]$/i.test(body)) {
          await graphql(`
            mutation($id: ID!) {
              deleteDiscussionComment(input: { id: $id }) {
                comment { id }
              }
            }
          `, { id: comment.id }, token);
        }
      }

      hasNextPage = comments.pageInfo.hasNextPage;
      afterCursor = comments.pageInfo.endCursor;
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
        loginWithConsent();
      });
      container.querySelector('.vote-btn').addEventListener('click', function () {
        loginWithConsent();
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

  // ---------------------------------------------------------------------------
  // Discussion link — lazily creates the discussion if logged in
  // ---------------------------------------------------------------------------
  function renderDiscussionLink(theoremName, container) {
    if (!container) return;

    const { discussionNumber } = getVote(theoremName);
    container.innerHTML = '';

    if (discussionNumber) {
      const url = `https://github.com/${REPO_OWNER}/${REPO_NAME}/discussions/${discussionNumber}`;
      container.innerHTML = `<a href="${FC.escapeHTML(url)}" target="_blank" rel="noopener" class="discussion-link">View discussion on GitHub &#x2197;</a>`;
      return;
    }

    // If logged in but no discussion exists, lazily create one
    if (isLoggedIn()) {
      container.innerHTML = '<span class="discussion-link discussion-link--loading">Loading discussion...</span>';
      ensureDiscussion(theoremName).then(function () {
        const vote = getVote(theoremName);
        if (vote.discussionNumber) {
          const url = `https://github.com/${REPO_OWNER}/${REPO_NAME}/discussions/${vote.discussionNumber}`;
          container.innerHTML = `<a href="${FC.escapeHTML(url)}" target="_blank" rel="noopener" class="discussion-link">View discussion on GitHub &#x2197;</a>`;
        }
      }).catch(function (e) {
        console.error('Failed to create discussion:', e);
        container.innerHTML = '';
      });
    }
  }

  // ---------------------------------------------------------------------------
  // Truth prediction UI
  // ---------------------------------------------------------------------------
  function renderTruthWidget(theoremName, container) {
    if (!container) return;

    const { thumbsUp, thumbsDown, userTruth } = getVote(theoremName);

    container.innerHTML = '';
    container.className = 'truth-widget';

    if (!isLoggedIn()) {
      container.innerHTML = `
        <button class="truth-btn" title="Predict true" aria-label="Predict true" disabled>
          <span class="truth-btn__icon">&#x1F44D;</span>
          <span class="truth-btn__count">${thumbsUp}</span>
        </button>
        <button class="truth-btn" title="Predict false" aria-label="Predict false" disabled>
          <span class="truth-btn__icon">&#x1F44E;</span>
          <span class="truth-btn__count">${thumbsDown}</span>
        </button>
        <a href="#" class="auth-prompt">Sign in to predict</a>
      `;
      container.querySelector('.auth-prompt').addEventListener('click', function (e) {
        e.preventDefault();
        loginWithConsent();
      });
      return;
    }

    let busy = false;

    const upBtn = document.createElement('button');
    upBtn.className = 'truth-btn' + (userTruth === 'up' ? ' truth-btn--active-up' : '');
    upBtn.title = userTruth === 'up' ? 'Remove prediction' : 'Predict: conjecture is true';
    upBtn.setAttribute('aria-label', upBtn.title);
    upBtn.innerHTML = `<span class="truth-btn__icon">&#x1F44D;</span><span class="truth-btn__count">${thumbsUp}</span>`;
    upBtn.addEventListener('click', async function () {
      if (busy) return;
      busy = true;
      upBtn.disabled = true;
      try {
        if (userTruth === 'up') {
          await removeTruth(theoremName);
        } else {
          await submitTruth(theoremName, 'up');
        }
        renderTruthWidget(theoremName, container);
      } catch (e) {
        console.error('Truth prediction failed:', e);
        showToast('Prediction failed. Please try again.');
      } finally {
        busy = false;
        upBtn.disabled = false;
      }
    });

    const downBtn = document.createElement('button');
    downBtn.className = 'truth-btn' + (userTruth === 'down' ? ' truth-btn--active-down' : '');
    downBtn.title = userTruth === 'down' ? 'Remove prediction' : 'Predict: conjecture is false';
    downBtn.setAttribute('aria-label', downBtn.title);
    downBtn.innerHTML = `<span class="truth-btn__icon">&#x1F44E;</span><span class="truth-btn__count">${thumbsDown}</span>`;
    downBtn.addEventListener('click', async function () {
      if (busy) return;
      busy = true;
      downBtn.disabled = true;
      try {
        if (userTruth === 'down') {
          await removeTruth(theoremName);
        } else {
          await submitTruth(theoremName, 'down');
        }
        renderTruthWidget(theoremName, container);
      } catch (e) {
        console.error('Truth prediction failed:', e);
        showToast('Prediction failed. Please try again.');
      } finally {
        busy = false;
        downBtn.disabled = false;
      }
    });

    container.appendChild(upBtn);
    container.appendChild(downBtn);
  }

  function renderCardTruth(theoremName) {
    const { thumbsUp, thumbsDown } = getVote(theoremName);
    if (thumbsUp === 0 && thumbsDown === 0) return '';
    return `<span class="theorem-card__truth" title="Predictions: ${thumbsUp} true, ${thumbsDown} false">&#x1F44D; ${thumbsUp} &#x1F44E; ${thumbsDown}</span>`;
  }

  // ---------------------------------------------------------------------------
  // Difficulty UI
  // ---------------------------------------------------------------------------
  function renderDifficultyWidget(theoremName, container) {
    if (!container) return;

    const { avgDifficulty, numRatings, userDifficulty } = getVote(theoremName);

    container.innerHTML = '';
    container.className = 'difficulty-widget';

    const avgText = avgDifficulty !== null
      ? `<span class="difficulty-display">Avg difficulty: <strong>${avgDifficulty}</strong>/9 (${numRatings} rating${numRatings !== 1 ? 's' : ''})</span>`
      : '<span class="difficulty-display">No ratings yet</span>';

    if (!isLoggedIn()) {
      container.innerHTML = `${avgText}<a href="#" class="auth-prompt">Sign in to rate</a>`;
      container.querySelector('.auth-prompt').addEventListener('click', function (e) {
        e.preventDefault();
        loginWithConsent();
      });
      return;
    }

    container.innerHTML = avgText;

    const select = document.createElement('select');
    select.className = 'difficulty-select';
    select.setAttribute('aria-label', 'Rate difficulty 0\u20139');
    const placeholder = document.createElement('option');
    placeholder.value = '';
    placeholder.textContent = 'Rate difficulty\u2026';
    placeholder.disabled = true;
    placeholder.selected = userDifficulty === null;
    select.appendChild(placeholder);

    for (let i = 0; i <= 9; i++) {
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
    return `<span class="theorem-card__difficulty" title="Avg difficulty ${avgDifficulty}/9">
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
    loginWithConsent,
    logout,
    handleOAuthCallback,
    fetchAllVotes,
    getVote,
    submitVote,
    removeVote,
    submitTruth,
    removeTruth,
    submitDifficulty,
    removeDifficulty,
    ensureDiscussion,
    renderVoteButton,
    renderCardVoteCount,
    renderDiscussionLink,
    renderTruthWidget,
    renderCardTruth,
    renderDifficultyWidget,
    renderCardDifficulty,
  };
})();
