'use strict';

const express = require('express');
const jwt = require('jsonwebtoken');

const app = express();
app.use(express.json());

// ---------------------------------------------------------------------------
// Configuration — loaded at startup, secrets filled in by loadSecrets()
// ---------------------------------------------------------------------------
const config = {
  ALLOWED_ORIGIN:      process.env.ALLOWED_ORIGIN || '*',
  GH_APP_ID:           process.env.GH_APP_ID || '',
  GH_CLIENT_ID:        process.env.GH_CLIENT_ID || '',
  GH_CLIENT_SECRET:    process.env.GH_CLIENT_SECRET || '',
  GH_APP_PRIVATE_KEY:  process.env.GH_APP_PRIVATE_KEY || '',
};

// Secrets to load from Secret Manager when not set via env vars
const SECRET_NAMES = ['GH_CLIENT_ID', 'GH_CLIENT_SECRET', 'GH_APP_PRIVATE_KEY'];

/**
 * Load any missing secrets from Google Cloud Secret Manager.
 * Env vars take precedence (for local dev). In production on App Engine,
 * secrets come from Secret Manager.
 */
async function loadSecrets() {
  const missing = SECRET_NAMES.filter(name => !config[name]);
  if (missing.length === 0) return;

  let client;
  try {
    const { SecretManagerServiceClient } = require('@google-cloud/secret-manager');
    client = new SecretManagerServiceClient();
  } catch (e) {
    console.error('Secret Manager client unavailable and secrets not in env vars.');
    console.error('For local dev, set env vars: ' + missing.join(', '));
    process.exit(1);
  }

  const [projectId] = await client.getProjectId().then(id => [id]);

  for (const name of missing) {
    try {
      const [version] = await client.accessSecretVersion({
        name: `projects/${projectId}/secrets/${name}/versions/latest`,
      });
      config[name] = version.payload.data.toString('utf8');
      console.log(`  Loaded secret: ${name}`);
    } catch (e) {
      console.error(`Failed to load secret ${name}: ${e.message}`);
      process.exit(1);
    }
  }
}

// ---------------------------------------------------------------------------
// GitHub App installation token management
// ---------------------------------------------------------------------------

// Cache: "owner/repo" -> { token, expiresAt }
const installationTokenCache = new Map();

/**
 * Create a JWT for the GitHub App, valid for 10 minutes.
 */
function createAppJWT() {
  const now = Math.floor(Date.now() / 1000);
  return jwt.sign(
    { iat: now - 60, exp: now + 600, iss: config.GH_APP_ID },
    config.GH_APP_PRIVATE_KEY,
    { algorithm: 'RS256' },
  );
}

/**
 * Get a GitHub API installation token for the given repo.
 * Returns a cached token if still valid (with 5-minute margin).
 */
async function getInstallationToken(owner, repo) {
  const cacheKey = `${owner}/${repo}`;
  const cached = installationTokenCache.get(cacheKey);
  if (cached && cached.expiresAt > Date.now() + 5 * 60 * 1000) {
    return cached.token;
  }

  const appJWT = createAppJWT();

  // Find the installation ID for this repo
  const installResp = await fetch(`https://api.github.com/repos/${owner}/${repo}/installation`, {
    headers: {
      Authorization: `Bearer ${appJWT}`,
      Accept: 'application/vnd.github+json',
      'User-Agent': 'fc-oauth-proxy',
    },
  });
  if (!installResp.ok) {
    const text = await installResp.text();
    throw new Error(`Failed to find app installation for ${owner}/${repo}: ${installResp.status} ${text}`);
  }
  const { id: installationId } = await installResp.json();

  // Create an installation access token
  const tokenResp = await fetch(`https://api.github.com/app/installations/${installationId}/access_tokens`, {
    method: 'POST',
    headers: {
      Authorization: `Bearer ${appJWT}`,
      Accept: 'application/vnd.github+json',
      'User-Agent': 'fc-oauth-proxy',
    },
  });
  if (!tokenResp.ok) {
    const text = await tokenResp.text();
    throw new Error(`Failed to create installation token: ${tokenResp.status} ${text}`);
  }
  const { token, expires_at } = await tokenResp.json();

  installationTokenCache.set(cacheKey, {
    token,
    expiresAt: new Date(expires_at).getTime(),
  });

  return token;
}

// ---------------------------------------------------------------------------
// CORS
// ---------------------------------------------------------------------------
function getCorsHeaders(req) {
  const origin = req.headers.origin || '';
  // Allow any *.github.io origin (all GitHub Pages sites), plus any
  // explicitly listed origins (e.g. localhost for local dev).
  const allowed = config.ALLOWED_ORIGIN.split(',').map(s => s.trim());
  const isGitHubPages = /^https:\/\/[a-zA-Z0-9_-]+\.github\.io$/.test(origin);
  const corsOrigin = (isGitHubPages || allowed.includes(origin)) ? origin : allowed[0] || '*';
  return {
    'Access-Control-Allow-Origin': corsOrigin,
    'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
    'Access-Control-Allow-Headers': 'Content-Type, Authorization',
  };
}

// Log all requests
app.use((req, res, next) => {
  console.log(`[${req.method}] ${req.path} origin=${req.headers.origin || '(none)'}`);
  next();
});

app.options('*', (req, res) => {
  res.set(getCorsHeaders(req)).status(204).end();
});

// ---------------------------------------------------------------------------
// GitHub GraphQL helper
// ---------------------------------------------------------------------------
async function ghGraphQL(query, variables, token) {
  const resp = await fetch('https://api.github.com/graphql', {
    method: 'POST',
    headers: {
      Authorization: `Bearer ${token}`,
      'Content-Type': 'application/json',
      'User-Agent': 'fc-oauth-proxy',
    },
    body: JSON.stringify({ query, variables }),
  });
  if (!resp.ok) throw new Error(`GraphQL request failed: ${resp.status}`);
  const json = await resp.json();
  if (json.errors) throw new Error(json.errors[0].message);
  return json.data;
}

// ---------------------------------------------------------------------------
// Fetch all discussions
// ---------------------------------------------------------------------------
async function fetchAllDiscussions(owner, name) {
  const token = await getInstallationToken(owner, name);
  const result = {};

  let hasNextPage = true;
  let afterCursor = null;

  while (hasNextPage) {
    const data = await ghGraphQL(`
      query($owner: String!, $name: String!, $after: String) {
        repository(owner: $owner, name: $name) {
          discussions(first: 100, after: $after) {
            pageInfo { hasNextPage endCursor }
            nodes {
              id
              number
              title
              reactions(content: HEART) { totalCount }
              thumbsUpReactions: reactions(content: THUMBS_UP) { totalCount }
              thumbsDownReactions: reactions(content: THUMBS_DOWN) { totalCount }
              comments(first: 100) {
                pageInfo { hasNextPage endCursor }
                nodes {
                  body
                  author { login }
                }
              }
            }
          }
        }
      }
    `, { owner, name, after: afterCursor }, token);

    const discussions = data.repository.discussions;

    for (const disc of discussions.nodes) {
      let allComments = [...disc.comments.nodes];
      let commentPage = disc.comments.pageInfo;
      while (commentPage.hasNextPage) {
        const cData = await ghGraphQL(`
          query($discId: ID!, $after: String) {
            node(id: $discId) {
              ... on Discussion {
                comments(first: 100, after: $after) {
                  pageInfo { hasNextPage endCursor }
                  nodes {
                    body
                    author { login }
                  }
                }
              }
            }
          }
        `, { discId: disc.id, after: commentPage.endCursor }, token);
        const moreComments = cData.node.comments;
        allComments = allComments.concat(moreComments.nodes);
        commentPage = moreComments.pageInfo;
      }

      const difficultyByUser = {};
      for (const comment of allComments) {
        if (!comment.author) continue;
        const lines = comment.body.split('\n');
        for (const line of lines) {
          const trimmed = line.trim();
          if (/^difficulty [0-9]$/i.test(trimmed)) {
            difficultyByUser[comment.author.login] = parseInt(trimmed.split(' ')[1], 10);
          }
        }
      }

      const values = Object.values(difficultyByUser);
      const numRatings = values.length;
      const avgDifficulty = numRatings > 0
        ? Math.round((values.reduce((a, b) => a + b, 0) / numRatings) * 10) / 10
        : null;

      result[disc.title] = {
        count: disc.reactions.totalCount,
        thumbsUp: disc.thumbsUpReactions.totalCount,
        thumbsDown: disc.thumbsDownReactions.totalCount,
        avgDifficulty,
        numRatings,
        discussionId: disc.id,
        discussionNumber: disc.number,
      };
    }

    hasNextPage = discussions.pageInfo.hasNextPage;
    afterCursor = discussions.pageInfo.endCursor;
  }

  return result;
}

// ---------------------------------------------------------------------------
// Routes
// ---------------------------------------------------------------------------

// POST /token — OAuth code exchange
app.post('/token', async (req, res) => {
  const cors = getCorsHeaders(req);
  res.set(cors);

  const { code } = req.body || {};
  if (!code) {
    return res.status(400).json({ error: 'Missing code parameter' });
  }

  try {
    const ghResponse = await fetch('https://github.com/login/oauth/access_token', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json', Accept: 'application/json' },
      body: JSON.stringify({
        client_id: config.GH_CLIENT_ID,
        client_secret: config.GH_CLIENT_SECRET,
        code,
      }),
    });

    if (!ghResponse.ok) {
      return res.status(502).json({ error: 'GitHub token exchange failed' });
    }

    const data = await ghResponse.json();
    res.json(data);
  } catch (e) {
    console.error('Token exchange error:', e);
    res.status(500).json({ error: 'Token exchange failed' });
  }
});

// GET /discussions?owner=X&repo=Y — read-only proxy for anonymous users
app.get('/discussions', async (req, res) => {
  const cors = getCorsHeaders(req);
  res.set(cors);

  const owner = req.query.owner;
  const repo = req.query.repo;
  if (!owner || !repo) {
    return res.status(400).json({ error: 'Missing owner or repo query parameter' });
  }

  try {
    const data = await fetchAllDiscussions(owner, repo);
    res.set('Cache-Control', 'public, max-age=60').json(data);
  } catch (e) {
    console.error('Failed to fetch discussions:', e);
    res.status(500).json({ error: 'Failed to fetch discussions' });
  }
});

// Fallback 404
app.use((req, res) => {
  res.set(getCorsHeaders(req)).status(404).json({ error: 'Not found' });
});

// ---------------------------------------------------------------------------
// Start
// ---------------------------------------------------------------------------
const PORT = process.env.PORT || 8080;

loadSecrets().then(() => {
  app.listen(PORT, () => {
    console.log(`fc-oauth-proxy listening on port ${PORT}`);
  });
});
