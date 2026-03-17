'use strict';

const express = require('express');

const app = express();
app.use(express.json());

// ---------------------------------------------------------------------------
// Configuration — loaded at startup, secrets filled in by loadSecrets()
// ---------------------------------------------------------------------------
const config = {
  ALLOWED_ORIGIN:    process.env.ALLOWED_ORIGIN || '*',
  GH_CLIENT_ID:      process.env.GH_CLIENT_ID || '',
  GH_CLIENT_SECRET:  process.env.GH_CLIENT_SECRET || '',
  GH_READ_TOKEN:     process.env.GH_READ_TOKEN || '',
};

// Names of secrets to load from Secret Manager (only those not already set)
const SECRET_NAMES = ['GH_CLIENT_ID', 'GH_CLIENT_SECRET', 'GH_READ_TOKEN'];

/**
 * Load any missing secrets from Google Cloud Secret Manager.
 * If all secrets are already set via environment variables (local dev), this
 * is a no-op. In production on App Engine, environment variables are not set
 * for secrets — they come from Secret Manager instead.
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

  // Resolve project ID from the client (uses ADC / metadata server)
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
// CORS
// ---------------------------------------------------------------------------
function getCorsHeaders(req) {
  const origin = req.headers.origin || '';
  const allowed = config.ALLOWED_ORIGIN.split(',').map(s => s.trim());
  const corsOrigin = allowed.includes(origin) ? origin : allowed[0] || '*';
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
  if (!resp.ok) throw new Error(`GitHub API error: ${resp.status}`);
  const json = await resp.json();
  if (json.errors) throw new Error(json.errors[0].message);
  return json.data;
}

// ---------------------------------------------------------------------------
// Fetch all discussions
// ---------------------------------------------------------------------------
async function fetchAllDiscussions(owner, name) {
  const token = config.GH_READ_TOKEN;
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
      // Paginate comments if needed
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

      // Parse difficulty from comments: scan each line for /^difficulty [0-9]$/i
      // Latest match per user wins (comments are in chronological order)
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
