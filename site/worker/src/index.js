'use strict';

function jsonResponse(data, status, corsHeaders) {
  return new Response(JSON.stringify(data), {
    status,
    headers: { ...corsHeaders, 'Content-Type': 'application/json' },
  });
}

async function fetchAllDiscussions(env) {
  const token = env.GH_READ_TOKEN;
  const owner = env.GH_REPO_OWNER;
  const name = env.GH_REPO_NAME;
  const result = {};

  let hasNextPage = true;
  let afterCursor = null;

  while (hasNextPage) {
    const query = `
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
    `;

    const resp = await fetch('https://api.github.com/graphql', {
      method: 'POST',
      headers: {
        Authorization: `Bearer ${token}`,
        'Content-Type': 'application/json',
        'User-Agent': 'fc-oauth-proxy',
      },
      body: JSON.stringify({ query, variables: { owner, name, after: afterCursor } }),
    });

    if (!resp.ok) throw new Error(`GitHub API error: ${resp.status}`);
    const json = await resp.json();
    if (json.errors) throw new Error(json.errors[0].message);

    const discussions = json.data.repository.discussions;

    for (const disc of discussions.nodes) {
      // Paginate comments if needed
      let allComments = [...disc.comments.nodes];
      let commentPage = disc.comments.pageInfo;
      while (commentPage.hasNextPage) {
        const cQuery = `
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
        `;
        const cResp = await fetch('https://api.github.com/graphql', {
          method: 'POST',
          headers: {
            Authorization: `Bearer ${token}`,
            'Content-Type': 'application/json',
            'User-Agent': 'fc-oauth-proxy',
          },
          body: JSON.stringify({ query: cQuery, variables: { discId: disc.id, after: commentPage.endCursor } }),
        });
        if (!cResp.ok) break;
        const cJson = await cResp.json();
        if (cJson.errors) break;
        const moreComments = cJson.data.node.comments;
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

export default {
  async fetch(request, env) {
    const origin = request.headers.get('Origin') || '';
    const allowed = (env.ALLOWED_ORIGIN || '').split(',').map(s => s.trim());
    const corsOrigin = allowed.includes(origin) ? origin : allowed[0] || '*';
    const corsHeaders = {
      'Access-Control-Allow-Origin': corsOrigin,
      'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
      'Access-Control-Allow-Headers': 'Content-Type, Authorization',
    };

    if (request.method === 'OPTIONS') {
      return new Response(null, { status: 204, headers: corsHeaders });
    }

    const url = new URL(request.url);
    const path = url.pathname;

    // POST /token — OAuth code exchange
    if (path === '/token' && request.method === 'POST') {
      const { code } = await request.json().catch(() => ({}));
      if (!code) {
        return jsonResponse({ error: 'Missing code parameter' }, 400, corsHeaders);
      }

      const ghResponse = await fetch('https://github.com/login/oauth/access_token', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', Accept: 'application/json' },
        body: JSON.stringify({
          client_id: env.GH_CLIENT_ID,
          client_secret: env.GH_CLIENT_SECRET,
          code,
        }),
      });

      if (!ghResponse.ok) {
        return jsonResponse({ error: 'GitHub token exchange failed' }, 502, corsHeaders);
      }

      const data = await ghResponse.json();
      return jsonResponse(data, 200, corsHeaders);
    }

    // GET /discussions — read-only proxy for anonymous users
    if (path === '/discussions' && request.method === 'GET') {
      try {
        const data = await fetchAllDiscussions(env);
        return new Response(JSON.stringify(data), {
          status: 200,
          headers: {
            ...corsHeaders,
            'Content-Type': 'application/json',
            'Cache-Control': 'public, max-age=60',
          },
        });
      } catch (e) {
        console.error('Failed to fetch discussions:', e);
        return jsonResponse({ error: 'Failed to fetch discussions' }, 500, corsHeaders);
      }
    }

    return new Response('Not found', { status: 404, headers: corsHeaders });
  },
};
