'use strict';

async function verifyUser(token) {
  if (!token) return null;
  try {
    const resp = await fetch('https://api.github.com/user', {
      headers: {
        Authorization: `Bearer ${token}`,
        Accept: 'application/json',
        'User-Agent': 'fc-oauth-proxy',
      },
    });
    if (!resp.ok) return null;
    const user = await resp.json();
    return user.login ? { login: user.login } : null;
  } catch {
    return null;
  }
}

function computeAvgDifficulty(ratings) {
  const values = Object.values(ratings || {});
  if (values.length === 0) return { avgDifficulty: null, numRatings: 0 };
  return {
    avgDifficulty: Math.round((values.reduce((a, b) => a + b, 0) / values.length) * 10) / 10,
    numRatings: values.length,
  };
}

function jsonResponse(data, status, corsHeaders) {
  return new Response(JSON.stringify(data), {
    status,
    headers: { ...corsHeaders, 'Content-Type': 'application/json' },
  });
}

export default {
  async fetch(request, env) {
    const corsHeaders = {
      'Access-Control-Allow-Origin': env.ALLOWED_ORIGIN || '*',
      'Access-Control-Allow-Methods': 'GET, POST, DELETE, OPTIONS',
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

    // GET /votes?user=<login> — all vote counts + optional user vote status
    if (path === '/votes' && request.method === 'GET') {
      const userParam = url.searchParams.get('user') || '';
      const result = {};

      try {
        const list = await env.VOTES.list({ prefix: 'votes:' });
        const fetches = list.keys.map(async (key) => {
          const val = await env.VOTES.get(key.name, { type: 'json' });
          if (!val) return;
          const theoremName = key.name.slice('votes:'.length);
          const ratings = val.ratings || {};
          const { avgDifficulty, numRatings } = computeAvgDifficulty(ratings);
          result[theoremName] = {
            count: val.count || 0,
            userVoted: userParam ? (val.voters || []).includes(userParam) : false,
            avgDifficulty,
            numRatings,
            userDifficulty: userParam ? (ratings[userParam] ?? null) : null,
          };
        });
        await Promise.all(fetches);
      } catch (e) {
        return jsonResponse({ error: 'Failed to read votes' }, 500, corsHeaders);
      }

      return jsonResponse(result, 200, corsHeaders);
    }

    // POST /vote/:name — cast a vote (auth required)
    const voteMatch = path.match(/^\/vote\/(.+)$/);
    if (voteMatch && request.method === 'POST') {
      const token = (request.headers.get('Authorization') || '').replace('Bearer ', '');
      const user = await verifyUser(token);
      if (!user) {
        return jsonResponse({ error: 'Unauthorized' }, 401, corsHeaders);
      }

      const theoremName = decodeURIComponent(voteMatch[1]);
      const key = `votes:${theoremName}`;
      const val = await env.VOTES.get(key, { type: 'json' }) || { count: 0, voters: [] };

      if (!val.voters.includes(user.login)) {
        val.voters.push(user.login);
        val.count = val.voters.length;
        await env.VOTES.put(key, JSON.stringify(val));
      }

      return jsonResponse({ count: val.count, userVoted: true }, 200, corsHeaders);
    }

    // DELETE /vote/:name — remove a vote (auth required)
    if (voteMatch && request.method === 'DELETE') {
      const token = (request.headers.get('Authorization') || '').replace('Bearer ', '');
      const user = await verifyUser(token);
      if (!user) {
        return jsonResponse({ error: 'Unauthorized' }, 401, corsHeaders);
      }

      const theoremName = decodeURIComponent(voteMatch[1]);
      const key = `votes:${theoremName}`;
      const val = await env.VOTES.get(key, { type: 'json' }) || { count: 0, voters: [], ratings: {} };

      const idx = val.voters.indexOf(user.login);
      if (idx !== -1) {
        val.voters.splice(idx, 1);
        val.count = val.voters.length;
        const hasRatings = Object.keys(val.ratings || {}).length > 0;
        if (val.count === 0 && !hasRatings) {
          await env.VOTES.delete(key);
        } else {
          await env.VOTES.put(key, JSON.stringify(val));
        }
      }

      return jsonResponse({ count: val.count, userVoted: false }, 200, corsHeaders);
    }

    // POST /difficulty/:name — rate difficulty (auth required)
    const diffMatch = path.match(/^\/difficulty\/(.+)$/);
    if (diffMatch && request.method === 'POST') {
      const token = (request.headers.get('Authorization') || '').replace('Bearer ', '');
      const user = await verifyUser(token);
      if (!user) {
        return jsonResponse({ error: 'Unauthorized' }, 401, corsHeaders);
      }

      const body = await request.json().catch(() => ({}));
      const value = body.value;
      if (!Number.isInteger(value) || value < 0 || value > 10) {
        return jsonResponse({ error: 'Value must be an integer 0–10' }, 400, corsHeaders);
      }

      const theoremName = decodeURIComponent(diffMatch[1]);
      const key = `votes:${theoremName}`;
      const val = await env.VOTES.get(key, { type: 'json' }) || { count: 0, voters: [], ratings: {} };
      if (!val.ratings) val.ratings = {};

      val.ratings[user.login] = value;
      await env.VOTES.put(key, JSON.stringify(val));

      const { avgDifficulty, numRatings } = computeAvgDifficulty(val.ratings);
      return jsonResponse({ avgDifficulty, numRatings, userDifficulty: value }, 200, corsHeaders);
    }

    // DELETE /difficulty/:name — remove difficulty rating (auth required)
    if (diffMatch && request.method === 'DELETE') {
      const token = (request.headers.get('Authorization') || '').replace('Bearer ', '');
      const user = await verifyUser(token);
      if (!user) {
        return jsonResponse({ error: 'Unauthorized' }, 401, corsHeaders);
      }

      const theoremName = decodeURIComponent(diffMatch[1]);
      const key = `votes:${theoremName}`;
      const val = await env.VOTES.get(key, { type: 'json' }) || { count: 0, voters: [], ratings: {} };
      if (!val.ratings) val.ratings = {};

      delete val.ratings[user.login];

      const hasVoters = (val.voters || []).length > 0;
      const hasRatings = Object.keys(val.ratings).length > 0;
      if (!hasVoters && !hasRatings) {
        await env.VOTES.delete(key);
      } else {
        await env.VOTES.put(key, JSON.stringify(val));
      }

      const { avgDifficulty, numRatings } = computeAvgDifficulty(val.ratings);
      return jsonResponse({ avgDifficulty, numRatings, userDifficulty: null }, 200, corsHeaders);
    }

    return new Response('Not found', { status: 404, headers: corsHeaders });
  },
};
