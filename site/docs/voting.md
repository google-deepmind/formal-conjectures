# Voting System

The Formal Conjectures website includes a voting and difficulty rating system. Votes and ratings are stored in Cloudflare KV via a worker. GitHub OAuth is used only for identity verification — the consent screen requires zero permissions ("Verify your GitHub identity").

## Architecture

```
Browser (voting.js)
  └── All operations → Cloudflare Worker (worker/)
        ├── OAuth token exchange
        ├── Vote and difficulty CRUD
        └── Cloudflare KV storage
```

No GitHub API calls are made from the browser except `/user` during OAuth login to fetch the username. See [`worker/README.md`](../worker/README.md) for API endpoints, KV data model, and worker setup.

## How Votes Work

- Each user can vote once per theorem (like/unlike toggle)
- Deduplication is handled via a `voters` array in the KV value
- When a vote is removed and there are no remaining votes or ratings, the KV key is deleted

## Difficulty Ratings

- Users can independently rate the difficulty of each theorem on a 0–10 scale
- Each user can rate each theorem once; submitting again overwrites the previous rating
- The browse page shows the average difficulty alongside the vote count
- The theorem detail page shows a dropdown to rate difficulty and the current average

## OAuth Flow

1. User clicks "Sign in with GitHub"
2. Browser redirects to `https://github.com/login/oauth/authorize` with `client_id` and `redirect_uri` (no scopes — zero permissions)
3. GitHub redirects back to the page with `?code=...`
4. `voting.js` detects the code, POSTs `{ code }` to the worker's `/token` endpoint
5. The worker exchanges the code for an access token using the client secret
6. `voting.js` fetches `/user` from GitHub to get the username
7. Token and username are stored in `localStorage`

## Client Configuration

Two constants at the top of `src/js/voting.js`:

| Constant | Description |
|---|---|
| `WORKER_URL` | URL of the Cloudflare Worker |
| `GH_CLIENT_ID` | GitHub OAuth App client ID |

## Setting Up for Development

1. **Register a GitHub OAuth App** at https://github.com/settings/developers
   - Set the callback URL to your local dev URL (e.g., `http://localhost:8000`)
   - Do NOT request any scopes (zero permissions)
2. **Set up the worker** — follow [`worker/README.md`](../worker/README.md) for KV namespace creation, secrets, and local dev
3. **Update `voting.js` constants** — point `WORKER_URL` to `http://localhost:8787`, set `GH_CLIENT_ID`
4. **Start the worker**: `cd worker && npm run dev`
5. **Build and serve the site**: `npm run build && cd site && python3 -m http.server 8000`

## Deploying to Production

1. **Create a GitHub OAuth App** (or reuse the dev one) — set the **Authorization callback URL** to your production site URL
2. **Deploy the worker** — follow [`worker/README.md`](../worker/README.md) for KV namespace, secrets, CORS origin, and deployment
3. **Update `voting.js` constants** — set `WORKER_URL` to your deployed worker URL and `GH_CLIENT_ID` to your production client ID
4. **Build and deploy the site**: `npm run build` and deploy the `site/` directory (e.g., via GitHub Pages)

## Limitations

- Cloudflare KV is eventually consistent — there may be brief delays before vote counts update across regions
- The `GET /votes` endpoint lists all KV keys, which may be slow with very large numbers of voted theorems
- Vote counts are cached in memory after the first fetch within a page session
