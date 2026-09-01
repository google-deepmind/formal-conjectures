# OAuth Proxy & Voting Worker

A Cloudflare Worker that handles GitHub OAuth token exchange and vote storage via Cloudflare KV.

## Prerequisites

- [Node.js](https://nodejs.org/) >= 18
- A [Cloudflare account](https://dash.cloudflare.com/sign-up) (free tier works)
- A GitHub OAuth App

## Register a GitHub OAuth App

1. Go to GitHub → Settings → Developer Settings → [OAuth Apps](https://github.com/settings/developers)
2. Click **New OAuth App**
3. Fill in:
   - **Application name:** Formal Conjectures Voting
   - **Homepage URL:** Your site URL (e.g., `https://formal-conjectures.github.io`)
   - **Authorization callback URL:** Your site URL (the client handles the redirect)
4. After creating, note the **Client ID** and generate a **Client Secret**

## Setup

```bash
cd worker
npm install
```

## Create KV Namespace

```bash
npx wrangler kv namespace create VOTES
npx wrangler kv namespace create VOTES --preview
```

Copy the output IDs into `wrangler.toml`:

```toml
[[kv_namespaces]]
binding = "VOTES"
id = "<production-id>"
preview_id = "<preview-id>"
```

## Configure Secrets

Store your GitHub OAuth App credentials as Cloudflare Worker secrets:

```bash
npx wrangler secret put GH_CLIENT_ID
npx wrangler secret put GH_CLIENT_SECRET
```

You'll be prompted to enter each value.

## API Endpoints

### `POST /token`
Exchange a GitHub OAuth authorization code for an access token.

**Request:** `{ "code": "..." }`
**Response:** `{ "access_token": "...", "token_type": "bearer", "scope": "" }`

### `GET /votes?user=<login>`
Get all vote counts and difficulty data. The `user` parameter is optional — when provided, the response includes whether that user has voted and their difficulty rating for each theorem.

**Response:** `{ "TheoremName": { "count": 5, "userVoted": true, "avgDifficulty": 6.2, "numRatings": 3, "userDifficulty": 7 }, ... }`

### `POST /vote/:name`
Cast a vote for a theorem. Requires `Authorization: Bearer <token>` header.

**Response:** `{ "count": 6, "userVoted": true }`

### `DELETE /vote/:name`
Remove a vote from a theorem. Requires `Authorization: Bearer <token>` header.

**Response:** `{ "count": 5, "userVoted": false }`

### `POST /difficulty/:name`
Rate the difficulty of a theorem (0–10 integer). Requires `Authorization: Bearer <token>` header.

**Request:** `{ "value": 7 }`
**Response:** `{ "avgDifficulty": 6.2, "numRatings": 3, "userDifficulty": 7 }`

### `DELETE /difficulty/:name`
Remove your difficulty rating from a theorem. Requires `Authorization: Bearer <token>` header.

**Response:** `{ "avgDifficulty": 5.5, "numRatings": 2, "userDifficulty": null }`

## Local Development

```bash
npm run dev
```

This starts a local dev server (default `http://localhost:8787`). For local dev, create a `.dev.vars` file:

```
GH_CLIENT_ID=your_client_id
GH_CLIENT_SECRET=your_client_secret
```

## Deploy

```bash
npm run deploy
```

## Configuration

The `ALLOWED_ORIGIN` variable in `wrangler.toml` controls CORS. Update it to match your deployed site URL.

## KV Data Model

- **Namespace:** `VOTES`
- **Key format:** `votes:{theoremName}`
- **Value format:** `{ "count": N, "voters": ["user1", "user2"], "ratings": { "user1": 7, "user3": 4 } }`

The `voters` array handles deduplication — each GitHub user can only vote once per theorem. The `ratings` object maps GitHub logins to difficulty values (0–10 integers). When the last voter removes their vote and there are no ratings, the KV key is deleted.
