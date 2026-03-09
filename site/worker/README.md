# OAuth Proxy & Discussions Reader Worker

A Cloudflare Worker that handles GitHub App OAuth token exchange and provides a read-only proxy for GitHub Discussions data (for anonymous users).

**Important:** This uses a **GitHub App**, not an OAuth App. Permissions are set on the app itself, not via OAuth scopes. The app must be installed on the target repo for user tokens to work.

## Prerequisites

- [Node.js](https://nodejs.org/) >= 18
- A [Cloudflare account](https://dash.cloudflare.com/sign-up) (free tier works)
- A GitHub App with Discussions: Read & Write permission, installed on the target repo
- A GitHub fine-grained PAT with read-only Discussions access

## Register a GitHub App

1. Go to GitHub → Settings → Developer Settings → [GitHub Apps](https://github.com/settings/apps)
2. Click **New GitHub App**
3. Fill in:
   - **GitHub App name:** Formal Conjectures Voting
   - **Homepage URL:** Your site URL (e.g., `https://formal-conjectures.github.io`)
   - **Callback URL:** Your site URL (the client handles the redirect)
   - **Request user authorization (OAuth) during installation:** checked
4. Under **Permissions → Repository permissions**, set **Discussions** to **Read and write**
5. After creating, note the **Client ID** (starts with `Iv`) and generate a **Client Secret**

## Install the App on the Repo

After creating the app, go to the app's settings page → **Install App** tab → click **Install** next to your account → select the target repository.

**This is required.** Without installation, user tokens won't have access to the repo's discussions, and all GraphQL mutations will fail with "Resource not accessible by integration".

## Create a Read-Only PAT

1. Go to GitHub → Settings → Developer Settings → [Fine-grained tokens](https://github.com/settings/tokens?type=beta)
2. Create a token scoped to the target repository with **Discussions: Read** access
3. This token is used by the worker to serve discussion data to anonymous users

## Setup

```bash
cd worker
npm install
```

## Configure Secrets

```bash
npx wrangler secret put GH_CLIENT_ID
npx wrangler secret put GH_CLIENT_SECRET
npx wrangler secret put GH_READ_TOKEN
```

- `GH_CLIENT_ID` / `GH_CLIENT_SECRET` — from your GitHub App
- `GH_READ_TOKEN` — the fine-grained PAT with read-only Discussions access

## API Endpoints

### `POST /token`
Exchange a GitHub App OAuth authorization code for an access token.

**Request:** `{ "code": "..." }`
**Response:** `{ "access_token": "...", "token_type": "bearer", "scope": "..." }`

### `GET /discussions`
Get aggregated discussion data for all theorems. Used by anonymous users who can't query GitHub directly.

**Response:**
```json
{
  "TheoremName": {
    "count": 5,
    "thumbsUp": 12,
    "thumbsDown": 3,
    "avgDifficulty": 6.2,
    "numRatings": 3,
    "discussionId": "D_kwDO...",
    "discussionNumber": 1
  }
}
```

Response includes `Cache-Control: public, max-age=60`.

## Local Development

```bash
npm run dev
```

This starts a local dev server (default `http://localhost:8787`). For local dev, create a `.dev.vars` file:

```
GH_CLIENT_ID=your_client_id
GH_CLIENT_SECRET=your_client_secret
GH_READ_TOKEN=your_read_token
ALLOWED_ORIGIN=http://localhost:8000
```

**CORS:** The `ALLOWED_ORIGIN` variable controls which origins are allowed. It supports comma-separated values (e.g. `http://localhost:8000,http://localhost:8080`). In `.dev.vars` it overrides the production value from `wrangler.toml`. Make sure it matches the port your local site is served on, or you'll get CORS errors.

## Deploy

```bash
npm run deploy
```

## Configuration

| Variable | Location | Description |
|---|---|---|
| `ALLOWED_ORIGIN` | `wrangler.toml` (production), `.dev.vars` (local override) | CORS allowed origin(s), comma-separated |
| `GH_REPO_OWNER` | `wrangler.toml` | GitHub repo owner |
| `GH_REPO_NAME` | `wrangler.toml` | GitHub repo name |
| `GH_CLIENT_ID` | Secret | GitHub App client ID |
| `GH_CLIENT_SECRET` | Secret | GitHub App client secret |
| `GH_READ_TOKEN` | Secret | Fine-grained PAT for anonymous reads |

## Troubleshooting

- **CORS errors:** Check that `ALLOWED_ORIGIN` (in `.dev.vars` for local dev) matches the origin your site is served from (including port)
- **500 on `/discussions`:** Check that `GH_READ_TOKEN` has Discussions read access and that `GH_REPO_OWNER`/`GH_REPO_NAME` in `wrangler.toml` point to the correct repo
- **"Resource not accessible by integration":** The GitHub App isn't installed on the target repo — see "Install the App on the Repo" above
- **401 Unauthorized on GraphQL:** The user's token is invalid or expired — log out and re-authorize. This can also happen after changing the app's permissions
