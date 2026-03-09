# Voting System

The Formal Conjectures website includes a voting, truth prediction, and difficulty rating system backed by GitHub Discussions. The Cloudflare Worker handles OAuth token exchange and serves as a read-only proxy for anonymous users. All write operations go directly from the browser to the GitHub GraphQL API using the user's token.

## Architecture

```
Browser (voting.js)
  ├── Anonymous reads → Cloudflare Worker → GitHub GraphQL (GH_READ_TOKEN)
  ├── Authenticated reads → GitHub GraphQL directly (user's token)
  └── All writes → GitHub GraphQL directly (user's token)

Cloudflare Worker (worker/)
  ├── POST /token — OAuth code-for-token exchange
  └── GET /discussions — read-only aggregated discussion data
```

**Important:** This uses a **GitHub App** (not an OAuth App). With GitHub Apps, permissions are defined on the app itself — the OAuth authorization URL does not use `scope` parameters. The user authorizes the app, and the token inherits whatever permissions the app has.

## Data Model

Each theorem gets a GitHub Discussion (lazily created on first interaction):

- **Discussion title** = theorem name (e.g. `FormalConjectures.NumberTheory.GoldbachConjecture.goldbach_conjecture`)
- **Likes** = HEART reactions on the discussion
- **Truth prediction** = THUMBS_UP (true) / THUMBS_DOWN (false) reactions
- **Difficulty** = any comment line matching `/^difficulty [0-9]$/i` (latest per user wins, range 0–9)

## Interaction Types

### Likes (HEART reactions)
- Each user can like once per theorem (toggle on/off)
- Shown as a heart button with count on detail pages and browse cards

### Truth Predictions (THUMBS_UP / THUMBS_DOWN reactions)
- Users predict whether a conjecture is true or false
- Selecting one removes the other (at most one active per user)
- Shown as thumbs up/down buttons with counts

### Difficulty Ratings (Comments)
- Users rate difficulty on a 0–9 scale via comments
- Any line in any comment matching `difficulty N` (0–9) counts as a rating — so users can include a difficulty rating alongside other commentary
- Latest match per user wins (across all their comments)
- When using the UI dropdown, the system posts a pure `difficulty N` comment and auto-deletes previous pure-difficulty comments by that user
- Multi-line comments containing a difficulty line alongside other content are **never** auto-deleted
- Browse page and detail page show the average

### Discussion Link
- The theorem detail page shows a link to the GitHub Discussion (when one exists)
- Users can participate in the discussion directly on GitHub

## OAuth Flow

1. User clicks "Sign in with GitHub"
2. Browser redirects to the GitHub App authorization URL — permissions are defined on the app, **not** via OAuth scopes
3. GitHub redirects back with `?code=...`
4. `voting.js` exchanges the code via the worker's `/token` endpoint
5. Token and username stored in `localStorage`

**Troubleshooting:** If you get "Resource not accessible by integration" errors, the GitHub App is missing permissions or isn't installed on the target repo (see setup steps below).

## Client Configuration

Constants at the top of `src/js/voting.js`:

| Constant | Description |
|---|---|
| `WORKER_URL` | URL of the Cloudflare Worker |
| `GH_CLIENT_ID` | GitHub App client ID (starts with `Iv`) |
| `REPO_OWNER` | GitHub repo owner |
| `REPO_NAME` | GitHub repo name |
| `REPO_ID` | GraphQL node ID of the repository |

## Setting Up

### 1. Enable Discussions

Go to the target repo → **Settings** → **General** → **Features** → check **Discussions**. This creates a default category (e.g. "General") which the system uses to create new discussions.

### 2. Register a GitHub App

Go to GitHub → Settings → Developer Settings → GitHub Apps → **New GitHub App**.

- Set **Callback URL** to your site URL
- Under **Permissions → Repository permissions**, set **Discussions** to **Read and write**
- Note the **Client ID** (starts with `Iv`) and generate a **Client Secret**

### 3. Install the GitHub App on the repo

After creating the app, go to the app's settings page → **Install App** tab → click **Install** next to your account → select the target repository. **This step is required** — without it, user tokens won't have permission to create discussions or reactions, and you'll get "Resource not accessible by integration" errors.

### 4. Create a fine-grained PAT

Go to GitHub → Settings → Developer Settings → Fine-grained tokens. Create a token scoped to the target repository with **Discussions: Read** access. This is used by the worker as `GH_READ_TOKEN` to serve data to anonymous users.

### 5. Record the repository ID

The `REPO_ID` constant in `voting.js` is the GraphQL node ID of the repo. Find it with:
```bash
gh api graphql -f query='{ repository(owner:"OWNER", name:"REPO") { id } }'
```
The `id` field in the response (e.g. `R_kgDO...`) is the value to use.

### 6. Set up the worker

See [`worker/README.md`](../worker/README.md) for secrets configuration and deployment.

### 7. Update `voting.js` constants

Set `WORKER_URL`, `GH_CLIENT_ID`, `REPO_OWNER`, `REPO_NAME`, and `REPO_ID`.

### 8. Build and serve

```bash
npm run build && cd site && python3 -m http.server 8000
```

## Limitations

- Discussion creation requires the user to be authenticated
- GitHub GraphQL API rate limits apply (5,000 requests/hour for authenticated users)
- The worker proxy caches responses for 60 seconds
- Vote counts are cached in memory after the first fetch within a page session
- After changing GitHub App permissions, users must log out and re-authorize to get a token with the updated permissions
