# Voting System

The Formal Conjectures website includes a voting, truth prediction, and difficulty rating system backed by GitHub Discussions. GitHub OAuth is used for identity verification — the consent screen requires zero permissions ("Verify your GitHub identity").

## Architecture

```
Browser (voting.js)
  ├── Reads: GET /discussions?owner=X&repo=Y → App Engine proxy → GitHub GraphQL (read-only PAT)
  └── Writes: directly → GitHub GraphQL (user's OAuth token)
        ├── Likes = HEART reactions on Discussion
        ├── Truth predictions = THUMBS_UP / THUMBS_DOWN reactions
        └── Difficulty ratings = comments matching /^difficulty [0-9]$/i
```

All data is stored as native GitHub Discussions features (reactions and comments) on the repository. There is no separate database.

A shared App Engine proxy (`formal-conjectures-web-worker`) handles OAuth token exchange and anonymous discussion reads for all forks. The proxy is repo-agnostic — the client passes the repo owner and name as query parameters.

## How It Works for Forkers

The default configuration works out of the box for any fork:

1. **Enable GitHub Pages** on the fork (Settings > Pages > GitHub Actions)
2. **Enable Discussions** on the fork (Settings > General > Features)
3. **Install the GitHub App** on the fork: go to https://github.com/apps/formal-conjectures-voting/installations/new, select your fork, and grant it access

The CI workflow (`-webtest` branches) automatically sets `REPO_OWNER`, `REPO_NAME`, and `REPO_ID` from the repository context. The shared proxy URL and GitHub App client ID are built into the defaults.

No GCP project, secrets, or tokens are needed for a forker to use the voting system.

## How Votes Work

- Each user can vote once per theorem (like/unlike toggle via HEART reaction)
- Discussions are created lazily: a Discussion is created when a logged-in user first views a theorem detail page (or when the first interaction occurs)
- Discussion titles are the fully-qualified Lean theorem name

## Truth Predictions

- Users can predict whether a conjecture is true (thumbs up) or false (thumbs down)
- Each user can have one prediction per theorem; changing your prediction removes the old one
- The browse page shows aggregated prediction counts

## Difficulty Ratings

- Users can rate the difficulty of each theorem on a 0-9 scale
- Ratings are stored as discussion comments matching `difficulty N`
- Submitting a new rating deletes the previous rating comment
- The browse page shows the average difficulty alongside the vote count

## Consent Modal

The first time a user clicks vote, predict, or rate difficulty, a modal dialog explains:
- Why GitHub login is needed (identity verification only, zero permissions)
- That all activity is public (stored as GitHub Discussions, visible to anyone)
- What specifically is stored (heart reactions, thumbs reactions, comments)

The acknowledgement is stored in `localStorage` so it only appears once.

## OAuth Flow

1. User clicks a voting/prediction/rating action
2. Consent modal appears (first time only) explaining public nature of activity
3. Browser redirects to `https://github.com/login/oauth/authorize` with `client_id` and `redirect_uri` (no scopes — zero permissions)
4. GitHub redirects back to the page with `?code=...`
5. `voting.js` detects the code, POSTs `{ code }` to the App Engine proxy's `/token` endpoint
6. The proxy exchanges the code for an access token using the GitHub App's client secret
7. `voting.js` fetches `/user` from GitHub to get the username
8. Token and username are stored in `localStorage`

## Client Configuration

Constants at the top of `src/js/voting.js`:

| Constant | Default | Description |
|---|---|---|
| `WORKER_URL` | Shared `formal-conjectures-web-worker` App Engine URL | Proxy for OAuth + discussion reads |
| `GH_CLIENT_ID` | `Iv23lid2mjCGp7EIKrJn` | Shared GitHub App client ID |
| `REPO_OWNER` | Set by CI workflow | GitHub repo owner |
| `REPO_NAME` | Set by CI workflow | GitHub repo name |
| `REPO_ID` | Set by CI workflow | GitHub repo GraphQL node ID |

For local development, edit these constants directly in `voting.js`.

## Local Development

To run the full voting system locally:

1. **Start the App Engine proxy** (see [`appengine/README.md`](../appengine/README.md)):

```bash
cd site/appengine
export GH_CLIENT_ID=your_client_id
export GH_CLIENT_SECRET=your_client_secret
export GH_READ_TOKEN=your_read_token
export ALLOWED_ORIGIN=http://localhost:8000
node server.js
```

2. **Edit `voting.js`** to point at localhost:

```js
const WORKER_URL = 'http://localhost:8080';
const REPO_OWNER = 'your_github_user';
const REPO_NAME  = 'formal-conjectures';
// ...
```

3. **Build and serve the site**:

```bash
cd site
node build.js
cd site
python3 -m http.server 8000
```

## Running Your Own Proxy

If you want to run your own App Engine proxy instead of using the shared one, see [`appengine/README.md`](../appengine/README.md) for full setup instructions.

## Limitations

- GitHub GraphQL API has rate limits (5000 points/hour for authenticated users)
- The `GET /discussions` endpoint paginates through all discussions, which may be slow with very large numbers
- Vote counts are cached in memory after the first fetch within a page session
- The App Engine proxy caches discussion data for 60 seconds
- The shared proxy's `GH_READ_TOKEN` must have Discussions read access on any repo that uses it
