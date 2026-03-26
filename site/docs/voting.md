# Voting System

The Formal Conjectures website includes a voting, truth prediction, and difficulty rating system backed by GitHub Discussions. GitHub OAuth is used for identity verification — the consent screen requires zero additional OAuth scopes.

## Architecture

```
Browser (voting.js)
  ├── Reads: GET /discussions?owner=X&repo=Y → App Engine proxy → GitHub GraphQL
  └── Writes: directly → GitHub GraphQL (user's OAuth token)
        ├── Likes = HEART reactions on Discussion
        ├── Truth predictions = THUMBS_UP / THUMBS_DOWN reactions
        └── Difficulty ratings = comments matching /^difficulty [0-9]$/i
```

All data is stored as native GitHub Discussions features (reactions and comments) on the repository. There is no separate database.

A shared App Engine proxy (`formal-conjectures-web-worker`) handles OAuth token exchange and anonymous discussion reads. It uses GitHub App installation tokens, so it works automatically for any repo where the [formal-conjectures-voting](https://github.com/apps/formal-conjectures-voting) app is installed. The proxy only serves `google-deepmind/formal-conjectures` and its forks.

OAuth callbacks are also routed through the proxy, so a single registered callback URL works for all forks — no per-fork GitHub App configuration is needed.

## How It Works for Forkers

To deploy the website with voting on your fork:

1. **Enable GitHub Pages** on the fork (Settings > Pages > GitHub Actions)
2. **Enable Discussions** on the fork (Settings > General > Features)
3. **Create a "Problems" discussion category** (Discussions > Categories > New category, name it exactly `Problems`, choose the "Open-ended discussion" format)
4. **Install the GitHub App**: https://github.com/apps/formal-conjectures-voting/installations/new
5. **Push a branch ending in `-webtest`** (e.g. `my-feature-webtest`)

The CI workflow configures everything automatically. No GCP project, secrets, or tokens are needed.

If the GitHub App is not installed, vote counts won't load but the rest of the site works normally.

## Webtest Branches

Branches whose name ends with `-webtest` trigger a fast website-only build:

- The Lean build, docgen, and `extract_names` steps are **skipped**
- The conjectures JSON is **downloaded from the live site**
- Voting configuration is **injected automatically** from the repository context
- The site is **deployed to GitHub Pages**

This works on any repo, including upstream. On `main`, the full Lean build runs and voting is also configured.

Branches without the `-webtest` suffix are unaffected — PRs and feature branches run the normal build without deploying.

## How Votes Work

- Each user can vote once per theorem (like/unlike toggle via HEART reaction)
- Discussions are created lazily when a logged-in user first views a theorem's discussion link, or when they first vote/predict/rate
- Discussion titles are the fully-qualified Lean theorem name

## Truth Predictions

- Users can predict whether a conjecture is true (thumbs up) or false (thumbs down)
- Each user can have one prediction per theorem; changing removes the old one
- The browse page shows aggregated prediction counts

## Difficulty Ratings

- Users can rate the difficulty of each theorem on a 0-9 scale
- Ratings are stored as discussion comments containing only `difficulty N`
- Submitting a new rating deletes the previous single-line rating comment
- The browse page shows the average difficulty alongside the vote count

## Consent Modal

The first time a user clicks vote, predict, or rate difficulty, a modal explains:
- Why GitHub login is needed (identity verification, zero additional OAuth scopes)
- That all activity is public (stored as GitHub Discussions, visible to anyone)
- What specifically is stored (heart reactions, thumbs reactions, comments)

The user acts with their own GitHub permissions. The acknowledgement is stored in `localStorage` so the modal only appears once per browser.

## OAuth Flow

1. User clicks a voting/prediction/rating action
2. Consent modal appears (first time only)
3. Browser redirects to GitHub OAuth; the callback URL points to the shared proxy
4. GitHub redirects to the proxy's `/oauth/callback` with `?code=...`
5. The proxy validates the return URL and bounces the code back to the user's site
6. `voting.js` exchanges the code for a token via the proxy's `/token` endpoint
7. Token and username are stored in `localStorage`

## Client Configuration

Constants at the top of `src/js/voting.js` (placeholders replaced by CI at build time):

| Constant | Injected value | Description |
|---|---|---|
| `WORKER_URL` | `https://formal-conjectures-web-worker.uc.r.appspot.com` | Shared proxy URL |
| `GH_CLIENT_ID` | `Iv23lid2mjCGp7EIKrJn` | Shared GitHub App client ID |
| `REPO_OWNER` | From `github.repository_owner` | GitHub repo owner |
| `REPO_NAME` | From `github.event.repository.name` | GitHub repo name |
| `REPO_ID` | Fetched via GitHub API | GitHub repo GraphQL node ID |

For local development, edit these directly in `voting.js`.

## Local Development

1. **Start the proxy** (see [`appengine/README.md`](../appengine/README.md) for details):

```bash
cd site/appengine && npm install
export GH_APP_ID=3005907
export GH_CLIENT_ID=your_client_id
export GH_CLIENT_SECRET=your_client_secret
export GH_APP_PRIVATE_KEY="$(cat path/to/private-key.pem)"
export ALLOWED_ORIGIN=http://localhost:8000
node server.js
```

2. **Edit `voting.js`** constants to point at localhost and your repo.

3. **Build and serve**:

```bash
cd site && node build.js && cd site && python3 -m http.server 8000
```

## Running Your Own Proxy

See [`appengine/README.md`](../appengine/README.md) for full instructions on deploying your own App Engine proxy.

## Limitations

- GitHub GraphQL API rate limits (5000 points/hour for authenticated users)
- The `/discussions` endpoint paginates all discussions, which may be slow with very large numbers
- Vote counts are cached in memory per page session
- The proxy caches discussion data for 60 seconds
- The GitHub App must be installed on any repo that uses the shared proxy
- Webtest builds depend on the live site being available for the conjectures JSON
