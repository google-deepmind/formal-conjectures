# OAuth Proxy & Discussions Reader — App Engine

A repo-agnostic App Engine service that provides GitHub App OAuth token exchange and a read-only proxy for GitHub Discussions data. One deployment can serve multiple repositories.

## Default Shared Proxy

The Formal Conjectures project runs a shared proxy on the `formal-conjectures-web-worker` GCP project. This is used by the default `voting.js` configuration, so **forkers do not need to deploy their own proxy**.

The shared proxy:
- Handles OAuth token exchange for the [formal-conjectures-voting](https://github.com/apps/formal-conjectures-voting) GitHub App (`Iv23lid2mjCGp7EIKrJn`)
- Reads discussions from any repo passed via `?owner=X&repo=Y`
- Requires its `GH_READ_TOKEN` to have Discussions read access on repos that use it

To use the shared proxy with a new fork:
1. Install the GitHub App on your fork: https://github.com/apps/formal-conjectures-voting/installations/new
2. The `GH_READ_TOKEN` PAT must be updated to include the fork's repo in its scope — contact the maintainer to request access.

## Running Your Own Proxy

If you prefer to run your own proxy (e.g. for a private fork, or to avoid depending on the shared service), follow the steps below.

### Prerequisites

- [Node.js](https://nodejs.org/) >= 20
- [Google Cloud SDK](https://cloud.google.com/sdk/docs/install) (`gcloud` CLI)
- A GCP project with App Engine enabled

### Setup

```bash
cd site/appengine
npm install
```

### Creating the GitHub App and Tokens

#### GitHub App (`GH_CLIENT_ID` and `GH_CLIENT_SECRET`)

1. Go to https://github.com/settings/apps/new
2. Fill in:
   - **App name**: anything (e.g. "FC Voting")
   - **Homepage URL**: your site URL
   - **Callback URL**: your site URL (must match where users are redirected after OAuth)
   - **Webhook**: uncheck "Active" (not needed)
3. Under **Permissions > Repository permissions**, set **Discussions** to **Read & write**
4. Click **Create GitHub App**
5. On the app's settings page, copy the **Client ID** (`GH_CLIENT_ID`)
6. Click **Generate a new client secret** and copy it (`GH_CLIENT_SECRET`)
7. **Install the app** on your repo: go to https://github.com/settings/apps, click your app, then **Install App**, and select the target repository

#### Fine-grained PAT (`GH_READ_TOKEN`)

This token is used by the proxy to read discussions without requiring the user to be logged in.

1. Go to https://github.com/settings/personal-access-tokens/new
2. Fill in:
   - **Token name**: anything (e.g. "FC Discussions Reader")
   - **Expiration**: choose an appropriate lifetime
   - **Repository access**: select **Only select repositories** and pick the repos that will use this proxy
3. Under **Permissions > Repository permissions**, set **Discussions** to **Read-only**
4. Click **Generate token** and copy it (`GH_READ_TOKEN`)

### Secrets

The server loads secrets from environment variables if set, otherwise from [Google Cloud Secret Manager](https://cloud.google.com/secret-manager). This means local dev uses env vars and production uses Secret Manager — same code, no config files with real secrets.

#### Storing secrets in Secret Manager (production)

```bash
echo -n "your_client_id"     | gcloud secrets create GH_CLIENT_ID --data-file=-
echo -n "your_client_secret" | gcloud secrets create GH_CLIENT_SECRET --data-file=-
echo -n "your_read_token"    | gcloud secrets create GH_READ_TOKEN --data-file=-
```

Grant the App Engine service account access:

```bash
PROJECT_ID=$(gcloud config get-value project)
for SECRET in GH_CLIENT_ID GH_CLIENT_SECRET GH_READ_TOKEN; do
  gcloud secrets add-iam-policy-binding $SECRET \
    --member="serviceAccount:${PROJECT_ID}@appspot.gserviceaccount.com" \
    --role="roles/secretmanager.secretAccessor"
done
```

### Local Development

```bash
cd site/appengine
export GH_CLIENT_ID=your_client_id
export GH_CLIENT_SECRET=your_client_secret
export GH_READ_TOKEN=your_read_token
export ALLOWED_ORIGIN=http://localhost:8000
node server.js
```

Then edit `src/js/voting.js` to point `WORKER_URL` at `http://localhost:8080` and serve the site:

```bash
cd site/site
python3 -m http.server 8000
```

### Deploy

Edit `app.yaml` to set `ALLOWED_ORIGIN` for your deployment (comma-separated list of allowed origins), then:

```bash
gcloud app deploy
```

Secrets are loaded from Secret Manager automatically at startup.

Your service will be available at `https://PROJECT_ID.REGION_ID.r.appspot.com`. Update `WORKER_URL` in `voting.js` to point to this URL.

## API Endpoints

### `POST /token`

OAuth code exchange. Receives `{ "code": "..." }` and exchanges it for a GitHub access token using the GitHub App's client secret.

### `GET /discussions?owner=OWNER&repo=REPO`

Returns aggregated discussion data for the given repository. Includes vote counts (HEART reactions), truth predictions (THUMBS_UP/DOWN), and average difficulty ratings (parsed from comments). Response is cached for 60 seconds.

## Configuration

| Variable | Source | Description |
|---|---|---|
| `ALLOWED_ORIGIN` | `app.yaml` / env | CORS allowed origin(s), comma-separated |
| `GH_CLIENT_ID` | Secret Manager / env | GitHub App client ID |
| `GH_CLIENT_SECRET` | Secret Manager / env | GitHub App client secret |
| `GH_READ_TOKEN` | Secret Manager / env | Fine-grained PAT for anonymous reads |

## Cost

App Engine standard F1 instances include 28 free instance hours/day. With `max_instances: 1` in `app.yaml`, this proxy stays well within the free tier for typical usage.
