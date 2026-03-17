# OAuth Proxy & Discussions Reader — App Engine

A Google App Engine service that provides GitHub App OAuth token exchange and a read-only proxy for GitHub Discussions data.

**Important:** This uses a **GitHub App**, not an OAuth App. Permissions are set on the app itself, not via OAuth scopes. The app must be installed on the target repo for user tokens to work.

## Prerequisites

- [Node.js](https://nodejs.org/) >= 20
- [Google Cloud SDK](https://cloud.google.com/sdk/docs/install) (`gcloud` CLI)
- A GCP project with App Engine enabled

## Setup

```bash
cd appengine
npm install
```

## Creating the GitHub App and Tokens

### GitHub App (`GH_CLIENT_ID` and `GH_CLIENT_SECRET`)

1. Go to https://github.com/settings/apps/new
2. Fill in:
   - **App name**: anything (e.g. "FC Voting Dev")
   - **Homepage URL**: `http://localhost:8000` (or your production URL)
   - **Callback URL**: `http://localhost:8000` (must match where users are redirected after OAuth)
   - **Webhook**: uncheck "Active" (not needed)
3. Under **Permissions > Repository permissions**, set **Discussions** to **Read & write**
4. Click **Create GitHub App**
5. On the app's settings page, copy the **Client ID** (`GH_CLIENT_ID`)
6. Click **Generate a new client secret** and copy it (`GH_CLIENT_SECRET`)
7. **Install the app** on your repo: go to https://github.com/settings/apps, click your app, then **Install App**, and select the target repository

### Fine-grained PAT (`GH_READ_TOKEN`)

This token is used by the proxy to read discussions anonymously (without requiring users to be logged in).

1. Go to https://github.com/settings/personal-access-tokens/new
2. Fill in:
   - **Token name**: anything (e.g. "FC Discussions Reader")
   - **Expiration**: choose an appropriate lifetime
   - **Repository access**: select **Only select repositories** and pick your target repo
3. Under **Permissions > Repository permissions**, set **Discussions** to **Read-only**
4. Click **Generate token** and copy it (`GH_READ_TOKEN`)

## Secrets

The server loads secrets from environment variables if set, otherwise from [Google Cloud Secret Manager](https://cloud.google.com/secret-manager). This means local dev uses env vars and production uses Secret Manager — same code, no config files with real secrets.

### Storing secrets in Secret Manager (production)

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

## Local Development

Set the secrets as environment variables and run the server:

```bash
cd appengine
export GH_CLIENT_ID=your_client_id
export GH_CLIENT_SECRET=your_client_secret
export GH_READ_TOKEN=your_read_token
export GH_REPO_OWNER=your_repo_owner
export GH_REPO_NAME=formal-conjectures
export ALLOWED_ORIGIN=http://localhost:8000
node server.js
```

Then serve the site in another terminal:

```bash
cd site/site
python3 -m http.server 8000
```

The proxy runs on `http://localhost:8080`. The site on `http://localhost:8000`.

## Deploy

Edit `app.yaml` to set `ALLOWED_ORIGIN`, `GH_REPO_OWNER`, and `GH_REPO_NAME` for your deployment, then:

```bash
gcloud app deploy
```

Secrets are loaded from Secret Manager automatically at startup.

Your service will be available at `https://PROJECT_ID.REGION_ID.r.appspot.com`.

## API Endpoints

- `POST /token` — OAuth code exchange
- `GET /discussions` — aggregated discussion data (cached 60s)

## Configuration

| Variable | Source | Description |
|---|---|---|
| `ALLOWED_ORIGIN` | `app.yaml` / env | CORS allowed origin(s), comma-separated |
| `GH_REPO_OWNER` | `app.yaml` / env | GitHub repo owner |
| `GH_REPO_NAME` | `app.yaml` / env | GitHub repo name |
| `GH_CLIENT_ID` | Secret Manager / env | GitHub App client ID |
| `GH_CLIENT_SECRET` | Secret Manager / env | GitHub App client secret |
| `GH_READ_TOKEN` | Secret Manager / env | Fine-grained PAT for anonymous reads |

## Cost

App Engine standard F1 instances include 28 free instance hours/day. With `max_instances: 1` in `app.yaml`, this proxy stays well within the free tier for typical usage.
