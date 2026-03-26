#!/usr/bin/env node
/**
 * create_discussions.js — Pre-create GitHub Discussions for conjectures.
 *
 * Reads the processed conjectures JSON, compares against existing discussions,
 * and creates a Discussion for each conjecture that doesn't have one yet.
 *
 * Usage:
 *   GITHUB_TOKEN=<token> node create_discussions.js <owner> <repo>
 *
 * The token needs Discussions read+write permission. In GitHub Actions, use
 * the built-in GITHUB_TOKEN with `discussions: write` in the workflow
 * permissions block:
 *
 *   permissions:
 *     discussions: write
 *
 * Then pass it as:
 *   env:
 *     GITHUB_TOKEN: ${{ github.token }}
 */

'use strict';

const CATEGORY_NAME = 'Problems';

async function graphql(query, variables, token) {
  const resp = await fetch('https://api.github.com/graphql', {
    method: 'POST',
    headers: {
      Authorization: `Bearer ${token}`,
      'Content-Type': 'application/json',
      'User-Agent': 'fc-create-discussions',
    },
    body: JSON.stringify({ query, variables }),
  });
  if (!resp.ok) {
    const text = await resp.text();
    throw new Error(`GraphQL ${resp.status}: ${text}`);
  }
  const json = await resp.json();
  if (json.errors) throw new Error(json.errors[0].message);
  return json.data;
}

async function getRepoId(owner, repo, token) {
  const data = await graphql(`
    query($owner: String!, $repo: String!) {
      repository(owner: $owner, name: $repo) { id }
    }
  `, { owner, repo }, token);
  return data.repository.id;
}

async function getCategoryId(owner, repo, token) {
  const data = await graphql(`
    query($owner: String!, $repo: String!) {
      repository(owner: $owner, name: $repo) {
        discussionCategories(first: 25) {
          nodes { id name }
        }
      }
    }
  `, { owner, repo }, token);
  const match = data.repository.discussionCategories.nodes.find(
    c => c.name === CATEGORY_NAME
  );
  if (!match) {
    throw new Error(
      `Discussion category "${CATEGORY_NAME}" not found. ` +
      `Create it in the repository settings under Discussions.`
    );
  }
  return match.id;
}

async function getExistingDiscussionTitles(owner, repo, token) {
  const titles = new Set();
  let hasNextPage = true;
  let after = null;

  while (hasNextPage) {
    const data = await graphql(`
      query($owner: String!, $repo: String!, $after: String) {
        repository(owner: $owner, name: $repo) {
          discussions(first: 100, after: $after) {
            pageInfo { hasNextPage endCursor }
            nodes { title }
          }
        }
      }
    `, { owner, repo, after }, token);

    for (const d of data.repository.discussions.nodes) {
      titles.add(d.title);
    }
    hasNextPage = data.repository.discussions.pageInfo.hasNextPage;
    after = data.repository.discussions.pageInfo.endCursor;
  }

  return titles;
}

async function createDiscussion(repoId, categoryId, title, body, token) {
  await graphql(`
    mutation($repoId: ID!, $categoryId: ID!, $title: String!, $body: String!) {
      createDiscussion(input: {
        repositoryId: $repoId,
        categoryId: $categoryId,
        title: $title,
        body: $body
      }) {
        discussion { number }
      }
    }
  `, { repoId, categoryId, title, body }, token);
}

async function main() {
  const token = process.env.GITHUB_TOKEN;
  if (!token) {
    console.error('GITHUB_TOKEN environment variable is required.');
    process.exit(1);
  }

  const [owner, repo] = process.argv.slice(2);
  if (!owner || !repo) {
    console.error('Usage: GITHUB_TOKEN=<token> node create_discussions.js <owner> <repo>');
    process.exit(1);
  }

  // Load conjectures
  const fs = require('fs');
  const dataPath = require('path').join(__dirname, 'data', 'conjectures.json');
  if (!fs.existsSync(dataPath)) {
    console.error(`Data file not found: ${dataPath}`);
    process.exit(1);
  }
  const raw = JSON.parse(fs.readFileSync(dataPath, 'utf8'));
  const conjectures = raw.conjectures || raw.problems || raw;
  if (!Array.isArray(conjectures) || conjectures.length === 0) {
    console.error('No conjectures found in data file.');
    process.exit(1);
  }

  console.log(`Loaded ${conjectures.length} conjectures.`);

  // Get repo metadata
  const [repoId, categoryId, existing] = await Promise.all([
    getRepoId(owner, repo, token),
    getCategoryId(owner, repo, token),
    getExistingDiscussionTitles(owner, repo, token),
  ]);

  console.log(`Found ${existing.size} existing discussions.`);

  // Find missing discussions
  const theoremNames = conjectures.map(c => c.theorem);
  const missing = theoremNames.filter(name => !existing.has(name));
  console.log(`${missing.length} discussions to create.`);

  if (missing.length === 0) {
    console.log('All discussions already exist.');
    return;
  }

  // Create missing discussions with rate limiting.
  // GitHub's secondary rate limit for mutations requires a delay between each.
  // After hitting the limit, we do a long cooldown before resuming.
  const DELAY_MS = 2000;
  const COOLDOWN_MS = 120000; // 2 minutes after a rate limit hit
  let created = 0;
  let errors = 0;
  for (const name of missing) {
    const shortName = name.split('.').pop();
    const body = `Discussion for theorem **${shortName}**.\n\nFull Lean name: \`${name}\``;
    let success = false;
    while (!success) {
      try {
        await createDiscussion(repoId, categoryId, name, body, token);
        created++;
        success = true;
        if (created % 50 === 0) {
          console.log(`  Created ${created}/${missing.length}...`);
        }
      } catch (e) {
        if (e.message.includes('too quickly') || e.message.includes('rate limit') || e.message.includes('abuse')) {
          console.log(`  Rate limited at ${created}/${missing.length}, cooling down ${COOLDOWN_MS / 1000}s...`);
          await new Promise(r => setTimeout(r, COOLDOWN_MS));
        } else {
          console.error(`  Failed to create discussion for ${name}: ${e.message}`);
          errors++;
          break;
        }
      }
    }
    // Delay between every creation to stay under secondary rate limits
    await new Promise(r => setTimeout(r, DELAY_MS));
  }

  console.log(`Done. Created ${created}, errors ${errors}, total ${existing.size + created}.`);
}

main();
