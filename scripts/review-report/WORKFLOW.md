# Opt-in Actions preparation

The workflow prepares review inputs using the installed toolkit. Maintainers must
accept its prerequisites and configure it before activation. It uses trusted
default-branch code; candidate PRs cannot supply the workflow or build recipe.

A contributor with current write, maintain, or admin permission can request a run
with an exact `/review` comment. The controller freezes the PR revisions, collects
cited sources, and builds in a fresh isolated container. It retains a draft and
inputs as Actions artifacts for 30 days. Missing sources or unavailable builds
remain incomplete. Failed builds remain failures.

An existing agent or human session conducts the semantic review. This workflow
has no AI credentials, model generation, or publication job. Download and replay
the retained run through `conjectures review prepare --input DIR`, then follow its
printed procedure and finish command. Publication is a separate explicit operation.

## Maintainer configuration

1. Build the environment using `conjectures setup review` from an accepted toolkit
   revision. Its bundled production recipe verifies the upstream source and Lean
   archive, then records the resulting image digest. It needs no evaluation cache.
2. Push that reviewed image through the operator's normal registry process. Set
   `FC_REVIEW_IMAGE` to its public registry digest. Target dependency drift is
   checked before every build; candidate files cannot choose another image.
3. Exercise preparation on a disposable mathematical PR, then explicitly enable
   `FC_REVIEW_ENABLED=true` only after maintainer acceptance.

Preparation supports at most five new or modified problem modules. Broader,
configuration, shared utility, and deleted-file changes require ordinary review.
The source collector fetches bounded directly cited pages, not recursive browsing.
The workflow retains operational evidence; it does not decide mathematical
acceptance, verify external proofs, or measure semantic review accuracy.

An artifact is temporary retention. Durable publication uses `conjectures evidence
publish RUN`, with an inspected public export and an existing evidence destination.
See [the toolkit guide](../../toolkit/README.md) and FC #4394 for the delivery order.
