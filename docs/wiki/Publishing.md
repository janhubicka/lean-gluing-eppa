# Publishing the research wiki

The authoritative wiki source is
[`docs/wiki/`](https://github.com/janhubicka/lean-gluing-eppa/tree/main/docs/wiki).
Its front page is `README.md`, which the synchronized GitHub Wiki
displays as **Home**. `_Sidebar.md` gives the navigation.

**Important:** GitHub Wikis are stored in a separate
`lean-gluing-eppa.wiki.git` repository. Merely merging
`docs/wiki/*.md` does **not** automatically create a
GitHub Wiki tab page.

## Current publication status (15 October 2026)

**Published and synchronizing.** The separate `lean-gluing-eppa.wiki.git`
repository is initialized. [Actions run 38766957545](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38766957545)
cloned it, generated `Home.md` and `_Sidebar.md`, and pushed Wiki commit
`55a5fab` to its `master` branch. Its *Sync source pages to GitHub Wiki tab*
step completed successfully. The [live wiki](https://github.com/janhubicka/lean-gluing-eppa/wiki)
now contains all eleven pages. No manual first-page initialization remains
necessary for this repository. The bootstrap instructions below apply to
fresh forks or copies whose Wiki storage has never been created.

## Automatic synchronization

The repository carries
[`.github/workflows/publish-wiki.yml`](../../.github/workflows/publish-wiki.yml),
modeled on the successfully published lean-milliken wiki.
Its triggers are:

- `push` on `main` modifying `docs/wiki/**` or its workflow;
- `workflow_dispatch` for manual re-synchronization.

First it checks whether the remote `owner/repo.wiki.git`
actually exists. Only if that succeeds does it run
`Andrew-Chen-Wang/github-wiki-action@v5` at an **immutable commit**
with `preprocess: true` and `strategy: clone`.
**Its actual run uses `git push -f origin master`.** This is intentional:
`docs/wiki/` is the single source of truth, but it means manual changes
made only in the Wiki tab may be overwritten. Review Wiki edits in the
code repository instead. The action revision and checkout revision are
pinned to immutable commits in the workflow.

### If the Wiki has never had a Home page

There is a one-time prerequisite that a GitHub action
cannot bypass merely by pushing `docs/wiki` to `main`:

1. Open [the project's GitHub Wiki](https://github.com/janhubicka/lean-gluing-eppa/wiki)
   while signed in with edit permission.
2. Click **Create the first page**, title it **Home**, enter
   a short temporary sentence, and save.
3. Open [Publish wiki workflow](https://github.com/janhubicka/lean-gluing-eppa/actions/workflows/publish-wiki.yml),
   choose **Run workflow** on `main`, and run it once to populate the new
   Wiki repository. This is required on a fresh fork.

The first page initializes the separate Wiki Git
repository. Subsequent publication is automatic from
the source-controlled Markdown. A direct edit in the
GitHub Wiki may be overwritten by the next synchronization.

## How to check publication

The wiki publishing workflow must reach
**Sync source documentation to the GitHub Wiki tab**
with a successful result. Its earlier
**Check whether the Wiki Git repository exists** step
being green alone is insufficient: it may merely
have recorded `initialized=false` and skipped
the actual publication.

When this page is linked from the main README,
the source-controlled version remains readable even if
the separate Wiki is not yet initialized.
Do not describe the GitHub Wiki as live until its
publisher has actually pushed a Git commit.

## Maintenance

Update the Markdown in `docs/wiki` via a normal
reviewable PR. This preserves source history and
lets the Lean CI audit its local links. Keep
human-readable statements application-neutral and
pin all declarations to an actually checked source
revision. A future API cleanup should edit the
crosswalk and update known downstream clients rather
than keeping obsolete wrappers forever.
