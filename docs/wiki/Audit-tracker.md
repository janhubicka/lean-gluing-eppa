# Audit tracker — Gluing EPPA Lean library

**15 October 2026:** The finite relational EPPA and full ordinary/coherent
complete-overlap sparsening proofs are checked. Their source is preserved in
[the library](https://github.com/janhubicka/lean-gluing-eppa).
The live [GitHub Wiki](https://github.com/janhubicka/lean-gluing-eppa/wiki)
is synchronized from this repository's `docs/wiki/`.
This tracker distinguishes completed Lean checks, code cleanup, and
outstanding **independent mathematical** review.

## Main theorem certification

| Item | Validation |
| --- | --- |
| Unconditional finite relational EPPA | `GluingEPPA.finite_relational_eppa_private` |
| Ordinary complete-overlap sparsening | `GluingEPPA.Sparsening.OrbitAtlas.sparsening_eppa` |
| Coherent complete-overlap sparsening | `GluingEPPA.Sparsening.OrbitAtlas.coherent_sparsening_eppa` |
| Fixed-language statement crosswalk | [Published statements](Published-statements.md) |
| Final theorem CI | [PR run 38738905840](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38738905840), [merged-main run 38739744079](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38739744079) |

The original checked source is
[`136bd0f5f47209f090ea4e284a8c6a4c9386d795`](https://github.com/janhubicka/lean-gluing-eppa/commit/136bd0f5f47209f090ea4e284a8c6a4c9386d795).
Four exact-name manifests cover **331 declarations**:
281 + 21 + 12 + 17. The only transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The three independent finite
regression *programs* are supplementary checks, not substitutes for
formal proof or external mathematical refereeing.

## Cleanup and publication milestones

| PR | Result | Status |
| --- | --- | --- |
| [#58](https://github.com/janhubicka/lean-gluing-eppa/pull/58) | Eleven-page research wiki, publisher, documentation and import-DAG checks; 88 redundant direct umbrella imports reduced to six without losing any of the 88 modules | Merged; build, 331 axiom checks, regressions, and documentation checks passed |
| [#59](https://github.com/janhubicka/lean-gluing-eppa/pull/59) | Removed deprecated/no-op tactics in two files | Merged; CI passed |
| [#60](https://github.com/janhubicka/lean-gluing-eppa/pull/60) | Replaced deprecated tactic names and the retired Mathlib finite-sum import in eight files | Merged; CI passed |
| [#61](https://github.com/janhubicka/lean-gluing-eppa/pull/61) | Recorded the real GitHub Wiki publication | Merged |
| [#62](https://github.com/janhubicka/lean-gluing-eppa/pull/62) | Pinned Wiki publishing actions; removed direct-Wiki-edit trigger; disclosed force-push behavior | Merged |

[Wiki run 38766957545](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38766957545)
pushed all original eleven pages as Wiki commit `55a5fab`.
The publishing action's log includes `git push -f origin master`;
**edits only in the Wiki UI may be overwritten**. Update `docs/wiki/`
through reviewed PRs instead.

## Compiler warnings (run-specific snapshot)

The earlier main build reported **108 warnings**. The checked
[PR #60 build](https://github.com/janhubicka/lean-gluing-eppa/actions/runs/38767430841)
reported **95 warnings and 23 hints**, while retaining all 331
axiom checks and three regression suites. In that latter build:

| Warning type | Count of warning headings |
| --- | ---: |
| Automatically included unused section variables | 29 |
| Tactic optimizer suggestions | 27 |
| Unused `simp` arguments | 10 |
| Unused named arguments | 7 |
| Remaining deprecated API/tactic warnings | 6 |
| Tactic-sequencing hints | 4 |
| Module-system import warnings | 2 |
| Instance reducibility warning | 1 |
| Other warnings | 2 |

The build summary counts `warning:` messages differently from this
grouping, which counts *headings*. Incremental compilation and cache
reuse may change the warning total: **95 is not a future CI ceiling**.
Do not silence unused section-variable warnings without first checking
whether the exported theorem type becomes more general.

## Why some alternatives remain

`FiniteEPPA`, `UnorderedFiniteEPPA` and `PrivateFiniteEPPA`
prove distinct useful ordinary-EPPA constructions. They are not merely
compatibility wrappers. Likewise, the terminal modules
`Sparsening.Saturated` and `Sparsening.Descent` provide independent
generic saturation/descent results. They are not prerequisites of the
final complete-overlap theorem but remain directly importable and
axiom-audited. Removing them would require a separate downstream
usage review and manifest adjustment.

`PartialFamily.coherentBase` provides only **inverse-compatible**
padding; it is not coherent EPPA. True coherent extension families
are formalized in `OrbitExtensionFamily`.

## Open research-quality checks

1. **Independent referee review:** check correspondence of the Lean
   definitions and all theorem assumptions to the published theorem.
   The adversarial passes so far are self-audits.
2. **Small proof-code hygiene PRs:** address genuine unused `simp`
   arguments and deprecated interfaces; avoid changing theorem
   hypotheses casually.
3. **Downstream consumption test:** in another compatible Lake project,
   import both the umbrella and several narrow modules.
4. **Future mathematics:** symbol-permuting automorphisms and induced
   local-tree embeddings are not part of the verified claims.

## Reproduce the checks

~~~sh
lake update
lake exe cache get
lake build
for manifest in scripts/Check*Axioms.lean; do
  lake env lean "$manifest" > axioms.log
  python3 scripts/check-axiom-log.py axioms.log "$manifest"
done
python3 scripts/check_saturated_cover.py --exhaustive
python3 scripts/check_atlas_action.py
python3 scripts/check_orbit_atlas.py
python3 scripts/audit_library_imports.py
python3 scripts/check_wiki_docs.py
~~~
