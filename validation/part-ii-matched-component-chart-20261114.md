# Exact matched-component chart assembly, 14 November 2026

This separate generic lemma package takes the actual matched restriction
of an injective two-block Link/pushout and three commuting *bijective*
coordinate charts (old piece, new piece, and the WHOLE interface). It
combines them into an equivalence from the smaller exact pushout to the
entire actual M-connected component. Coverage is discharged by the
previously compiled matched-component theorem, not by a new assumption.

Sources: `PushoutEquiv.lean` and `MatchedComponentChartExtension.lean`
were retrieved from the earlier PR #152 branch. That exact-head workflow
had one error in the latter at line 78: an injectivity proof expected
`v = w`, but passed only `(G v).val = (G w).val`.
The revised proof uses `Subtype.ext (congrArg Subtype.val hvw)`.
The **new branch is not compiled** until exact-head CI passes.

This does not construct concrete finite-history normalized charts, nor
does an arbitrary equivalence automatically preserve and reflect
completed M-letter transitions. These remain proof obligations of
the manuscript's `lem:chain-restriction`.

No Part I or manuscript files are modified.
