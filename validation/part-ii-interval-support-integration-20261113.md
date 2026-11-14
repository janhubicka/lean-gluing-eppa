# Checked-source interval support integration, 13 November 2026

Copied fourteen Lean modules without editing their contents from the
previously green historical interval proof stack at commit `0fe94a50184acf0262569cefc411f9fd20ff1bfa`.
Run 42487170477 compiled that exact head and passed the named axiom audit.
This branch revalidates the source against the newer merged Part II baseline
`f4ff224352b7bc72deead7dd60d8aa655c39c302`. It is a candidate until *this* branch's CI succeeds.

The original finite separated `LinkChain.buildNonempty` has a covering
history of historical Cayley blocks. The theorem
`LinkChain.buildNonempty_has_consecutive_history` establishes that every
actual M-component has a consecutive block support interval. A last-block
chart and correct old/new root support transitions are included.

It remains necessary to relate that family to the exact boundary-parameter
history and to assemble the unique middle shifts into an edge- and
fixed-point-reflecting normalized smaller-chain quotient. The fact that
support is consecutive does NOT establish the global normalized M-component
isomorphism or the augmented-recursion construction.

No manuscript or Part I files are modified. No axioms or admissions are added.
