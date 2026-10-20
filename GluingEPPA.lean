import GluingEPPA.FiniteEPPA
import GluingEPPA.UnorderedFiniteEPPA
import GluingEPPA.PrivateFiniteEPPA
import GluingEPPA.Sparsening.Saturated
import GluingEPPA.Sparsening.Descent
import GluingEPPA.Sparsening.SparseningTheorem
import GluingEPPA.Steiner.LiftedTriples

/-!
# The Gluing EPPA library

This public umbrella imports the terminal local modules. Use a narrower import
when possible. The complete public import closure is checked in CI by
`scripts/audit_library_imports.py`.

The `Steiner` modules validate parts of the recursive construction in the
separate paper `steiner_eppa.tex`; they do not yet export its final EPPA theorem.
-/
