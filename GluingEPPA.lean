import GluingEPPA.FiniteEPPA
import GluingEPPA.UnorderedFiniteEPPA
import GluingEPPA.PrivateFiniteEPPA
import GluingEPPA.Sparsening.Saturated
import GluingEPPA.Sparsening.Descent
import GluingEPPA.Sparsening.SparseningTheorem
import GluingEPPA.Steiner.DiagramUniformExtension

/-!
# The Gluing EPPA library

This public umbrella imports the terminal local modules of each construction.
Earlier versions listed every module by name, adding no semantics but
obscuring the actual dependency structure.

Use a narrower import when possible (for example
`GluingEPPA.Sparsening.TreeHomEmbedding` for locally exact maps or
`GluingEPPA.Sparsening.SparseningTheorem` for the two final theorems).
The import graph and its complete public closure are checked in CI
by `scripts/audit_library_imports.py`.
-/
