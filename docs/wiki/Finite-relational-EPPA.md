# Finite relational EPPA via gluing diagrams

The ordinary EPPA part of the library is usable independently of the
sparsening theorem. It constructs a finite induced witness for all
partial automorphisms of an arbitrary finite structure in a fixed,
finite **relational** language, including empty partial maps, nullary
predicates and tuples with repeated coordinates.

The principal exported result is
`GluingEPPA.finite_relational_eppa_private` in
[`PrivateFiniteEPPA.lean`](../../GluingEPPA/PrivateFiniteEPPA.lean).
The simpler predecessor results
`finite_relational_eppa` and
`finite_relational_eppa_unordered`
remain available for users studying the intermediate constructions.

## The gluing ingredients

1. A partial automorphism is a partial bijection preserving and
   reflecting the induced relational structure.
   `RelPartialAut` provides the finite family of all such maps.
2. The maps form labels on an inverse-compatible finite permutation
   diagram. On a padded carrier, each label has a total permutation.
   The graph of each total permutation encodes transport of the
   corresponding partial map. The inverses are controlled explicitly.
3. For each relevant edge of the diagram, assign a Boolean valuation
   coordinate. Take a chart copy for each valuation and glue chart
   occurrences according to the labelled permutation edges.
4. Relation tuples are *contributed by a single chart*. This guarantees
   that the original root chart is induced: one cannot create a new
   relation tuple on old vertices merely by identifying unrelated
   chart occurrences.
5. For the compact private-marker version, use marked transpositions
   and three-cycles. These make the label permutations identifiable
   and prevent inverse pairs from collapsing into unintended
   repetitions.

The three checked routes have different presentation costs. The
oriented occurrence-indexed cover is the more direct presentation.
The unordered-edge cover more closely matches the written
Boolean gluing argument. Private two-/three-cycle markers give the
preferred final relational theorem with the compact padded carrier.

## Modules and useful declarations

| Module | Checked role |
| --- | --- |
| `Relational`, `RelPartialAut` | Relations of arbitrary arity, all induced partial isomorphisms |
| `PermutationDiagram`, `PartialFamily` | Inverse-compatible labelled finite permutation family |
| `OrientedCover`, `OrientedAssembly` | The oriented Boolean cover and contributed relations |
| `UnorderedEdges`, `UnorderedCover`, `UnorderedAssembly` | Unordered edge coordinates and full quotient |
| `PrivateCycles`, `PrivateCycleInjection` | Two-/three-cycle marker actions and nonidentity |
| `PaddedPrivateFamily` | Uniform private permutation extension |
| `FiniteEPPA`, `UnorderedFiniteEPPA`, `PrivateFiniteEPPA` | Three unconditional ordinary-EPPA endpoints |

For orientation:

~~~lean
import GluingEPPA

#check GluingEPPA.finite_relational_eppa
#check GluingEPPA.finite_relational_eppa_unordered
#check GluingEPPA.finite_relational_eppa_private
#check GluingEPPA.RelPartialAut
~~~

## Distinguish inverse compatibility from coherence

The ordinary construction chooses total permutations such that partial
maps and their inverses are respected. A partial-map family may have
different compositions even when all pairwise inverses work.
Therefore this **does not** prove the coherent EPPA property.
The coherent sparsening theorem has a **coherent EPPA-witness as an
input** and preserves its chosen composition equations.
Do not label `PartialFamily.coherentBase` as the latter: its name
historically refers to inverse-compatible base choices.

## Bounds and scope

The padded private carrier has an explicitly verified bound of
`|A| + 2|I|`, where `I` is its inverse-indexed label set.
Sharper pruning to the `2s+3t` marker count is not independently
formalized. These bounds concern the initial permutation carrier;
they are not a claim of a practical bound on the size of the
iterated sparsening witness.

The language is fixed: the checked theorems do **not** allow
partial automorphisms to permute relation symbols.
Nullary relations keep their truth value whenever a root copy is
present; repeated coordinates are never silently excluded.

The [sparsening construction](Sparsening-construction.md) starts
from an existing finite EPPA-witness and proves strictly more
geometric conclusions without re-proving this initial relational
theorem.
