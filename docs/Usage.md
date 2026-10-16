# Using the interfaces

[Back to the overview and build instructions](../README.md#use-and-verification).

### Imports and interfaces

Import `GroupTheory` for these results, or import
`GroupTheory.Topology.OpenQuotient`,
`GroupTheory.Topology.ConnectedComponentQuotient`,
`GroupTheory.Topology.ConnectedComponentOpenSubgroup`,
`GroupTheory.Topology.Sections`, `GroupTheory.CyclicNorm` or
`GroupTheory.FGScalarSurjectivity`, `GroupTheory.Topology.CompactOpenSubgroup`,
`GroupTheory.Topology.OpenKernel` or `GroupTheory.Topology.CircleCharacter`
individually. The finite-index results are also available through
`GroupTheory.Topology.FiniteIndex`; the open/closed/clopen subgroup and left-coset
statements through `GroupTheory.Topology.Algebra.Group.Quotient`; and character subgroups through
`GroupTheory.Topology.CharacterSubgroups`. The rational-circle inclusion and
character comparisons are available through `GroupTheory.Topology.RationalCircle`
and `GroupTheory.Topology.RationalCircleCharacter`. The compact/discrete map
results are available through `GroupTheory.Topology.ContinuousMap.CompactDiscrete`
and `GroupTheory.Topology.Algebra.CompactGroup.DiscreteFactor`.
Import `GroupTheory.Topology.Algebra.OpenSubgroup.Pi` for finite-cylinder
containment, or `GroupTheory.Topology.Algebra.CompactGroup.PiDiscreteFactor`
for finite-coordinate map factorization. Import
`GroupTheory.Topology.Algebra.Group.PiDiscreteFactor` for the homomorphism
projection and descent APIs; all are re-exported by `GroupTheory`.
For a discrete-group-valued homomorphism `f : (∀ i, G i) →ₜ* H`, use
`obtain ⟨s, N, fbar, hfactor, hquot, hstage⟩ :=
ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor f`.
Here `hfactor` is a bundled homomorphism equality, and `hquot` and `hstage`
give intrinsic quotient and stage discreteness. With compact factors, the
`_finite` theorem returns coordinate finiteness and product finiteness instead.
Use `letI := ContinuousMap.discreteTopology_of_compactSpace (X := X) (Y := Y)`
when a local map-space discreteness instance is needed, or obtain the quotient
map with `obtain ⟨N, fbar, hfactor⟩ := f.exists_openNormalSubgroup_factor`.
For `f : C(I → G, Y)`, use
`obtain ⟨s, N, fbar, hfactor⟩ := f.exists_finset_openNormalSubgroup_pi_factor`;
`hfactor x` identifies `f x` with evaluation of `fbar` on the selected quotient
coordinates. For an open normal subgroup `M` of a dependent product, use
`obtain ⟨s, N, hsubset⟩ := M.exists_finset_pi_subset`; for a constant family,
use `obtain ⟨s, N, hsubset⟩ := M.exists_finset_uniform_pi_subset`.
For example, after
`import GroupTheory`, use `MonCat.sectionsLift F q hq` to bundle a compatible
continuous family and `MonCat.sectionsπ_comp_sectionsLift F q hq j` to recover
its `j`th component; use
`QuotientGroup.connectedComponentQuotientLift_mk_apply f x` to recover `f x`;
use `Topology.IsOpenQuotientMap.totallyDisconnectedSpace hf` for an open
quotient map `hf` between compact Hausdorff totally disconnected and Hausdorff
spaces;
use `AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm hperiod hinjective hlift`
or `(AddCommGroup.nsmul_surjective_iff_finite_coprime (A := A) (n := n) hn).mp hsurj`.
The maintained `GroupTheoryTest` root exercises the interfaces but is not
required by downstream imports. Its sections clients include empty indexing,
parallel arrows, non-group stages, discontinuous transitions, nonsurjective
projections and a nontrivial consequence of `sections_topology`. The cyclic
clients cover fixed-class lifting, the coordinate swap on `ℤ × ℤ` and
counterexamples when hypotheses are dropped; the scalar clients include
concrete `ZMod` examples. The quotient clients cover connected real, discrete,
indiscrete non-Hausdorff and mixed connected/discrete groups. The compact/discrete
clients exhibit distinct Boolean values, isolated maps and continuous observers;
they derive right invariance and separation of quotient points from factorization.
The power clients use a Boolean observer that depends on both coordinates and
cannot be a homomorphism for any group structure on `Bool`. They also exhibit
a nonconstant observer with infinite index and infinite discrete target,
finite/discrete selected stages, empty indices and targets, and an explicit
empty-coordinate factorization of a constant map. The homomorphism clients
include two essential coordinates with proper nontrivial kernels, heterogeneous
factors, arbitrary topologies on ignored factors, noninjective descent,
infinite discrete targets and a surjective integer observer that rules out
finite stages. Empty and trivial cases and a closed nonopen real normal
subgroup test the boundaries of the canonical projection.

### Action automorphisms

Import `GroupTheory.GroupAction.Centralizer` (or `GroupTheory`). For an action
`A` in a category, use `Action.autEquivCentralizer A α` to obtain its underlying
automorphism as a centralizer element, or `(Action.autEquivCentralizer A).symm f`
to equip a commuting isomorphism with equivariance. The lemmas
`Action.coe_autEquivCentralizer` and `Action.mapIso_autEquivCentralizer_symm`
characterize both forgetful maps.

For `[Group G] [MulAction G X]`, use `Action.autEquivPermCentralizer G X` for
permutations instead. Its `_apply`, `_apply_symm`, `_symm_hom_apply` and
`_symm_inv_apply` lemmas are simp lemmas for the four coordinates. Use
`Action.autEquivPermCentralizer_eq_iff` to prove equality with a supplied
centralizer member by evaluation. Stock `map_mul`, `map_one` and `map_inv`
apply directly to both multiplicative equivalences. The `_mul_apply` lemma
makes the order `α.hom.hom (β.hom.hom x)` explicit. No unfolding of the
constructors or choice of an element of `X` is needed.

### Compatibility

Older Profinite Groups versions that also define
`Topology.IsOpenQuotientMap.totallyDisconnectedSpace` cannot share an import
graph with `GroupTheory.Topology.OpenQuotient` or the aggregate `GroupTheory`
import. Removing that duplicate prevents the collision. Preserving that Profinite
Groups API also requires re-exporting Group Theory's canonical declaration.

Continuous Group Cohomology versions that define
`ContinuousMap.discreteTopology_of_compactSpace` and
`ContinuousMap.exists_openNormalSubgroup_factor` cannot share an import graph
with these Group Theory modules or the aggregate `GroupTheory` import.
Compatible versions must re-export the Group Theory declarations rather than
defining them again.
