# Group Theory

Reusable Lean results on identity-component quotients of topological groups,
compact open subgroups of totally disconnected locally compact groups,
open kernels and finite images of continuous group homomorphisms,
compact-open discreteness and finite-quotient factorization of discrete-valued maps,
finite-coordinate quotient factorization on arbitrary powers of compact groups,
finite-image and open-kernel rational-circle character subgroups,
the rational-circle inclusion and comparison with continuous circle characters,
open finite-index subgroups of compact commutative groups with dense finite generation,
continuous compatible sections of monoid diagrams, open quotients of compact
totally disconnected spaces, finite cyclic norms and natural scalar maps of
finitely generated abelian groups.
The library depends directly on mathlib, not on a source repository or the
incubator. The mathematical guides explain the proof ideas, examples and limits
in more detail.

## Headline results

**Compact open subgroup neighborhoods.** Every identity neighborhood in a
locally compact totally disconnected topological group contains a compact open
subgroup; neighborhoods need not be open, and no ambient compactness or separate
Hausdorff hypothesis is imposed. `OpenSubgroup.nhds_one_hasBasis_compact` expresses
the neighborhood basis. For any compact open set, `OpenSubgroup.leftStabilizer`
constructs its open left-translation stabilizer, even if the set misses the identity.
When the set contains the identity, that subgroup is compact and contained in the set.
The construction requires neither local compactness nor total disconnectedness.
See [the subgroup API](GroupTheory/Topology/CompactOpenSubgroup.lean)
and [the boundary clients](GroupTheoryTest/Topology/CompactOpenSubgroup.lean).

**Open kernels and finite images.** For a continuous homomorphism from a
nonarchimedean group, a target identity neighborhood containing no nontrivial
subgroup forces an open kernel, without source compactness, commutativity or a
separation assumption on the target. An open kernel makes any group homomorphism
locally constant, even without continuity or a topology on the target.
Compactness of the source then gives finite image and a finite, discrete
quotient by the kernel; Mathlib's `QuotientGroup.kerLift` gives the unique
factorization, injective onto the image but not necessarily surjective onto
the target. The centered half-circle supplies the target neighborhood for
circle-valued characters, including those on compact locally compact totally
disconnected groups via the compact-open subgroup basis. See
[the general API](GroupTheory/Topology/OpenKernel.lean),
[the circle specialization](GroupTheory/Topology/CircleCharacter.lean) and
[a nonconstant two-element character](GroupTheoryTest/Topology/OpenKernel.lean).

**Rational-circle character subgroups.** A character of an abelian group has
finite image precisely when it has finite order as a whole character. For
topological abelian groups, characters with open kernels form a subgroup;
compactness makes every such character finite-order, without a Hausdorff
assumption. The converse holds for compact Hausdorff groups containing a dense
finitely generated subgroup, using openness of finite-index subgroups. Both
subgroups admit precomposition, with continuity required only for the
open-kernel restriction. See
[the character subgroup API](GroupTheory/Topology/CharacterSubgroups.lean)
and [the finite and 2-adic examples](GroupTheoryTest/Topology/CharacterSubgroups.lean).

**Rational-circle and continuous characters.** The rational additive circle embeds
in the unit circle, and every finite-order circle point has a rational preimage.
For a compact nonarchimedean commutative additive group, open-kernel
rational-circle characters identify additively with its continuous
circle-valued characters.
If the group is additionally Hausdorff and has a dense finitely generated
additive subgroup, its finite-order characters supply that domain. These
comparisons neither cover all abstract rational-circle characters nor give a
topological equivalence. See [the inclusion](GroupTheory/Topology/RationalCircle.lean),
[both comparison maps](GroupTheory/Topology/RationalCircleCharacter.lean) and
[the finite and 2-adic clients](GroupTheoryTest/Topology/RationalCircleCharacter.lean).

**Finite index from dense finite generation.** In a compact Hausdorff
commutative topological group with an abstractly finitely generated dense
subgroup, every positive-power range has finite index and is open. Every
abstract finite-index subgroup is therefore open, without assuming that it is
closed. Additive versions use positive natural-number scalar maps. The dense
integer subgroup of the 2-adic integers witnesses doubling with finite-index
open range and a proper finite-index reduction kernel; the zero scalar map
has infinite-index range. See [the subgroup results](GroupTheory/Topology/FiniteIndex.lean)
and [the 2-adic examples](GroupTheoryTest/Topology/FiniteIndex.lean).

**Open quotients of compact spaces.** If `f : X → Y` is an open quotient map,
`X` is compact, Hausdorff and totally disconnected, and `Y` is Hausdorff,
`Topology.IsOpenQuotientMap.totallyDisconnectedSpace` gives total
disconnectedness of `Y`. This is a general result about topological spaces,
independent of group structure. See [the theorem](GroupTheory/Topology/OpenQuotient.lean)
and [a non-injective finite projection](GroupTheoryTest/Topology/OpenQuotient.lean).

**Discrete-valued maps on compact spaces and groups.** For any compact space
`X` and discrete space `Y`, `ContinuousMap.discreteTopology_of_compactSpace`
gives discreteness of the existing compact-open topology on `C(X, Y)`.
For any compact topological group `G`, every `f : C(G, Y)` descends through
an open normal subgroup: `ContinuousMap.exists_openNormalSubgroup_factor`
gives `N : OpenNormalSubgroup G` and `fbar : C(G ⧸ N.toSubgroup, Y)` with
`∀ g, fbar (QuotientGroup.mk g) = f g`. Mathlib's open-subgroup quotient APIs
make this quotient finite and discrete. Neither theorem requires Hausdorffness
or nonemptiness of the spaces; factorization requires neither total
disconnectedness nor commutativity of `G`, and no algebraic structure on `Y`
or homomorphism condition on `f`. Discreteness is a theorem, not a new global
instance. See [the map-space theorem](GroupTheory/Topology/ContinuousMap/CompactDiscrete.lean),
[the group factorization](GroupTheory/Topology/Algebra/CompactGroup/DiscreteFactor.lean),
[isolated maps and observers](GroupTheoryTest/Topology/ContinuousMap/CompactDiscrete.lean)
and [right-invariance and separation clients](GroupTheoryTest/Topology/Algebra/CompactGroup/DiscreteFactor.lean).

**Finite-coordinate factorization on compact group powers.** For an arbitrary
index type `I`, compact topological group `G` and discrete space `Y`, every
`f : C(I → G, Y)` factors through finitely many quotient coordinates.
`ContinuousMap.exists_finset_openNormalSubgroup_pi_factor` gives
`s : Finset I`, one `N : OpenNormalSubgroup G` and
`fbar : C((s → G ⧸ N.toSubgroup), Y)` with the canonical triangle
`∀ x : I → G, fbar (fun i : s => QuotientGroup.mk (x i)) = f x`.
The topologies are the canonical product and group-quotient topologies.
It is the **selected finite stage** `s → G ⧸ N.toSubgroup`, not the full
quotient power over `I`, that is finite and discrete. The types `I`, `G` and
`Y` have independent universes, and neither `I` nor `Y` needs to be finite.
The selected set may be empty. No additional nonemptiness, Hausdorffness,
commutativity, total disconnectedness or profinite hypothesis is required;
`Y` needs no group structure and `f` need not be a homomorphism.

The supporting cylinder API is more general: for arbitrary `I` and a family
`A : I → Type*` with only `[∀ i, Group (A i)]` and
`[∀ i, TopologicalSpace (A i)]`, any
`M : OpenNormalSubgroup (∀ i, A i)` contains a finite cylinder.
`OpenNormalSubgroup.exists_finset_pi_subset M` gives `s : Finset I` and
`N : ∀ i : s, OpenNormalSubgroup (A i)` such that
`∀ x : (∀ i, A i), (∀ i : s, x i ∈ N i) → x ∈ M`.
For a constant family and `M : OpenNormalSubgroup (I → G)`,
`OpenNormalSubgroup.exists_finset_uniform_pi_subset M`
gives one `N : OpenNormalSubgroup G` with
`∀ x : I → G, (∀ i : s, x i ∈ N) → x ∈ M`.
Coordinates outside `s` are unrestricted. These two containment theorems
require neither continuity of group operations, compactness, separation nor
a finite index type. The factorization combines the existing unary theorem
with this finite-cylinder containment and continuous quotient descent.
See [the cylinder API](GroupTheory/Topology/Algebra/OpenSubgroup/Pi.lean),
[the power factorization](GroupTheory/Topology/Algebra/CompactGroup/PiDiscreteFactor.lean)
and [two-coordinate, infinite-index and empty-index clients](GroupTheoryTest/Topology/Algebra/CompactGroup/PiDiscreteFactor.lean).

**Locally compact identity components.** In a locally compact topological group,
the identity component is the intersection of **all** open subgroups, even
without a Hausdorff assumption; membership and point-separation lemmas make
this characterization usable. For a continuous open surjective group homomorphism
with locally compact source, the closure of its identity-component image is
the identity component of the target, without target separation or local
compactness assumptions. Openness and closure are essential; the printed
open-*normal* intersection is false in general. The image argument uses the
locally compact open-quotient theorem for totally disconnected groups, proved
by restricting to a compact open subgroup. See [the component theorems](GroupTheory/Topology/ConnectedComponentOpenSubgroup.lean),
[their boundary clients](GroupTheoryTest/Topology/ConnectedComponentOpenSubgroup.lean)
and [the open-quotient lemma](GroupTheory/Topology/OpenQuotient.lean).

**Identity-component quotients.** For any topological group, the ordinary
quotient by Mathlib's `Subgroup.connectedComponentOfOne` is Hausdorff and totally
disconnected, without a separation or local-compactness hypothesis on the
original group. `QuotientGroup.connectedComponentQuotientMk` is the canonical
continuous projection. `QuotientGroup.connectedComponentQuotientLift` factors
continuous homomorphisms into totally disconnected groups, with application,
composition, uniqueness and hom-equivalence APIs. The target group's
operations need not be continuous. See
[the quotient API](GroupTheory/Topology/ConnectedComponentQuotient.lean)
and [boundary examples](GroupTheoryTest/Topology/ConnectedComponentQuotient.lean).

**Continuous compatible sections.** For any category `J`, functor
`F : J ⥤ MonCat`, and topologies on its monoid stages, the existing Mathlib
compatible-sections subtype has continuous coordinate projections
`MonCat.sectionsπContinuousMonoidHom F j`. For any monoid `H` with an arbitrary
topology, `MonCat.sectionsLift` constructs a continuous monoid homomorphism
from a family of continuous homomorphisms `H →ₜ* F.obj j` compatible with
**every** arrow.
`MonCat.sectionsLift_unique` and `MonCat.sectionsHomEquiv` give its uniqueness
and the equivalence with compatible families. `MonCat.sections_topology`
identifies the sections topology as the initial topology: the infimum of the
topologies induced by all coordinate projections.
`GrpCat.sectionsπContinuousMonoidHom` extends
Mathlib's algebraic projection for group-valued diagrams. No continuity of
multiplication on `H` or the stages, or of the transition maps, is assumed;
filteredness, inhabitance, compactness, separation and surjectivity are likewise
unnecessary. This is a continuous-*monoid*-homomorphism API, not a TopCat limit
or topological-group structure assertion. See [the definitions and theorems](GroupTheory/Topology/Sections.lean)
and [boundary examples](GroupTheoryTest/Topology/Sections.lean).

**Finite cyclic norm exactness.**
[`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range`](GroupTheory/CyclicNorm.lean)
identifies `ker (∑ i ∈ Finset.range m, sigma ^ i)` with `range (1 - sigma)`
for an endomorphism `sigma` of any additive commutative group `A`. It requires
`m : ℕ` with `0 < m` and `sigma ^ m = 1` (not necessarily *exact* order `m`),
injectivity of multiplication by that **same** `m`, and an elementwise fixed
lift: if `sigma a - a ∈ m • A`, some `sigma`-fixed `z` satisfies
`a - z ∈ m • A`. This is useful when fixed classes modulo `m • A` have
fixed representatives even though multiplication by `m` is not surjective.
It does not assume divisibility or a global fixed-lift section, and does not
assert an unconditional Tate/cohomology theorem or source coverage. See the
[cyclic norm guide](GroupTheory/CyclicNorm/README.md) and its
[client examples and counterexamples](GroupTheoryTest/CyclicNorm.lean).

**Surjective natural scalars on FG abelian groups.** For `[AddCommGroup A]`,
`[AddGroup.FG A]` and `n : ℕ` with `2 ≤ n`, surjectivity of the
map `fun x : A => n • x` forces `Finite A` and
`Nat.Coprime n (Nat.card A)`. A *single* integer scalar is a two-sided
inverse for `n • ·` on every element; the finite-and-coprime condition
characterizes both surjectivity and bijectivity of that map. The four APIs in
[`GroupTheory.FGScalarSurjectivity`](GroupTheory/FGScalarSurjectivity.lean) are
`AddCommGroup.exists_zsmul_inverse_of_nsmul_surjective`,
`AddCommGroup.finite_coprime_of_nsmul_surjective`,
`AddCommGroup.nsmul_surjective_iff_finite_coprime` and
`AddCommGroup.nsmul_bijective_iff_finite_coprime`. These statements do not
apply to arbitrary surjective endomorphisms and do not formalize K-theory.
See the [FG scalar guide](GroupTheory/FGScalarSurjectivity/README.md) and its
[client examples](GroupTheoryTest/FGScalarSurjectivity.lean).

## Using the library

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "groupTheory"
git = "https://github.com/FormalFrontier/group-theory.git"
rev = "main"
```

GitHub `main` contains reviewed releases, not development commits. Lake resolves
that ref when you add or update the dependency; your `lake-manifest.json` keeps
that resolution until another update. Use the matching Lean and mathlib versions
listed below. For a fixed reproducible version, replace `main` with the full
commit of a published release. Dependencies from another Formal Frontier library
or the incubator use the GitHub URL and full published release commit, not moving
`main`, development commits or PR heads.

Import the full library with:

```lean
import GroupTheory
```

## Use and verification

### Imports and interfaces

Import `GroupTheory` for these results, or import
`GroupTheory.Topology.OpenQuotient`,
`GroupTheory.Topology.ConnectedComponentQuotient`,
`GroupTheory.Topology.ConnectedComponentOpenSubgroup`,
`GroupTheory.Topology.Sections`, `GroupTheory.CyclicNorm` or
`GroupTheory.FGScalarSurjectivity`, `GroupTheory.Topology.CompactOpenSubgroup`,
`GroupTheory.Topology.OpenKernel` or `GroupTheory.Topology.CircleCharacter`
individually. The finite-index results are also available through
`GroupTheory.Topology.FiniteIndex`, and character subgroups through
`GroupTheory.Topology.CharacterSubgroups`. The rational-circle inclusion and
character comparisons are available through `GroupTheory.Topology.RationalCircle`
and `GroupTheory.Topology.RationalCircleCharacter`. The compact/discrete map
results are available through `GroupTheory.Topology.ContinuousMap.CompactDiscrete`
and `GroupTheory.Topology.Algebra.CompactGroup.DiscreteFactor`.
Import `GroupTheory.Topology.Algebra.OpenSubgroup.Pi` for finite-cylinder
containment, or `GroupTheory.Topology.Algebra.CompactGroup.PiDiscreteFactor`
for finite-coordinate factorization; both APIs are re-exported by `GroupTheory`.
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
empty-coordinate factorization of a constant map.

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

### Building and checking the repository

Use the pinned Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and run from this repository:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build GroupTheory GroupTheoryTest
```

The matching precompiled mathlib cache **must succeed before the build**.
`LEAN_NUM_THREADS` is runtime tuning, not a child-process or memory cap;
`LAKE_JOBS` is unsupported by this pinned Lake. Build both roots when
verifying the maintained producer and clients. The configured CI also checks
complete transitive axioms, including private declarations, against only
`propext`, `Classical.choice` and `Quot.sound`; building alone does not
establish that audit. No benchmark, memory guarantee or source-coverage
claim is implied by this guidance.

## References

- Van Dantzig's compact-open subgroup theorem, used in Neukirch, Schmidt,
  and Wingberg, *Cohomology of Number Fields*, corrected second edition,
  Chapter I, §1, Proposition (1.1.9), for the identity-component discussion.
- Mathlib's `OpenSubgroup` and `MulAction.stabilizer` supply the algebraic interface;
  its compact-neighborhood and clopen-basis results supply the topological inputs.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, electronic version 2.3, Chapter I, §1, (1.1.9)(i) and its
  preceding paragraph. The continuous universal property here is an
  interpretation that does not require the source's local compactness assumption.
- Mathlib's `Subgroup.connectedComponentOfOne`, `QuotientGroup.lift` and
  closed-normal quotient topology supply the component and quotient APIs.
- Mathlib's clopen basis for compact Hausdorff totally disconnected spaces
  and open-quotient basis transport supply the generic open-quotient proof.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1, remarks following Theorem (1.1.11), motivate
  the compact totally disconnected character case; the open-kernel API applies
  more generally. Mathlib's `NonarchimedeanGroup`, locally constant functions
  and quotient-group interfaces supply the reusable proof ingredients.

- Formal Frontier Agents, *Continuous Group Cohomology*, compact/discrete
  continuous-map discreteness and compact-group factorization formalizations.
  The proofs use Mathlib's compact-open subbasic sets, compactness of fibers,
  clopen identity neighborhoods and continuous quotient elimination.
- Mathlib's finite-supported product neighborhoods, finite intersections of
  open subgroups and products of open quotient maps supply the finite-coordinate
  extension. The cylinder argument uses Monica Omar's product-membership API,
  in particular `Submonoid.pi_mem_of_mulSingle_mem_aux`.

**Credit and license.** Formal Frontier AI agents developed the Lean proofs and
clients. The continuous sections API builds on Mathlib's sections definitions.
The compact-open subgroup result is the classical van Dantzig theorem, used as
a prerequisite in Neukirch, Schmidt, and Wingberg's *Cohomology of Number
Fields*, Chapter I, §1. Its translation-stabilizer argument independently
assembles Mathlib's compact-neighborhood, clopen-basis and subgroup APIs;
no Pontryagin or Bourbaki passage was inspected or transcribed.
The generic open-quotient proof was first formalized in Formal Frontier's
Profinite Groups library and uses Mathlib's clopen and basis APIs.
The compact/discrete continuous-map and factorization proofs were first formalized
by Formal Frontier Agents in the Continuous Group Cohomology library; their
proofs and public declarations are preserved here, using Mathlib's compact-open
and clopen-neighborhood APIs.
The identity-component quotient API interprets Neukirch--Schmidt--Wingberg's
totally disconnected quotient and reuses Mathlib's component and quotient APIs.
The open-kernel and finite-image arguments generalize their character case
using Mathlib's nonarchimedean, locally constant and quotient APIs; this does
not assert a comparison with all abstract characters or source coverage.
The rational-circle inclusion and torsion-value lift follow the Formal Frontier
Supernatural Numbers formalization of circle-valued characters.
Prism supplied the FG scalar mathematical argument, with determinant-route
advice from Lattice. This work is credited to **Authors: Formal Frontier Agents**
and licensed under [Apache-2.0](LICENSE). Neither human review nor an external
source paper is claimed for the original cyclic norm and FG scalar proofs.
