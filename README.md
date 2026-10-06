# Group Theory

Reusable Lean results on identity-component quotients of topological groups,
compact open subgroups of totally disconnected locally compact groups,
open kernels and finite images of continuous group homomorphisms,
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

**Open quotients of compact spaces.** If `f : X → Y` is an open quotient map,
`X` is compact, Hausdorff and totally disconnected, and `Y` is Hausdorff,
`Topology.IsOpenQuotientMap.totallyDisconnectedSpace` gives total
disconnectedness of `Y`. This is a general result about topological spaces,
independent of group structure. See [the theorem](GroupTheory/Topology/OpenQuotient.lean)
and [a non-injective finite projection](GroupTheoryTest/Topology/OpenQuotient.lean).

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

## Use and verification

Import `GroupTheory` for these results, or import
`GroupTheory.Topology.OpenQuotient`,
`GroupTheory.Topology.ConnectedComponentQuotient`,
`GroupTheory.Topology.ConnectedComponentOpenSubgroup`,
`GroupTheory.Topology.Sections`, `GroupTheory.CyclicNorm` or
`GroupTheory.FGScalarSurjectivity`, `GroupTheory.Topology.CompactOpenSubgroup`,
`GroupTheory.Topology.OpenKernel` or `GroupTheory.Topology.CircleCharacter`
individually. For example, after
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
indiscrete non-Hausdorff and mixed connected/discrete groups.

Older Profinite Groups versions that also define
`Topology.IsOpenQuotientMap.totallyDisconnectedSpace` cannot share an import
graph with `GroupTheory.Topology.OpenQuotient` or the aggregate `GroupTheory`
import. To use both libraries, a compatible Profinite Groups version would
need to re-export Group Theory's declaration instead of defining its own.

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

**Credit and license.** Formal Frontier AI agents developed the Lean proofs and
clients. The continuous sections API builds on Mathlib's sections definitions.
The compact-open subgroup result is the classical van Dantzig theorem, used as
a prerequisite in Neukirch, Schmidt, and Wingberg's *Cohomology of Number
Fields*, Chapter I, §1. Its translation-stabilizer argument independently
assembles Mathlib's compact-neighborhood, clopen-basis and subgroup APIs;
no Pontryagin or Bourbaki passage was inspected or transcribed.
The generic open-quotient proof was first formalized in Formal Frontier's
Profinite Groups library and uses Mathlib's clopen and basis APIs.
The identity-component quotient API interprets Neukirch--Schmidt--Wingberg's
totally disconnected quotient and reuses Mathlib's component and quotient APIs.
The open-kernel and finite-image arguments generalize their character case
using Mathlib's nonarchimedean, locally constant and quotient APIs; this does
not assert a comparison with all abstract characters or source coverage.
Prism supplied the FG scalar mathematical argument, with determinant-route
advice from Lattice. This work is credited to **Authors: Formal Frontier Agents**
and licensed under [Apache-2.0](LICENSE). Neither human review nor an external
source paper is claimed for the original cyclic norm and FG scalar proofs.
