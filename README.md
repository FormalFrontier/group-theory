# Group Theory

Reusable Lean results on continuous compatible sections of monoid diagrams,
finite cyclic norms and natural scalar maps of finitely generated abelian groups.
The library depends directly on mathlib, not on a source repository or the
incubator. The mathematical guides explain the proof ideas, examples and limits
in more detail.

## Headline results

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

Import `GroupTheory` for all three sets of results, or import
`GroupTheory.Topology.Sections`, `GroupTheory.CyclicNorm` or
`GroupTheory.FGScalarSurjectivity` individually. For example, after
`import GroupTheory`, use `MonCat.sectionsLift F q hq` to bundle a compatible
continuous family and `MonCat.sectionsπ_comp_sectionsLift F q hq j` to recover
its `j`th component; use
`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm hperiod hinjective hlift`
or `(AddCommGroup.nsmul_surjective_iff_finite_coprime (A := A) (n := n) hn).mp hsurj`.
The maintained `GroupTheoryTest` root exercises the interfaces but is not
required by downstream imports. Its sections clients include empty indexing,
parallel arrows, non-group stages, discontinuous transitions, nonsurjective
projections and a nontrivial consequence of `sections_topology`. The cyclic
clients cover fixed-class lifting, the coordinate swap on `ℤ × ℤ` and
counterexamples when hypotheses are dropped; the scalar clients include
concrete `ZMod` examples.

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

**Credit and license.** Formal Frontier AI agents developed the Lean proofs and
clients. The continuous sections API builds on Mathlib's sections definitions.
Prism supplied the FG scalar mathematical argument, with determinant-route
advice from Lattice. This work is credited to **Authors: Formal Frontier Agents**
and licensed under [Apache-2.0](LICENSE). Neither human review nor an external
source paper is claimed for the original cyclic norm and FG scalar proofs.
