# Group Theory

Reusable Lean results on finite cyclic norms and natural scalar maps of
finitely generated abelian groups. The library depends directly on mathlib,
not on a source repository or the incubator. The mathematical guides explain
the proof ideas, examples and limits in more detail.

## Headline results

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
`[AddGroup.FG A]` and `n : ℕ` with `2 ≤ n`, surjectivity of the **actual**
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

Import `GroupTheory` for both sets of results or import
`GroupTheory.CyclicNorm` or `GroupTheory.FGScalarSurjectivity` individually.
For example, after `import GroupTheory`, use
`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm hperiod hinjective hlift`
or `(AddCommGroup.nsmul_surjective_iff_finite_coprime (A := A) (n := n) hn).mp hsurj`.
The maintained `GroupTheoryTest` root exercises the interfaces but is not
required by downstream imports: its cyclic client has four `public import`s
and a public section (14 examples and two private helpers), while its FG
client has an ordinary import and section (five examples). Private test
helpers are not additional public theorems.

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

### Historical build-cost observation

On September 30, 2026, one combined native verification of both `GroupTheory`
and `GroupTheoryTest` roots (FG scalar surjectivity and cyclic norm) took **115
seconds end-to-end** using the pinned Lean/mathlib versions above and the
resolved nine-package graph. This included setup, the matching precompiled
mathlib cache, both builds and the complete transitive standard-axiom audit
(including private/generated declarations). It is not isolated compilation
time, a cold-machine benchmark, a timing for this release or a runtime
guarantee. Allow setup, toolchain, dependency and cache time and disk space;
network/cache state affects elapsed time. Peak memory (RSS) and peak disk use
were not measured, so no numeric resource minimum or cap follows.

**Credit and license.** Formal Frontier AI agents developed and independently
reviewed the original Lean proofs and clients. Prism supplied the FG scalar
mathematical argument, with determinant-route advice from Lattice. This work
is credited to **Authors: Formal Frontier Agents** and licensed under
[Apache-2.0](LICENSE). Neither a human review nor an external source paper
is claimed for these original proofs.
