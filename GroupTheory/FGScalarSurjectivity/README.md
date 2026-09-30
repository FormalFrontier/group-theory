# Surjective scalars on finitely generated abelian groups

Import `GroupTheory.FGScalarSurjectivity` or `GroupTheory`. Throughout, let
`[AddCommGroup A] [AddGroup.FG A]` and `n : ℕ` with `2 ≤ n`. The four public
declarations in [the module](../FGScalarSurjectivity.lean) concern the
**actual** function `fun x : A => n • x`, not an arbitrary endomorphism:

- `AddCommGroup.exists_zsmul_inverse_of_nsmul_surjective hn hsurj` produces
  one `k : ℤ` with both `n • (k • x) = x` and `k • (n • x) = x` for every
  `x : A`, given scalar surjectivity `hsurj`. The integer representative
  need not be unique, but this inverse is uniform in `x`.
- `AddCommGroup.finite_coprime_of_nsmul_surjective hn hsurj` proves
  `Finite A ∧ Nat.Coprime n (Nat.card A)`. Finiteness and coprimality are
  *conclusions*, not hypotheses of this forward direction.
- `AddCommGroup.nsmul_surjective_iff_finite_coprime hn` equates scalar
  surjectivity with `Finite A ∧ Nat.Coprime n (Nat.card A)`.
- `AddCommGroup.nsmul_bijective_iff_finite_coprime hn` gives the same
  finite-and-coprime criterion for bijectivity of the actual scalar map.

## Argument

Surjectivity and finite generation of the top integer submodule yield
`⊤ ≤ Ideal.span {(n : ℤ)} • ⊤`. The finite-generation form of Nakayama's
lemma supplies an annihilator `d = 1 + (n : ℤ) * k`; `2 ≤ n` forces
`d ≠ 0`. This gives torsion, then finite generation gives `Finite A`.
The same identity makes `-k` a two-sided integer-scalar inverse. Cauchy's
theorem rules out a prime common to `n` and `Nat.card A`: a nonzero element
of that prime order would contradict the inverse. The converse reuses
mathlib's `Nat.Coprime.nsmul_right_bijective`.

## Examples and boundaries

The [FG client](../../GroupTheoryTest/FGScalarSurjectivity.lean) uses an
ordinary producer import and section, with five examples checking the
forward results, both inverse equations, `ZMod 1` at `n = 2`, and nonzero
`ZMod 7` at `n = 2`. The lower bound is essential: multiplication by `1`
is surjective on infinite finitely generated `ℤ`. Finite generation is
essential: positive-scalar multiplication is surjective on infinite `ℚ`.
No result here concerns arbitrary endomorphisms, nonabelian power maps,
all-scalar divisibility, a K-theory theorem or external-source coverage.

Use the pinned toolchain and dependency in the [root build instructions](../../README.md#use-and-verification),
including the matching `lake exe cache get` **before** building both
maintained roots. `LEAN_NUM_THREADS` tunes runtime behavior, not a
child-process or memory cap; `LAKE_JOBS` is unsupported by pinned Lake.
Formal Frontier AI agents developed and independently reviewed the original
Lean proofs and clients. Prism provided the mathematical argument, with
determinant-route advice from Lattice. Authors: Formal Frontier Agents.
Licensed under [Apache-2.0](../../LICENSE).
