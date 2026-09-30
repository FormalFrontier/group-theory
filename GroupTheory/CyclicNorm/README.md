# Finite cyclic norm exactness

For `[AddCommGroup A]`, `sigma : AddMonoid.End A` and `m : ℕ`, import
`GroupTheory.CyclicNorm` (or `GroupTheory`) and apply
[`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range`](../CyclicNorm.lean).
Its hypotheses are:

1. `0 < m` and `sigma ^ m = 1` in the endomorphism ring. The period need not
   be the *exact* order of `sigma`.
2. `Function.Injective (nsmulAddMonoidHom (α := A) m)`, multiplication by
   this same `m` on `A`. No surjectivity or divisibility is required.
3. For every `a` such that `sigma a - a` lies in
   `(nsmulAddMonoidHom (α := A) m).range`, there is a `z` fixed by `sigma`
   with `a - z` in that range. Each fixed class modulo `m • A` therefore
   has a fixed representative; no global choice of a section is assumed.

It concludes the following equality of mathlib additive subgroups:

```lean
(∑ i ∈ Finset.range m, sigma ^ i).ker = (1 - sigma).range
```

## Why fixed lifting suffices

The geometric-sum identity first gives `range (1 - sigma) ≤ ker norm`.
For `v` with norm zero, a double partial sum constructs `w` such that
`(1 - sigma) w = m • v`. Thus `sigma w - w ∈ m • A`, so the lifting
hypothesis gives `w - z = m • b` with `sigma z = z`. Applying
`1 - sigma` yields `m • v = m • ((1 - sigma) b)`; injectivity of
multiplication by `m` cancels the scalar and proves the reverse inclusion.
This never inverts multiplication by `m` on all of `A`.

## Clients and limits

[`GroupTheoryTest.CyclicNorm`](../../GroupTheoryTest/CyclicNorm.lean) has
four `public import`s and a public section. Its 14 examples exercise the
general result across universes, period one, trivial groups, a bijective
scalar and transfer through an injective restriction. A coordinate swap on
`ℤ × ℤ` with `m = 2` has the equality even though multiplication by two
is **not** onto. Another application uses `sigma = -1` on `ZMod 3`.

The hypotheses are material, not merely a convenient proof technique:
`sigma = -1` on `ℤ` with `m = 2` lacks a fixed integral lift for a fixed
class modulo `2ℤ`, and the equality fails; with `sigma = 1` on `ZMod 2`,
multiplication by two is not injective and the equality also fails. The
client's quotient-induced map and coordinate-swap helper are private; they
are not exported results. The theorem asserts a conditional norm-kernel
criterion, not a general cohomology or unconditional Tate statement.

Use the pinned toolchain and dependency in the [root build instructions](../../README.md#use-and-verification),
including `lake exe cache get` **before** building both maintained roots.
Formal Frontier AI agents developed and independently reviewed the original
Lean theorem and clients. Authors: Formal Frontier Agents. Licensed under
[Apache-2.0](../../LICENSE).
