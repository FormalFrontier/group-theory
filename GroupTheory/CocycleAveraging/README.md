# Finite-group crossed-map averaging

## Headline results

Let `G` be a finite group and `A` an additive commutative group, in independent
universes, with its given `DistribMulAction G A`. Suppose multiplication by
`Nat.card G` is bijective on `A`. Every `groupCohomology.IsCocycle₁ z` is principal:

```text
z g = g • v - v.
```

With `[Fintype G]`, the theorem
`IsCocycle₁.eq_smul_sub_inverse_nsmul_sum` uses the explicit witness

```text
v = -((Equiv.ofBijective (fun a => Nat.card G • a) hN).symm (∑ g, z g)).
```

`IsCocycle₁.exists_eq_smul_sub` requires only `[Finite G]`.
There are no ring, field, characteristic, finite-generation or nontriviality
hypotheses. The witness has a minus sign for the convention `g • v - v`.

`AddMonoidHom.map_neg_inverse_nsmul_sum` proves naturality under arbitrary additive maps
between groups with bijective multiplication by the same natural number.
It needs only a finite index type, not an action or a cocycle law. Transporting
cocycles is a separate question and additionally requires action equivariance.

The application in `GroupTheoryTest.CocycleAveraging` obtains a fixed point for
the affine transformations `a ↦ g • a + z g`.

## Unit scalar orders

For `[Semiring R] [Module R A]`, a unit `(Nat.card G : R)` suffices:
`IsCocycle₁.exists_eq_smul_sub_of_isUnit_card` gives principality with only
`[Finite G]`. The semiring may be noncommutative or zero. No compatibility
between the given additive group action and the scalar action is required.

With `[Fintype G]`, `u : Rˣ` and `(u : R) = (Nat.card G : R)`,
`IsCocycle₁.eq_smul_sub_inv_smul_sum` uses the vector
`-((↑(u⁻¹) : R) • ∑ g, z g)`. The associated affine fixed point has the
opposite sign. `AddMonoidHom.map_neg_inv_smul_sum` gives naturality for arbitrary
additive maps between an `R`-module and an `S`-module, in independent universes.
It allows arbitrary finite index types and a common arbitrary natural number,
represented by a unit in each semiring. No map between the coefficient semirings,
scalar linearity, or action is needed.
