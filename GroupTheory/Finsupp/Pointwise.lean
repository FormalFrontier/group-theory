/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.DFinsupp.Pointwise
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Constant-fibre agreement for pointwise multiplication

`Finsupp.toDFinsupp` preserves the pointwise product when the fibres are constant.
The forward comparison needs only `MulZeroClass`, with no decidability assumptions.
The inverse comparison and `finsuppEquivDFinsupp` use the decidability assumptions
of those existing conversions. The equivalence's forward map is
`Finsupp.toDFinsupp`, so its product comparison reuses `Finsupp.toDFinsupp_mul`
directly. All fibre operations are those of the same given coefficient structure.

Multiplication on `DFinsupp` is selected explicitly by the non-instance datum
`DFinsupp.pointwiseMul`. This does not register a multiplication on `DFinsupp` or
change the convolution multiplication on `DirectSum`.

## Inherited arithmetic and hierarchy

The other conversion laws are already in `Mathlib.Data.Finsupp.ToDFinsupp`:
`Finsupp.toDFinsupp_zero`, `Finsupp.toDFinsupp_add`, `Finsupp.toDFinsupp_neg`,
`Finsupp.toDFinsupp_sub`, and their `DFinsupp.toFinsupp` counterparts.
The existing `finsuppAddEquivDFinsupp` and its inverse preserve natural and integer
scaling by `map_nsmul` and `map_zsmul`. Classical decisions may be chosen inside
a proof of a forward comparison; they are not additional forward hypotheses.
Uniform scalar multiplication uses the existing `Finsupp.toDFinsupp_smul` and
`DFinsupp.toFinsupp_smul` at `Monoid R`, `AddMonoid M`, `DistribMulAction R M`.
For uniform modules, `finsuppLequivDFinsupp R` is the existing linear equivalence.

Thus the multiplication comparison below applies separately at `MulZeroClass`,
`SemigroupWithZero`, `NonUnitalNonAssocSemiring`, `NonUnitalSemiring`,
`NonUnitalCommSemiring`, `NonUnitalNonAssocRing`, `NonUnitalRing`, and
`NonUnitalCommRing`. On the dependent side the stronger structures are obtained
with the corresponding existing `Function.Injective` constructors along
`DFunLike.coe` and `DFunLike.coe_injective`. Their source multiplication is
`DFinsupp.pointwiseMul`; all other source operations are the stock `DFinsupp`
zero, addition, natural scaling, and, in the ring cases, negation, subtraction
and integer scaling. The witnesses are `DFinsupp.coe_zero`, `DFinsupp.coe_add`,
`DFinsupp.coe_nsmul`, `DFinsupp.coe_neg`, `DFinsupp.coe_sub`,
`DFinsupp.coe_zsmul`, as applicable, and `DFinsupp.coe_pointwiseMul`.
The targets are the corresponding dependent `Pi` structures. These constructors
retain their supplied operations, so passing to a weaker structure retains the
same operation comparisons; no equality of proof-bearing structures is needed.

## Coercions, support and singletons

The whole-function and evaluation comparisons follow from
`Finsupp.toDFinsupp_mul`, the existing `Finsupp.toDFinsupp_coe`,
`Finsupp.coe_mul`, and `DFinsupp.pointwiseMul_apply`.
The singleton comparison is in the original orientation of `Finsupp.single_mul`.
Identifying images of singletons with `DFinsupp.single` uses the existing
`Finsupp.toDFinsupp_single` only when `DecidableEq` on the index is available.

The existing `Finsupp.support_mul_subset_left` and
`Finsupp.support_mul_subset_right` need no decisions; `Finsupp.support_mul` needs
only `DecidableEq` on the index. To compare with computable `DFinsupp` supports,
use the root theorem `toDFinsupp_support` together with
`Finsupp.toDFinsupp_mul`, choosing the additional coefficient nonzero decisions
locally when necessary. These are support inclusions, not equality with the
intersection: zero divisors are allowed.

## References

This comparison accompanies the dependent generalization of Mathlib's
`Mathlib.Data.Finsupp.Pointwise`, originally formalized by Kim Morrison.
The conversion maps and additive and linear equivalences are Mathlib's existing
ones from `Mathlib.Data.Finsupp.ToDFinsupp`.
-/

@[expose] public section

universe u v

variable {ι : Type u} {M : Type v}

namespace Finsupp

variable [MulZeroClass M]

/-- Conversion to constant dependent fibres preserves the pointwise product,
without any decidability assumptions. -/
@[simp]
theorem toDFinsupp_mul (f g : ι →₀ M) :
    (f * g).toDFinsupp =
      @Mul.mul (Π₀ _ : ι, M) (DFinsupp.pointwiseMul (β := fun _ : ι => M))
        f.toDFinsupp g.toDFinsupp := by
  apply DFinsupp.ext
  intro i
  simp only [toDFinsupp_coe, mul_apply, DFinsupp.pointwiseMul_apply]

/-- The image of the singleton product formula, in the orientation of
`Finsupp.single_mul`. This statement does not identify these images with
`DFinsupp.single`, so it needs no index decision procedure. -/
theorem toDFinsupp_single_mul (i : ι) (a b : M) :
    (single i (a * b)).toDFinsupp =
      @Mul.mul (Π₀ _ : ι, M) (DFinsupp.pointwiseMul (β := fun _ : ι => M))
        (single i a).toDFinsupp (single i b).toDFinsupp := by
  rw [single_mul, toDFinsupp_mul]

end Finsupp

namespace DFinsupp

variable [DecidableEq ι] [MulZeroClass M] [∀ m : M, Decidable (m ≠ 0)]

/-- Conversion from constant dependent fibres preserves the selected pointwise
product, using exactly the decision assumptions of `DFinsupp.toFinsupp`. -/
@[simp]
theorem toFinsupp_pointwiseMul (f g : Π₀ _ : ι, M) :
    (toFinsupp
      (@Mul.mul (Π₀ _ : ι, M) (pointwiseMul (β := fun _ : ι => M)) f g) : ι →₀ M) =
        toFinsupp f * toFinsupp g := by
  apply Finsupp.ext
  intro i
  simp only [toFinsupp_coe, Finsupp.mul_apply, pointwiseMul_apply]

end DFinsupp
