/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Pointwise scalar multiplication and conversion to `DFinsupp`

`Finsupp.toDFinsupp_pointwise_smul` identifies `Finsupp.pointwiseScalar` with the
existing `DFinsupp` scalar action, after pulling back the action on each coefficient
along evaluation of the scalar function. The scalars are full functions; only the
vector has finite support. No algebraic structure on the scalars is needed beyond
the given zero-preserving action on the coefficients.

The action on `DFinsupp` is selected explicitly, not registered as an instance.
This avoids the nested-function action ambiguity described in
`Mathlib.Data.Finsupp.Pointwise`. The coefficient types and their class data in the
comparison are constant copies of the given type and action.

## Reused interfaces

With the evaluation-pulled-back coefficient actions supplied explicitly,
`DFinsupp.smul_apply`, `DFinsupp.coe_smul`, `DFinsupp.single_smul` and
`DFinsupp.support_smul` give the application, coercion, singleton and support
interfaces. The singleton interface requires decidable equality of indices;
computable supports additionally require decisions for nonzero coefficients.
The forward conversion theorem has neither requirement.

For the plain and additive equivalences, the forward map is
`Finsupp.toDFinsupp`. Applying `DFinsupp.toFinsupp` to the forward comparison and
using the inverse identities gives the inverse comparison. These use the decision
arguments of `finsuppEquivDFinsupp`. For semiring coefficients the same comparison
applies to `Finsupp.pointwiseScalarSemiring` and `Finsupp.pointwiseModule`.
The pointwise module comparison uses `finsuppAddEquivDFinsupp`, not the
uniform-scalar equivalence `finsuppLequivDFinsupp`.

## References

This comparison follows Mathlib's `Finsupp` pointwise theory by Kim Morrison and
its conversion interfaces between `Finsupp` and `DFinsupp`.
-/

@[expose] public section

universe u v w

namespace Finsupp

variable {I : Type u} {B : Type v} {C : Type w}
  [instZero : Zero C] [SMulZeroClass B C]

local notation "Q" =>
  @SMul.smul (I → B) (Π₀ _ : I, C)
    (@SMulZeroClass.toSMul _ _ _
      (@DFinsupp.instSMulZeroClass (ι := I) (γ := I → B) (β := fun _ => C)
        (fun _ => instZero)
        (fun i => SMulZeroClass.compFun C (fun s : I → B => s i))))

/-- Conversion to `DFinsupp` preserves pointwise scalar multiplication, using the
zero-preserving coefficient actions pulled back along evaluation. -/
@[simp]
theorem toDFinsupp_pointwise_smul (s : I → B) (f : I →₀ C) :
    ((pointwiseScalar (α := I) (β := B) (γ := C)).smul s f).toDFinsupp =
      Q s f.toDFinsupp :=
  DFinsupp.ext fun _ => rfl

end Finsupp
