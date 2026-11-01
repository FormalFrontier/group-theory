/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite sums of submodules

A finite sum of submodules is the corresponding finite supremum.
No compatibility with the multiplication on the ambient semiring is required.
-/

@[expose] public section

open scoped BigOperators

universe u v w

namespace Submodule

/-- A finite sum of submodules is the corresponding finite supremum. -/
@[simp] public theorem sum_eq_sup
    {R : Type u} {A : Type v} {ι : Type w}
    [Semiring R] [Semiring A] [Module R A]
    (s : Finset ι) (f : ι → Submodule R A) :
    s.sum f = s.sup f := by
  rw [Finset.sum_eq_fold]
  rfl

end Submodule
