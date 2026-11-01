/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier
-/
module

import GroupTheory.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Operations

/-!
# Agreement with ideal operations

The submodule characteristic lemmas specialize to the canonical operations on ideals over an
arbitrary semiring.
-/

universe u w

section

variable {R : Type u} [Semiring R]

example : (0 : Ideal R) = ⊥ := by
  rw [Submodule.zero_eq_bot]

example (I J : Ideal R) : I + J = I ⊔ J := by
  rw [Submodule.add_eq_sup]

example {ι : Type w} (s : Finset ι) (f : ι → Ideal R) : s.sum f = s.sup f :=
  Submodule.sum_eq_sup (R := R) (A := R) s f

end
