/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic

/-!
# Dependence on coordinates and single-coordinate insertions

A function that depends only on the coordinates in a set and takes `1` to `1` is trivial
on every single-coordinate insertion outside that set.
-/

@[expose] public section

universe u v w

namespace Function

/-- If a function takes `1` to `1` and its value is determined by the coordinates in `S`,
then it takes every single-coordinate insertion outside `S` to `1`. -/
theorem apply_mulSingle_eq_one_of_eqOn {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, One (G i)] [One D] [DecidableEq ι]
    (f : (∀ i, G i) → D) (hf1 : f 1 = 1) (S : Set ι)
    (hdep : ∀ x y : (∀ i, G i), (∀ i ∈ S, x i = y i) → f x = f y)
    {i : ι} (hi : i ∉ S) (a : G i) : f (Pi.mulSingle i a) = 1 := by
  calc
    f (Pi.mulSingle i a) = f (Pi.mulSingle i (1 : G i)) := by
      apply hdep
      intro j hj
      have hji : j ≠ i := by
        intro hji
        exact hi (hji ▸ hj)
      exact (Pi.mulSingle_eq_of_ne hji a).trans
        (Pi.mulSingle_eq_of_ne hji (1 : G i)).symm
    _ = f 1 := congrArg f (Pi.mulSingle_one i)
    _ = 1 := hf1

end Function
