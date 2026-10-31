/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.Category.Grp.Colimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Sums.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.NormNum

/-!
# A nonabelian arrow-relations quotient

The diagram consists of an identity arrow between two copies of `S₃`, together
with an isolated copy of `S₃`. Its arrow relation identifies the first two legs,
while generators from the arrow component and the isolated component need not
commute. Descent to `S₃` detects this without a normal-form calculation.
-/

open CategoryTheory GrpCat.Colimits

private abbrev Diagram := Fin 2 ⊕ Discrete Unit

private abbrev diagram : Diagram ⥤ GrpCat :=
  (Functor.const Diagram).obj (GrpCat.of (Equiv.Perm (Fin 3)))

private def evaluate : ColimitType diagram →* Equiv.Perm (Fin 3) :=
  desc diagram (fun _ => MonoidHom.id (Equiv.Perm (Fin 3))) (fun _ => rfl)

private theorem evaluate_ι (j : Diagram) (a : Equiv.Perm (Fin 3)) :
    evaluate (ι diagram j a) = a :=
  desc_ι diagram (fun _ => MonoidHom.id (Equiv.Perm (Fin 3)))
    (fun _ => rfl) j a

-- The nonidentity indexing arrow genuinely identifies two distinct factor copies.
example (a : Equiv.Perm (Fin 3)) :
    ι diagram (Sum.inl 1) a = ι diagram (Sum.inl 0) a :=
  ι_map diagram ((CategoryTheory.Sum.inl_ (Fin 2) (Discrete Unit)).map
    (homOfLE (show (0 : Fin 2) ≤ 1 by decide))) a

-- Distinct connected components are not made to commute by the construction.
example :
    ι diagram (Sum.inl 0) (Equiv.swap 0 1) *
        ι diagram (Sum.inr (Discrete.mk ())) (Equiv.swap 1 2) ≠
      ι diagram (Sum.inr (Discrete.mk ())) (Equiv.swap 1 2) *
        ι diagram (Sum.inl 0) (Equiv.swap 0 1) := by
  intro h
  have he := congrArg evaluate h
  simp only [map_mul, evaluate_ι] at he
  have h0 := Equiv.congr_fun he 0
  norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at h0
