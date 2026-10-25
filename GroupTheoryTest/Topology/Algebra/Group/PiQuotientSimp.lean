/-
Copyright (c) 2026 Formal Frontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import GroupTheory.Topology.Algebra.Group.PiDiscreteFactor

/-! # Computation for selected product quotients -/

namespace ContinuousMonoidHom

universe uI uG

variable {I : Type uI} {G : I → Type uG}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

-- Both default-simp routes, using only selected-coordinate hypotheses.
example (s : Finset I) (N : ∀ i : s, Subgroup (G i))
    [∀ i : s, (N i).Normal] (x : ∀ i, G i)
    (hx : ∀ i : s, x i ∈ N i) :
    x ∈ (piQuotient s N).toMonoidHom.ker ∧ piQuotient s N x = 1 := by
  simp [hx]

-- A proper singleton test when A is nontrivial; x false is unrestricted.
-- In particular this includes nontrivial finite discrete A.
example {A : Type uG} [Group A] [TopologicalSpace A] (x : Bool → A) :
    piQuotient (G := fun _ : Bool => A) {true}
      (fun _ => (⊥ : Subgroup A)) x = 1 ↔ x true = 1 := by
  simp

-- Empty selected set, retaining the given dependent source.
example (N : ∀ i : (∅ : Finset I), Subgroup (G i))
    [∀ i : (∅ : Finset I), (N i).Normal] (x : ∀ i, G i) :
    piQuotient ∅ N x = 1 := by
  simp

-- Existing coordinate computation with ordinary default simp.
example (s : Finset I) (N : ∀ i : s, Subgroup (G i))
    [∀ i : s, (N i).Normal] (x : ∀ i, G i) (i : s) :
    piQuotient s N x i = QuotientGroup.mk (x i) := by
  simp


end ContinuousMonoidHom
