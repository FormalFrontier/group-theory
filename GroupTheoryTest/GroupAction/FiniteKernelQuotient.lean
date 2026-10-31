/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import GroupTheory.GroupAction.Quotient

universe u v

/-- The genuine kernel quotient of the original action is finite and discrete,
with its canonical continuous projection and unique permutation-valued descent.
The evaluation action on the original `A` is recorded by its two action laws;
no instance for the original action or either original topology is replaced. -/
private theorem finite_discrete_action_kernel_quotient
    {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [Finite A] [T0Space A] [MulAction G A]
    (hcts : ∀ a : A, Continuous (fun g : G => g • a)) :
    let α : G →* Equiv.Perm A := MulAction.toPermHom G A
    let Q := G ⧸ α.ker
    let q : G →* Q := QuotientGroup.mk' α.ker
    let barα : Q →* Equiv.Perm A := QuotientGroup.kerLift α
    let β : Q → A → A := fun x a => barα x a
    Finite Q ∧ DiscreteTopology Q ∧ Continuous (q : G → Q) ∧
      (∀ a : A, β 1 a = a) ∧
      (∀ (x y : Q) (a : A), β (x * y) a = β x (β y a)) ∧
      (∀ (g : G) (a : A), β (q g) a = g • a) ∧
      barα.comp q = α ∧
      ∃! ρ : Q →* Equiv.Perm A, ρ.comp q = α := by
  let α : G →* Equiv.Perm A := MulAction.toPermHom G A
  let Q := G ⧸ α.ker
  let q : G →* Q := QuotientGroup.mk' α.ker
  let barα : Q →* Equiv.Perm A := QuotientGroup.kerLift α
  let β : Q → A → A := fun x a => barα x a
  have hfinite : Finite Q :=
    Finite.of_injective barα (QuotientGroup.kerLift_injective α)
  have hdiscrete : DiscreteTopology Q :=
    MulAction.discreteTopology_quotient_ker_toPermHom hcts
  have hqcts : Continuous (q : G → Q) := by
    change Continuous (fun g : G => (QuotientGroup.mk g : Q))
    exact continuous_quot_mk
  have hfactor : barα.comp q = α := by
    apply MonoidHom.ext
    intro g
    rfl
  refine ⟨hfinite, hdiscrete, hqcts, ?_, ?_, ?_, hfactor, ?_⟩
  · intro a
    exact congrArg (fun p : Equiv.Perm A => p a) barα.map_one
  · intro x y a
    exact congrArg (fun p : Equiv.Perm A => p a) (barα.map_mul x y)
  · intro g a
    have hg := congrArg (fun f : G →* Equiv.Perm A => f g) hfactor
    exact congrArg (fun p : Equiv.Perm A => p a) hg
  · refine ⟨barα, hfactor, ?_⟩
    intro ρ hρ
    apply MonoidHom.ext
    intro x
    refine Quotient.inductionOn x ?_
    intro g
    have hρg := congrArg (fun f : G →* Equiv.Perm A => f g) hρ
    have hbarαg := congrArg (fun f : G →* Equiv.Perm A => f g) hfactor
    exact hρg.trans hbarαg.symm
