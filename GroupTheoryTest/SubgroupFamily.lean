/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Topology.Algebra.Group.SubgroupFamily
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.UniformSpace.Basic

/-!
# Boundary cases for subgroup-family topologies

The empty family on the original additive group of integers gives the indiscrete
uniformity and topology. A nonempty family consisting of the zero subgroup gives
the discrete topology and a proper zero neighborhood. Each check passes the original
whole group record to the basis and its original additive-group parent to the stock
right uniformity. No data instance is replaced.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- With no subgroups prescribed, the associated uniformity and topology are indiscrete.
The equalities also record the original whole group, its parents, the family, and the
exact topology parent of the stock right uniform space. -/
private theorem empty_family_indiscrete :
    let g : AddCommGroup ℤ := inferInstance
    let a : AddGroup ℤ := g.toAddGroup
    let m : AddMonoid ℤ := a.toAddMonoid
    let c : AddCommMonoid ℤ := g.toAddCommMonoid
    let H : Empty → @AddSubgroup ℤ a := Empty.elim
    let S : Empty → @AddSubmonoid ℤ m.toAddZeroClass := fun i => (H i).toAddSubmonoid
    let T : Empty → @AddSubsemigroup ℤ m.toAdd :=
      fun i => (H i).toAddSubmonoid.toAddSubsemigroup
    let B : @AddGroupFilterBasis ℤ a := @AddSubgroup.familyBasis ℤ Empty g H
    let u : UniformSpace ℤ :=
      @IsTopologicalAddGroup.rightUniformSpace ℤ a B.topology
        (@AddGroupFilterBasis.isTopologicalAddGroup ℤ a B)
    g = (inferInstance : AddCommGroup ℤ) ∧
      a = g.toAddGroup ∧ m = a.toAddMonoid ∧ c = g.toAddCommMonoid ∧
      H = (Empty.elim : Empty → @AddSubgroup ℤ a) ∧
      S = (fun i => (H i).toAddSubmonoid) ∧
      T = (fun i => (H i).toAddSubmonoid.toAddSubsemigroup) ∧
      u.toTopologicalSpace = B.topology ∧ u.uniformity = ⊤ ∧ B.topology = ⊤ := by
  intro g a m c H S T B u
  have hn : @nhds ℤ B.topology 0 = ⊤ := by
    simpa using (@AddSubgroup.familyBasis_nhds_zero_eq_iInf ℤ Empty g H)
  have hu : u.uniformity = ⊤ := by
    change Filter.comap (fun p : ℤ × ℤ => p.2 + -p.1) (@nhds ℤ B.topology 0) = ⊤
    rw [hn, Filter.comap_top]
  have he : u = ⊤ := UniformSpace.ext hu
  have ht : B.topology = ⊤ := congrArg (@UniformSpace.toTopologicalSpace ℤ) he
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hu, ht⟩

/-- The zero subgroup in a nonempty family makes the topology discrete. In contrast to
an empty family, it supplies a zero neighborhood that does not contain `1`. -/
private theorem zero_subgroup_discrete :
    let g : AddCommGroup ℤ := inferInstance
    let a : AddGroup ℤ := g.toAddGroup
    let m : AddMonoid ℤ := a.toAddMonoid
    let c : AddCommMonoid ℤ := g.toAddCommMonoid
    let H : Unit → @AddSubgroup ℤ a := fun _ => ⊥
    let S : Unit → @AddSubmonoid ℤ m.toAddZeroClass := fun i => (H i).toAddSubmonoid
    let T : Unit → @AddSubsemigroup ℤ m.toAdd :=
      fun i => (H i).toAddSubmonoid.toAddSubsemigroup
    let B : @AddGroupFilterBasis ℤ a := @AddSubgroup.familyBasis ℤ Unit g H
    let u : UniformSpace ℤ :=
      @IsTopologicalAddGroup.rightUniformSpace ℤ a B.topology
        (@AddGroupFilterBasis.isTopologicalAddGroup ℤ a B)
    g = (inferInstance : AddCommGroup ℤ) ∧
      a = g.toAddGroup ∧ m = a.toAddMonoid ∧ c = g.toAddCommMonoid ∧
      H = (fun _ : Unit => (⊥ : @AddSubgroup ℤ a)) ∧
      S = (fun i => (H i).toAddSubmonoid) ∧
      T = (fun i => (H i).toAddSubmonoid.toAddSubsemigroup) ∧
      u.toTopologicalSpace = B.topology ∧
      u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) ∧ B.topology = ⊥ ∧
      ({0} : Set ℤ) ∈ @nhds ℤ B.topology 0 ∧ (1 : ℤ) ∉ ({0} : Set ℤ) := by
  intro g a m c H S T B u
  have hn : @nhds ℤ B.topology 0 = 𝓟 ({0} : Set ℤ) := by
    simpa [H] using (@AddSubgroup.familyBasis_nhds_zero_eq_iInf ℤ Unit g H)
  have hu : u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) := by
    change Filter.comap (fun p : ℤ × ℤ => p.2 + -p.1) (@nhds ℤ B.topology 0) = _
    rw [hn, Filter.comap_principal]
    congr 1
    ext p
    simp [SetRel.id, add_neg_eq_zero, eq_comm]
  have he : u = ⊥ := UniformSpace.ext hu
  have ht : B.topology = ⊥ := congrArg (@UniformSpace.toTopologicalSpace ℤ) he
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hu, ht, ?_, ?_⟩
  · rw [hn]
    exact Filter.mem_principal_self _
  · simp

/-- For the zero-subgroup family on the original integer module, fixed-scalar
continuity upgrades on the saved right uniform space and supplies the stock
completion module. Its scalar action computes on the original image, which
separates `2` from `1`. The diagonal uniformity comes from the preceding control,
not from the discrete topology alone. -/
private theorem zero_subgroup_completion_smul :
    let r : Ring ℤ := inferInstance
    let s : Semiring ℤ := r.toSemiring
    let g : AddCommGroup ℤ := inferInstance
    let m : @Module ℤ ℤ s g.toAddCommMonoid := inferInstance
    let d : @DistribSMul ℤ ℤ g.toAddGroup.toAddMonoid.toAddZeroClass :=
      @DistribMulAction.toDistribSMul ℤ ℤ s.toMonoid g.toAddCommMonoid.toAddMonoid
        m.toDistribMulAction
    let H : Unit → @AddSubgroup ℤ g.toAddGroup := fun _ => ⊥
    let B : @AddGroupFilterBasis ℤ g.toAddGroup := @AddSubgroup.familyBasis ℤ Unit g H
    let u : UniformSpace ℤ :=
      @IsTopologicalAddGroup.rightUniformSpace ℤ g.toAddGroup B.topology
        (@AddGroupFilterBasis.isTopologicalAddGroup ℤ g.toAddGroup B)
    u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) ∧
      ∃ hU : @IsUniformAddGroup ℤ u g.toAddGroup,
        ∃ hC : @UniformContinuousConstSMul ℤ ℤ u d.toSMulZeroClass.toSMul,
          let mC : @Module ℤ (@UniformSpace.Completion ℤ u) s
              (@UniformSpace.Completion.instAddCommGroup ℤ u g hU).toAddCommMonoid :=
            @UniformSpace.Completion.instModule (α := ℤ) (R := ℤ) u g hU s m hC
          mC.toDistribMulAction.toMulAction.toSMul =
            (inferInstance : SMul ℤ (@UniformSpace.Completion ℤ u)) ∧
          @SMul.smul ℤ (@UniformSpace.Completion ℤ u) mC.toDistribMulAction.toMulAction.toSMul
              2 (@UniformSpace.Completion.coe' ℤ u 1) =
            @UniformSpace.Completion.coe' ℤ u 2 ∧
          @UniformSpace.Completion.coe' ℤ u 2 ≠ @UniformSpace.Completion.coe' ℤ u 1 := by
  intro r s g m d H B u
  rcases zero_subgroup_discrete with ⟨_, _, _, _, _, _, _, _, hu, ht, _, _⟩
  have hUniformity : u.uniformity = 𝓟 (SetRel.id : Set (ℤ × ℤ)) := hu
  have hTopology : B.topology = ⊥ := ht
  have hTop : @IsTopologicalAddGroup ℤ B.topology g.toAddGroup :=
    @AddGroupFilterBasis.isTopologicalAddGroup ℤ g.toAddGroup B
  have hU : @IsUniformAddGroup ℤ u g.toAddGroup :=
    @isUniformAddGroup_of_addCommGroup ℤ g B.topology hTop
  have hH : ∀ (a : ℤ) (i : Unit) (x : ℤ), x ∈ H i → a • x ∈ H i := by
    intro a i x hx
    have hx0 : x = 0 := AddSubgroup.mem_bot.mp hx
    simpa only [hx0, smul_zero] using (H i).zero_mem
  have hCont : @ContinuousConstSMul ℤ ℤ B.topology d.toSMulZeroClass.toSMul :=
    @AddSubgroup.familyBasis_continuousConstSMul ℤ Unit g ℤ d H hH
  have hC : @UniformContinuousConstSMul ℤ ℤ u d.toSMulZeroClass.toSMul :=
    @uniformContinuousConstSMul_of_continuousConstSMul ℤ ℤ g.toAddGroup d u hU hCont
  have : @IsUniformAddGroup ℤ u g.toAddGroup := hU
  have : @UniformContinuousConstSMul ℤ ℤ u d.toSMulZeroClass.toSMul := hC
  have hT0 : @T0Space ℤ u.toTopologicalSpace := by
    change @T0Space ℤ B.topology
    rw [hTopology]
    infer_instance
  refine ⟨hUniformity, hU, hC, ?_⟩
  intro mC
  refine ⟨rfl, ?_, ?_⟩
  · have hOne :=
      @MulAction.one_smul ℤ (@UniformSpace.Completion ℤ u) s.toMonoid
        mC.toDistribMulAction.toMulAction (@UniformSpace.Completion.coe' ℤ u 1)
    calc
      _ = @SMul.smul ℤ (@UniformSpace.Completion ℤ u)
            mC.toDistribMulAction.toMulAction.toSMul 1
            (@UniformSpace.Completion.coe' ℤ u 1) +
          @SMul.smul ℤ (@UniformSpace.Completion ℤ u)
            mC.toDistribMulAction.toMulAction.toSMul 1
            (@UniformSpace.Completion.coe' ℤ u 1) :=
        @Module.add_smul ℤ (@UniformSpace.Completion ℤ u) s
          (@UniformSpace.Completion.instAddCommGroup ℤ u g hU).toAddCommMonoid
          mC 1 1 (@UniformSpace.Completion.coe' ℤ u 1)
      _ = @UniformSpace.Completion.coe' ℤ u 1 +
          @UniformSpace.Completion.coe' ℤ u 1 :=
        congrArg (fun z : @UniformSpace.Completion ℤ u => z + z) hOne
      _ = @UniformSpace.Completion.coe' ℤ u 2 :=
        (@UniformSpace.Completion.coe_add ℤ u g.toAddGroup hU 1 1).symm
  · intro hEq
    exact (by decide : (2 : ℤ) ≠ 1) (@UniformSpace.Completion.coe_injective ℤ u hT0 2 1 hEq)
