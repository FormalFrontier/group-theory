/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Defs
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.Nonarchimedean
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.UnitsNeighborhood
public import GroupTheory.Topology.ValueSubgroups
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Nonarchimedean homomorphisms into monoids

A continuous monoid homomorphism from a nonarchimedean topological group has open
fibers if the units of its target have no small subgroups. Consequently it is
locally constant, and its range is finite when the source is compact.

The target carries its given topology: continuity of its multiplication and
separation properties are not required. The proof uses the ambient value
neighborhood characterization of no small subgroups for units, followed by
`MonoidHom.mapsTo_iff_eq_one_of_subgroup_values`.
-/

@[expose] public section

open Set Topology

universe u v

namespace ContinuousMonoidHom

variable {G : Type u} {D : Type v}
variable [Group G] [TopologicalSpace G]
variable [NonarchimedeanGroup G] [Monoid D] [TopologicalSpace D]
variable [NoSmallSubgroups Dˣ]

/-- Every fiber is open when the source is nonarchimedean and the target units
have no small subgroups. In particular, the identity fiber is open. -/
theorem isOpen_fiber_of_noSmallSubgroups_units (f : G →ₜ* D) (d : D) :
    IsOpen (f ⁻¹' ({d} : Set D)) := by
  obtain ⟨V, hV₁, hV₂, hV₃⟩ :=
    Units.noSmallSubgroups_iff_exists_open_subgroup_eq_bot.mp
      (inferInstance : NoSmallSubgroups Dˣ)
  have hVo : IsOpen V := by assumption
  have hVone : (1 : D) ∈ V := by assumption
  have hN : f ⁻¹' V ∈ 𝓝 (1 : G) := by
    apply (hVo.preimage f.continuous).mem_nhds
    change f.toMonoidHom (1 : G) ∈ V
    rw [map_one]
    exact hVone
  obtain ⟨U, hU⟩ : ∃ U : OpenSubgroup G, (U : Set G) ⊆ f ⁻¹' V := by
    rcases ‹NonarchimedeanGroup G› with ⟨hG⟩
    exact hG _ hN
  have hUtriv : ∀ x ∈ (U : Set G), f x = 1 := by
    have hiff : Set.MapsTo (f : G → D) (U : Set G) V ↔
        ∀ x ∈ (U : Set G), f x = 1 := by
      apply MonoidHom.mapsTo_iff_eq_one_of_subgroup_values
        (f := f.toMonoidHom) (H := U.toSubgroup) (V := V)
      all_goals assumption
    exact hiff.mp hU
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change f x = d at hx
  have hcoset : IsOpen ((fun y : G => x⁻¹ * y) ⁻¹' (U : Set G)) :=
    U.isOpen.preimage (continuous_const.mul continuous_id)
  have hxcoset : x ∈ (fun y : G => x⁻¹ * y) ⁻¹' (U : Set G) := by
    simp
  filter_upwards [hcoset.mem_nhds hxcoset] with y hy
  change f y = d
  calc
    f y = f (x * (x⁻¹ * y)) := by simp
    _ = f x * f (x⁻¹ * y) := f.map_mul _ _
    _ = d := by rw [hUtriv _ hy, mul_one, hx]

/-- Such a homomorphism is locally constant in the given source and target
structures. -/
theorem isLocallyConstant_of_noSmallSubgroups_units (f : G →ₜ* D) :
    IsLocallyConstant (f : G → D) := by
  intro S
  have hpre : f ⁻¹' S = ⋃ d ∈ S, f ⁻¹' ({d} : Set D) := by
    ext x
    simp
  rw [hpre]
  exact isOpen_iUnion fun d => isOpen_iUnion fun _ =>
    f.isOpen_fiber_of_noSmallSubgroups_units d

/-- A compact nonarchimedean source gives finite range, without separation or
continuity of operations on the target monoid. -/
theorem finite_range_of_noSmallSubgroups_units [CompactSpace G] (f : G →ₜ* D) :
    (Set.range f).Finite := by
  classical
  have hcover : (Set.univ : Set G) ⊆ ⋃ x : G, f ⁻¹' ({f x} : Set D) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : G => f ⁻¹' ({f x} : Set D))
    (fun x => f.isOpen_fiber_of_noSmallSubgroups_units (f x)) hcover
  refine (s.finite_toSet.image (f : G → D)).subset ?_
  rintro d ⟨x, rfl⟩
  have hx := hs (Set.mem_univ x)
  rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
  rcases Set.mem_iUnion.mp hy with ⟨hys, hxy⟩
  change f x = f y at hxy
  exact ⟨y, hys, hxy.symm⟩

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {G : Type u} {D : Type v}
variable [Group G] [TopologicalSpace G]
variable [NonarchimedeanGroup G] [Group D] [TopologicalSpace D]
variable [NoSmallSubgroups D]

/-- A continuous monoid homomorphism from a nonarchimedean topological group
into a group with no small subgroups is locally constant. The target topology
need not make its operations continuous. -/
theorem isLocallyConstant_of_noSmallSubgroups (f : G →ₜ* D) :
    IsLocallyConstant (f : G → D) := by
  have hunits : NoSmallSubgroups Dˣ := by
    apply Units.noSmallSubgroups_iff_exists_open_subgroup_eq_bot.mpr
    rcases ‹NoSmallSubgroups D› with ⟨hD⟩
    obtain ⟨U, hU, hsmall⟩ := hD
    obtain ⟨V, hVU, hVo, hVone⟩ := mem_nhds_iff.mp hU
    refine ⟨V, ?_, ?_, ?_⟩
    · assumption
    · assumption
    · intro H hH
      have himage : H.map (Units.coeHom D) = ⊥ := by
        apply hsmall (H.map (Units.coeHom D))
        rintro d ⟨u, hu, rfl⟩
        exact hVU (hH u hu)
      apply le_antisymm ?_ bot_le
      intro u hu
      apply Subgroup.mem_bot.mpr
      apply Units.ext
      have hval : (u : D) ∈ H.map (Units.coeHom D) := ⟨u, hu, rfl⟩
      simpa [himage] using hval
  let _ : NoSmallSubgroups Dˣ := hunits
  exact f.isLocallyConstant_of_noSmallSubgroups_units

end ContinuousMonoidHom
