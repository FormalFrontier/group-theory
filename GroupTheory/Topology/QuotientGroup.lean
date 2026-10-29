/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Dense subgroups and coset quotient topologies

An open continuous surjection has an indiscrete target exactly when every fiber is dense.
Applied to the quotient by any subgroup of a group with separately continuous multiplication,
this characterizes the indiscrete quotient topology by density of the subgroup. Normality and
continuity of inversion are not required.

The proofs use Mathlib's open quotient projection and density APIs. The quotient carrier and
topology are the usual left cosets with their inherited quotient topology.
-/

@[expose] public section

open Set
open scoped Topology

universe u v

/-- An open continuous surjection has the indiscrete target topology if and only if all its
fibers are dense. The source and target may be empty and have independent universes. -/
theorem IsOpenMap.topology_eq_top_iff_dense_fibers {X : Type u} {Y : Type v}
    [TopologicalSpace X] [t : TopologicalSpace Y] {q : X → Y}
    (ho : IsOpenMap q) (hc : Continuous q) (hs : Function.Surjective q) :
    t = ⊤ ↔ ∀ y : Y, Dense (q ⁻¹' {y}) := by
  constructor
  · intro ht y
    refine dense_iff_inter_open.mpr ?_
    intro U hU hne
    have hqU : IsOpen[⊤] (q '' U) :=
      (congrArg (fun t : TopologicalSpace Y => @IsOpen Y t (q '' U)) ht).mp (ho U hU)
    have himage : q '' U = univ :=
      (TopologicalSpace.isOpen_top_iff _).mp hqU |>.resolve_left (hne.image q).ne_empty
    have hy : y ∈ q '' U := by rw [himage]; exact mem_univ y
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨x, hx, hxy⟩
  · intro hf
    ext U
    rw [TopologicalSpace.isOpen_top_iff]
    constructor
    · intro hU
      by_cases he : U = ∅
      · exact Or.inl he
      · right
        apply eq_univ_of_forall
        intro y
        obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.mpr he
        obtain ⟨x, hqx⟩ := hs z
        obtain ⟨a, ha, haU⟩ := (hf y).exists_mem_open (hU.preimage hc)
          ⟨x, by simpa only [mem_preimage, hqx] using hz⟩
        have hay : q a = y := ha
        simpa only [mem_preimage, hay] using haU
    · rintro (rfl | rfl)
      · exact isOpen_empty
      · exact isOpen_univ

namespace QuotientGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    {H : Subgroup G}

/-- The quotient topology on the left cosets of a subgroup is indiscrete exactly when the
subgroup is dense. No normality hypothesis is needed. -/
@[to_additive /-- The quotient topology on the additive cosets of an additive subgroup is
indiscrete exactly when the subgroup is dense. -/]
theorem topology_eq_top_iff_dense :
    (inferInstance : TopologicalSpace (G ⧸ H)) = ⊤ ↔ Dense (H : Set G) := by
  have hq := isOpenQuotientMap_mk (N := H)
  rw [hq.isOpenMap.topology_eq_top_iff_dense_fibers hq.continuous hq.surjective]
  constructor
  · intro hf
    simpa only [preimage_mk_one] using hf (mk 1)
  · intro hH y
    obtain ⟨g, rfl⟩ := mk_surjective y
    have hpre : (mk : G → G ⧸ H) ⁻¹' {mk g} =
        (fun x : G => g⁻¹ * x) ⁻¹' (H : Set G) := by
      ext x
      change mk x = mk g ↔ g⁻¹ * x ∈ H
      rw [eq_comm, QuotientGroup.eq]
    rw [hpre]
    exact hH.preimage (isOpenMap_mul_left _)

/-- In the coset space of a dense subgroup the only open sets are the empty set and the
whole space. -/
@[to_additive /-- In the coset space of a dense additive subgroup the only open sets are
the empty set and the whole space. -/]
theorem isOpen_iff_of_dense (hH : Dense (H : Set G)) (s : Set (G ⧸ H)) :
    IsOpen s ↔ s = ∅ ∨ s = univ := by
  have hs := congrArg (fun t : TopologicalSpace (G ⧸ H) => @IsOpen _ t s)
    (topology_eq_top_iff_dense.mpr hH)
  exact ⟨fun h => (TopologicalSpace.isOpen_top_iff s).mp (hs.mp h),
    fun h => hs.mpr ((TopologicalSpace.isOpen_top_iff s).mpr h)⟩

end QuotientGroup
