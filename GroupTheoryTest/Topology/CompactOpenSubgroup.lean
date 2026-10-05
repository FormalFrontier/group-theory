/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.CompactOpenSubgroup
public import Mathlib.Topology.Instances.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Topology.Constructions

/-!
# Compact-open subgroup boundary clients

The identity-neighborhood result is exercised on an infinite discrete group and a
compact, nondiscrete product of nontrivial finite groups. The stabilizer construction
also applies to a compact open set missing the identity and to an indiscrete,
non-Hausdorff topological group.
-/

public section

open Filter
open scoped Topology

namespace GroupTheoryTest.Topology.CompactOpenSubgroup

/-- Total disconnectedness already implies Hausdorffness for a topological group. -/
example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G] : T2Space G :=
  IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton

section InfiniteDiscrete

local instance : TopologicalSpace (Multiplicative ℤ) := ⊥
local instance : DiscreteTopology (Multiplicative ℤ) := ⟨rfl⟩
local instance : LocallyCompactSpace (Multiplicative ℤ) :=
  isCompact_singleton.locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_discrete {1}).mem_nhds (Set.mem_singleton (1 : Multiplicative ℤ)))

/-- The infinite discrete integer group has a compact open subgroup inside a singleton. -/
theorem discrete_integer_small_subgroup :
    ∃ H : OpenSubgroup (Multiplicative ℤ), IsCompact (H : Set (Multiplicative ℤ)) ∧
      (H : Set (Multiplicative ℤ)) ⊆ {1} ∧ H ≠ ⊤ := by
  obtain ⟨H, hHc, hHW⟩ := OpenSubgroup.exists_compact_subset_nhds_one
    ((isOpen_discrete {1}).mem_nhds (Set.mem_singleton (1 : Multiplicative ℤ)))
  refine ⟨H, hHc, hHW, ?_⟩
  intro htop
  have hone : Multiplicative.ofAdd (1 : ℤ) ∈ (H : Set (Multiplicative ℤ)) := by
    rw [htop]
    exact OpenSubgroup.mem_top _
  have hbad : (1 : ℤ) = 0 :=
    congrArg Multiplicative.toAdd (Set.mem_singleton_iff.mp (hHW hone))
  exact one_ne_zero hbad

/-- The discrete integer group itself is noncompact. -/
theorem discrete_integer_not_compact : ¬ CompactSpace (Multiplicative ℤ) := by
  intro hcompact
  have hfinite : Finite (Multiplicative ℤ) := finite_of_compact_of_discrete
  exact (not_finite_iff_infinite.mpr inferInstance) hfinite

/-- A compact open singleton missing the identity has only the identity in its stabilizer. -/
theorem discrete_nonidentity_leftStabilizer :
    (1 : Multiplicative ℤ) ∉ ({Multiplicative.ofAdd (1 : ℤ)} : Set (Multiplicative ℤ)) ∧
      ∀ g : Multiplicative ℤ,
        g ∈ OpenSubgroup.leftStabilizer {Multiplicative.ofAdd (1 : ℤ)}
          isCompact_singleton (isOpen_discrete _) ↔ g = 1 := by
  constructor
  · intro h
    have hbad : (0 : ℤ) = 1 :=
      congrArg Multiplicative.toAdd (Set.mem_singleton_iff.mp h)
    exact zero_ne_one hbad
  · intro g
    simp [OpenSubgroup.mem_leftStabilizer_iff, smul_eq_mul]

end InfiniteDiscrete

/-- A compact product of nontrivial finite discrete groups. -/
abbrev BinaryProduct := ℕ → Multiplicative (ZMod 2)

/-- A proper coordinate neighborhood of an infinite compact product contains a compact
open subgroup other than the whole group. -/
theorem product_small_subgroup :
    ∃ H : OpenSubgroup BinaryProduct, IsCompact (H : Set BinaryProduct) ∧
      (H : Set BinaryProduct) ⊆ {f | f 0 = 1} ∧ H ≠ ⊤ := by
  have hW : {f : BinaryProduct | f 0 = 1} ∈ 𝓝 (1 : BinaryProduct) :=
    ((isOpen_discrete {1}).preimage (continuous_apply 0)).mem_nhds (by simp)
  obtain ⟨H, hHc, hHW⟩ := OpenSubgroup.exists_compact_subset_nhds_one hW
  refine ⟨H, hHc, hHW, ?_⟩
  intro htop
  have hone : (fun _ : ℕ => Multiplicative.ofAdd (1 : ZMod 2)) ∈
      (H : Set BinaryProduct) := by
    rw [htop]
    exact OpenSubgroup.mem_top _
  have hbad : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd (hHW hone)
  exact one_ne_zero hbad

/-- The infinite product is compact, so its proper coordinate neighborhood is genuinely
smaller than the whole group despite ambient compactness. -/
theorem product_compact : CompactSpace BinaryProduct := inferInstance

/-- An infinite compact product of nontrivial finite discrete groups is not discrete. -/
theorem product_not_discrete : ¬ DiscreteTopology BinaryProduct := by
  intro hdiscrete
  have hfinite : Finite BinaryProduct := finite_of_compact_of_discrete
  exact (not_finite_iff_infinite.mpr inferInstance) hfinite

/-- Mathlib's compact-ambient clopen result specializes through the compactness bridge
on a proper coordinate neighborhood of the product. -/
theorem product_compact_ambient_bridge :
    ∃ H : OpenSubgroup BinaryProduct, IsCompact (H : Set BinaryProduct) ∧
      (H : Set BinaryProduct) ⊆ {f | f 0 = 1} := by
  have hclopen : IsClopen {f : BinaryProduct | f 0 = 1} :=
    (isClopen_discrete {1}).preimage (continuous_apply 0)
  exact OpenSubgroup.exists_compact_subset_iff_exists_subset.mpr
    (IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hclopen (by simp))

section NonHausdorff

local instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊤
local instance : IndiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

/-- The set-stabilizer API applies without a Hausdorff hypothesis, even for an
indiscrete topological group. -/
theorem indiscrete_leftStabilizer :
    OpenSubgroup.leftStabilizer (Set.univ : Set (Multiplicative (ZMod 2)))
      isCompact_univ isOpen_univ = ⊤ := by
  apply OpenSubgroup.ext
  intro g
  simp [OpenSubgroup.mem_leftStabilizer_iff]

end NonHausdorff

end GroupTheoryTest.Topology.CompactOpenSubgroup

end
