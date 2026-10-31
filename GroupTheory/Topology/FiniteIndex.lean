/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.Quotient
public import GroupTheory.Topology.Algebra.Group.Subgroup
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finite-index subgroups and closed power ranges

In a commutative group with continuous fixed left translations, a dense finitely
generated subgroup makes every closed positive-power range have finite index and be open.
In a compact Hausdorff
group, the power range is automatically closed, and every abstract finite-index
subgroup is open without a closedness assumption. The additive statements concern
the ranges of natural-number scalar homomorphisms, not repeated sums of subgroups.

Unlike abstract finite generation of the ambient group, dense finite generation
does not imply that its underlying group is finitely generated.

## References

* Neukirch, Schmidt, and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  for the finite-index openness argument in the profinite abelian setting.
* Mathlib's finite-generation and torsion-finiteness results for commutative groups,
  together with its canonical power homomorphisms and closed finite-index subgroup lemma.
-/

@[expose] public section

universe u

namespace Subgroup

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

section

variable [ContinuousConstSMul G G]

/-- A closed positive-power range has finite index in a commutative group with
continuous fixed left translations and a dense finitely generated subgroup. Finite relative
index gives finite index for the inverse image of the power range in the dense subgroup;
finite-index descent for closed subgroups then gives finite index in the ambient group.
Neither compactness nor ambient separation is needed.
The compact case extends the profinite abelian finite-index argument in Neukirch,
Schmidt, and Wingberg, *Cohomology of Number Fields*, Chapter I, §1. -/
@[to_additive /-- A closed positive-scalar range has finite index in a commutative
additive group with continuous fixed additions and a dense finitely generated subgroup.
Neither compactness nor separation of the ambient group is needed. -/]
theorem finiteIndex_range_powMonoidHom_of_dense_fg_of_isClosed (D : Subgroup G)
    (hfg : D.FG) (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n)
    (hclosed : IsClosed ((powMonoidHom (α := G) n).range : Set G)) :
    (powMonoidHom (α := G) n).range.FiniteIndex := by
  let P : Subgroup G := (powMonoidHom (α := G) n).range
  have hrel : (D.map (powMonoidHom (α := G) n)).IsFiniteRelIndex D :=
    isFiniteRelIndex_map_powMonoidHom_of_fg hfg (Nat.ne_of_gt hn)
  have hmap_le : D.map (powMonoidHom (α := G) n) ≤ P := by
    rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  have hrelP : P.IsFiniteRelIndex D :=
    @isFiniteRelIndex_of_le_left G _ (D.map (powMonoidHom (α := G) n)) P D
      hrel hmap_le
  have : (P.comap D.subtype).FiniteIndex := isFiniteRelIndex_iff_finiteIndex.mp hrelP
  exact P.finiteIndex_of_isClosed_of_dense_subgroup D hclosed hdense

/-- A closed positive-power range is open in a commutative group with continuous fixed
left translations and a dense finitely generated subgroup. -/
@[to_additive /-- A closed positive-scalar range is open in a commutative additive
group with continuous fixed additions and a dense finitely generated subgroup. -/]
theorem isOpen_range_powMonoidHom_of_dense_fg_of_isClosed (D : Subgroup G)
    (hfg : D.FG) (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n)
    (hclosed : IsClosed ((powMonoidHom (α := G) n).range : Set G)) :
    IsOpen ((powMonoidHom (α := G) n).range : Set G) := by
  let := finiteIndex_range_powMonoidHom_of_dense_fg_of_isClosed D hfg hdense hn hclosed
  exact (Subgroup.isOpen_iff_isClosed _).mpr hclosed

end

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]

/-- In a compact Hausdorff commutative group with a dense finitely generated subgroup,
the range of every positive power map has finite index. This extends Mathlib's
`Subgroup.finiteIndex_range_powMonoidHom_of_fg`, which instead assumes abstract finite
generation of the entire ambient group. -/
@[to_additive /-- In a compact Hausdorff commutative additive group with a dense finitely
generated subgroup, the range of every positive natural-number scalar map has finite
index. -/]
theorem finiteIndex_range_powMonoidHom_of_dense_fg (D : Subgroup G) (hfg : D.FG)
    (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom (α := G) n).range.FiniteIndex := by
  apply finiteIndex_range_powMonoidHom_of_dense_fg_of_isClosed D hfg hdense hn
  exact (isCompact_range (continuous_pow n)).isClosed

/-- The range of a positive power map is open when a finitely generated subgroup is dense. -/
@[to_additive /-- The range of a positive scalar map is open when a finitely generated
additive subgroup is dense. -/]
theorem isOpen_range_powMonoidHom_of_dense_fg (D : Subgroup G) (hfg : D.FG)
    (hdense : Dense (D : Set G)) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom (α := G) n).range : Set G) := by
  apply isOpen_range_powMonoidHom_of_dense_fg_of_isClosed D hfg hdense hn
  exact (isCompact_range (continuous_pow n)).isClosed

/-- Every abstract finite-index subgroup of a compact Hausdorff commutative group
with a dense finitely generated subgroup is open; no closedness is assumed of it.
This extends the profinite abelian finite-index argument in Neukirch, Schmidt,
and Wingberg, *Cohomology of Number Fields*, Chapter I, §1. -/
@[to_additive /-- Every abstract finite-index additive subgroup of a compact Hausdorff
commutative additive group with a dense finitely generated subgroup is open. -/]
theorem isOpen_of_finiteIndex_of_dense_fg (D : Subgroup G) (hfg : D.FG)
    (hdense : Dense (D : Set G)) (H : Subgroup G) [H.FiniteIndex] :
    IsOpen (H : Set G) := by
  have hindex : 0 < H.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  apply Subgroup.isOpen_mono (H₁ := (powMonoidHom (α := G) H.index).range)
    (H₂ := H) ?_ (isOpen_range_powMonoidHom_of_dense_fg D hfg hdense hindex)
  rintro _ ⟨g, rfl⟩
  exact H.pow_index_mem g

end Subgroup

end

/-! ## Subgroup neighborhoods under continuous left translations -/

@[expose] public section

open Topology
open scoped Pointwise

universe u

/-- A subgroup is open exactly when it is a neighborhood of the identity, assuming only
continuity of fixed left translations. This gives a left-translation version of Mathlib's
subgroup neighborhood criterion. -/
@[to_additive /-- An additive subgroup is open exactly when it is a neighborhood of zero,
assuming only continuity of fixed left additions. This gives a left-translation version of
Mathlib's additive subgroup neighborhood criterion. -/]
theorem Subgroup.isOpen_iff_mem_nhds_one
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) : IsOpen (H : Set G) ↔ (H : Set G) ∈ 𝓝 (1 : G) := by
  constructor
  · exact fun hH => hH.mem_nhds H.one_mem
  · intro hH
    obtain ⟨U, hUH, hU, h1U⟩ := mem_nhds_iff.mp hH
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hx
    refine mem_nhds_iff.mpr ⟨x • U, ?_, hU.smul x, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact H.mul_mem hx (hUH hy)
    · exact ⟨1, h1U, mul_one x⟩

/-- A subgroup is open exactly when its interior contains the identity, assuming only
continuity of fixed left translations. With separately continuous multiplication, the reverse
implication recovers Mathlib's `Subgroup.isOpen_of_one_mem_interior`. -/
@[to_additive /-- An additive subgroup is open exactly when its interior contains zero,
assuming only continuity of fixed left additions. With separately continuous addition, the
reverse implication recovers Mathlib's `AddSubgroup.isOpen_of_zero_mem_interior`. -/]
theorem Subgroup.isOpen_iff_one_mem_interior
    {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    (H : Subgroup G) : IsOpen (H : Set G) ↔ (1 : G) ∈ interior (H : Set G) := by
  rw [H.isOpen_iff_mem_nhds_one, mem_interior_iff_mem_nhds]

/-- An additive subgroup is clopen exactly when it is open, assuming only continuity
of fixed left additions. -/
theorem AddSubgroup.isClopen_iff_isOpen
    {A : Type u} [AddGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A]
    (K : AddSubgroup A) : IsClopen (K : Set A) ↔ IsOpen (K : Set A) := by
  have : ContinuousConstSMul (Multiplicative A) (Multiplicative A) :=
    ⟨fun a => (continuous_const_vadd a.toAdd : Continuous (fun b : A => a.toAdd + b))⟩
  exact K.toSubgroup.isClopen_iff_isOpen

/-- A closed positive-scalar range is open in a commutative additive group with
continuous fixed additions and a dense finitely generated subgroup. -/
theorem AddSubgroup.FG.isOpen_range_nsmul_of_isClosed
    {A : Type u} [AddCommGroup A] [TopologicalSpace A] [ContinuousConstVAdd A A]
    {D : AddSubgroup A} (hFG : D.FG) (hD : Dense (D : Set A)) {n : ℕ} (hn : 0 < n)
    (hc : IsClosed (Set.range (fun a : A => n • a))) :
    IsOpen (Set.range (fun a : A => n • a)) := by
  let N : AddSubgroup A := (nsmulAddMonoidHom (α := A) n).range
  let : N.FiniteIndex :=
    AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_dense_fg_of_isClosed D hFG hD hn hc
  exact (AddSubgroup.isOpen_iff_isClosed N).mpr hc

end
