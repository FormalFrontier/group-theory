/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.FiniteIndex
public import GroupTheory.Topology.OpenKernel
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.GroupTheory.Torsion

/-!
# Finite-image and open-kernel rational-circle characters

The torsion subgroup of `CharacterModule A` consists precisely of characters with finite
image. For a topological additive group, `CharacterModule.openKernel A` consists of
characters whose kernels are open. Both subgroups admit restriction along additive maps;
the latter restriction requires continuity. On compact groups, open kernels imply finite
image; in compact Hausdorff commutative groups with a densely finitely generated subgroup,
the converse holds.

Annihilating each point separately does not give a uniform annihilator for a character.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
  for the finite-index openness principle in the profinite abelian setting.
* Mathlib's `CharacterModule`, `AddCommGroup.torsion`, and the finite torsion
  layers of `AddCircle` supply the algebraic character interfaces.
-/

@[expose] public section

universe u v w

namespace CharacterModule

variable {A : Type u} [AddCommGroup A]

/-- A rational-circle character has finite image exactly when it has finite order in the
character group. The order must annihilate the entire character, not merely each value
with a potentially different exponent. -/
theorem mem_torsion_iff_finite_range (c : CharacterModule A) :
    c ∈ AddCommGroup.torsion (CharacterModule A) ↔ (Set.range c).Finite := by
  constructor
  · intro hc
    obtain ⟨n, hn, hzero⟩ := ((AddCommGroup.mem_torsion c).mp hc).exists_nsmul_eq_zero
    apply (AddCircle.finite_torsion (p := (1 : ℚ)) hn).subset
    rintro _ ⟨a, rfl⟩
    have ha := congrArg (fun d : CharacterModule A => d a) hzero
    change n • c a = 0 at ha
    exact ha
  · intro hfinite
    change (c.range : Set (AddCircle (1 : ℚ))).Finite at hfinite
    have : Finite c.range := hfinite.to_subtype
    obtain ⟨n, hn, hzero⟩ : AddMonoid.ExponentExists c.range :=
      AddMonoid.ExponentExists.of_finite
    apply (AddCommGroup.mem_torsion c).mpr
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨n, hn, ?_⟩
    apply CharacterModule.ext
    intro a
    have ha := congrArg (fun x : c.range => (x : AddCircle (1 : ℚ)))
      (hzero (⟨c a, ⟨a, rfl⟩⟩ : c.range))
    change n • c a = 0 at ha
    change n • c a = 0
    exact ha

variable [TopologicalSpace A] [IsTopologicalAddGroup A]

/-- The subgroup of rational-circle characters with open kernels. No continuity is
assumed of a character a priori. -/
def openKernel (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] : AddSubgroup (CharacterModule A) where
  carrier := {c | IsOpen (c.ker : Set A)}
  zero_mem' := by
    change IsOpen ((0 : CharacterModule A).ker : Set A)
    have hzero : ((0 : CharacterModule A).ker : Set A) = Set.univ := by
      ext a
      change (0 : A →+ AddCircle (1 : ℚ)) a = 0 ↔ True
      simp
    rw [hzero]
    exact isOpen_univ
  add_mem' := by
    intro c d hc hd
    apply AddSubgroup.isOpen_mono (H₁ := c.ker ⊓ d.ker) (H₂ := (c + d).ker)
    · intro a ha
      have hca : c a = 0 := ha.1
      have hda : d a = 0 := ha.2
      change c a + d a = 0
      simp [hca, hda]
    · change IsOpen ((c.ker : Set A) ∩ (d.ker : Set A))
      exact hc.inter hd
  neg_mem' := by
    intro c hc
    have hker : (-c).ker = c.ker := by
      ext a
      change -(c a) = 0 ↔ c a = 0
      exact neg_eq_zero
    change IsOpen ((-c).ker : Set A)
    rw [hker]
    exact hc

/-- Membership in the open-kernel subgroup is exactly openness of the character's kernel. -/
@[simp] theorem mem_openKernel (c : CharacterModule A) :
    c ∈ openKernel A ↔ IsOpen (c.ker : Set A) := Iff.rfl

/-- An open-kernel character is locally constant. -/
theorem isLocallyConstant_of_mem_openKernel {c : CharacterModule A}
    (hc : c ∈ openKernel A) : IsLocallyConstant (c : A → AddCircle (1 : ℚ)) :=
  c.isLocallyConstant_of_isOpen_ker ((mem_openKernel c).mp hc)

/-- An open-kernel character has finite order on a compact domain. -/
theorem openKernel_le_torsion [CompactSpace A] :
    openKernel A ≤ AddCommGroup.torsion (CharacterModule A) := by
  intro c hc
  exact (mem_torsion_iff_finite_range c).mpr
    (isLocallyConstant_of_mem_openKernel hc).range_finite

/-- A finite-image character has open kernel when a compact Hausdorff abelian group
contains a densely finitely generated subgroup. -/
theorem torsion_le_openKernel_of_dense_fg [CompactSpace A] [T2Space A]
    (D : AddSubgroup A) (hfg : D.FG) (hdense : Dense (D : Set A)) :
    AddCommGroup.torsion (CharacterModule A) ≤ openKernel A := by
  intro c hc
  have hfinite := (mem_torsion_iff_finite_range c).mp hc
  change (c.range : Set (AddCircle (1 : ℚ))).Finite at hfinite
  have : Finite c.range := hfinite.to_subtype
  have : c.ker.FiniteIndex :=
    AddSubgroup.finiteIndex_ker (c : A →+ AddCircle (1 : ℚ))
  exact (mem_openKernel c).mpr
    (AddSubgroup.isOpen_of_finiteIndex_of_dense_fg D hfg hdense c.ker)

/-- On a compact Hausdorff abelian group with a densely finitely generated subgroup,
open-kernel characters are exactly the finite-order characters. -/
theorem openKernel_eq_torsion_of_dense_fg [CompactSpace A] [T2Space A]
    (D : AddSubgroup A) (hfg : D.FG) (hdense : Dense (D : Set A)) :
    openKernel A = AddCommGroup.torsion (CharacterModule A) := by
  exact le_antisymm openKernel_le_torsion
    (torsion_le_openKernel_of_dense_fg D hfg hdense)

section Restriction

variable {B : Type v} [AddCommGroup B]
variable {C : Type w} [AddCommGroup C]

/-- Precomposition of finite-order characters by an arbitrary additive homomorphism. -/
def torsionRestrict (f : A →+ B) :
    AddCommGroup.torsion (CharacterModule B) →+
      AddCommGroup.torsion (CharacterModule A) where
  toFun c := ⟨dual f.toIntLinearMap c,
    AddCommGroup.le_comap_torsion (dual f.toIntLinearMap).toAddMonoidHom c.property⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (dual f.toIntLinearMap)
  map_add' c d := by
    apply Subtype.ext
    exact map_add (dual f.toIntLinearMap) (c : CharacterModule B) (d : CharacterModule B)

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Restriction evaluates by precomposition. -/
@[simp] theorem torsionRestrict_apply (f : A →+ B)
    (c : AddCommGroup.torsion (CharacterModule B)) (a : A) :
    ((torsionRestrict f c : CharacterModule A) a) = (c : CharacterModule B) (f a) := rfl

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Restriction along the identity additive homomorphism is the identity. -/
@[simp] theorem torsionRestrict_id :
    torsionRestrict (AddMonoidHom.id A) = AddMonoidHom.id _ := by
  ext c a
  simp

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- Successive restrictions agree with restriction along the composite. -/
theorem torsionRestrict_comp (f : A →+ B) (g : B →+ C) :
    torsionRestrict (g.comp f) = (torsionRestrict f).comp (torsionRestrict g) := by
  ext c a
  change (c : CharacterModule C) (g (f a)) =
    (torsionRestrict g c : CharacterModule B) (f a)
  exact (torsionRestrict_apply g c (f a)).symm

variable [TopologicalSpace B] [IsTopologicalAddGroup B]
variable [TopologicalSpace C] [IsTopologicalAddGroup C]

/-- Continuous precomposition of open-kernel characters. -/
def openKernelRestrict (f : A →ₜ+ B) : openKernel B →+ openKernel A where
  toFun c := ⟨dual f.toAddMonoidHom.toIntLinearMap c, by
    change IsOpen ((dual f.toAddMonoidHom.toIntLinearMap
      (c : CharacterModule B)).ker : Set A)
    have hker : ((dual f.toAddMonoidHom.toIntLinearMap
        (c : CharacterModule B)).ker : Set A) =
        (f : A → B) ⁻¹' ((c : CharacterModule B).ker : Set B) := by
      ext a
      simp only [Set.mem_preimage, dual_apply]
      rfl
    rw [hker]
    exact c.property.preimage f.continuous⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (dual f.toAddMonoidHom.toIntLinearMap)
  map_add' c d := by
    apply Subtype.ext
    exact map_add (dual f.toAddMonoidHom.toIntLinearMap)
      (c : CharacterModule B) (d : CharacterModule B)

/-- Evaluating the restricted open-kernel character evaluates its source character. -/
@[simp] theorem openKernelRestrict_apply (f : A →ₜ+ B) (c : openKernel B) (a : A) :
    ((openKernelRestrict f c : CharacterModule A) a) = (c : CharacterModule B) (f a) := rfl

/-- Continuous restriction along the identity is the identity. -/
@[simp] theorem openKernelRestrict_id :
    openKernelRestrict (ContinuousAddMonoidHom.id A) = AddMonoidHom.id _ := by
  ext c a
  simp

/-- Continuous restriction respects composition. -/
theorem openKernelRestrict_comp (f : A →ₜ+ B) (g : B →ₜ+ C) :
    openKernelRestrict (g.comp f) = (openKernelRestrict f).comp (openKernelRestrict g) := by
  ext c a
  simp

end Restriction

end CharacterModule

end
