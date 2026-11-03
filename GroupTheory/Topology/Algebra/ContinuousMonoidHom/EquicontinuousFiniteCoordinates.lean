/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.UniformFun
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Common finite-coordinate kernels for equicontinuous families

An arbitrary family of ordinary homomorphisms from a product of groups to a
group with a given uniform space structure and no small subgroups, equicontinuous
at the identity, kills one common finite-coordinate kernel. No compatibility
between the operations and the uniformity is assumed. Each source factor has
only a group structure and a topology.

The aggregate homomorphism takes values in the full uniform function space.
Equicontinuity at the identity is precisely continuity of this aggregate there.
The finite-coordinate kernel theorem for a single ordinary homomorphism then
applies. In particular the conclusion concerns the entire subgroup, including
infinite tails outside the chosen coordinates; it is not a finite-support
statement and does not assert global continuity.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe z u v w

variable {A : Type z} {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [UniformSpace D] [NoSmallSubgroups D]

namespace MonoidHom

/-- A family of ordinary homomorphisms equicontinuous at the identity into a
group with no small subgroups kills one common finite-coordinate subgroup.
Elements of this subgroup may have arbitrary, possibly infinite, tails outside
the finite set. No continuity of any group operation is required. -/
theorem exists_finset_forall_coordinateKernel_le_ker
    (F : A → ((∀ i, G i) →* D))
    (hF : EquicontinuousAt (fun a x => F a x) (1 : ∀ i, G i)) :
    ∃ s : Finset ι, ∀ a,
      Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ (F a).ker := by
  let Φ : (∀ i, G i) →* UniformFun A D :=
    { toFun := fun x => UniformFun.ofFun (fun a => F a x)
      map_one' := by
        apply UniformFun.toFun.injective
        funext a
        exact map_one (F a)
      map_mul' := by
        intro x y
        apply UniformFun.toFun.injective
        funext a
        exact map_mul (F a) x y }
  have hcont : ContinuousAt Φ (1 : ∀ i, G i) ↔
      EquicontinuousAt (fun a x => F a x) (1 : ∀ i, G i) := by
    change Tendsto (fun x => UniformFun.ofFun (fun a => F a x))
      (𝓝 (1 : ∀ i, G i))
      (𝓝 (UniformFun.ofFun (fun a => F a (1 : ∀ i, G i)))) ↔ _
    rw [UniformFun.tendsto_iff_tendstoUniformly]
    rfl
  obtain ⟨s, hs⟩ := Φ.exists_finset_coordinateKernel_le_ker (hcont.mpr hF)
  refine ⟨s, fun a x hx => MonoidHom.mem_ker.mpr ?_⟩
  have hxΦ : Φ x = 1 := MonoidHom.mem_ker.mp (hs hx)
  exact congrArg (fun f : UniformFun A D => f a) hxΦ

/-- One finite set of coordinates suffices to make every member of an
at-identity equicontinuous family equal to one on the whole off-coordinate
subgroup. The indexing type of the family need not be finite or inhabited. -/
theorem exists_finset_forall_eq_one_of_coordinates_eq_one
    (F : A → ((∀ i, G i) →* D))
    (hF : EquicontinuousAt (fun a x => F a x) (1 : ∀ i, G i)) :
    ∃ s : Finset ι, ∀ a (x : ∀ i, G i), (∀ i ∈ s, x i = 1) → F a x = 1 := by
  obtain ⟨s, hs⟩ := exists_finset_forall_coordinateKernel_le_ker F hF
  refine ⟨s, fun a x hx => MonoidHom.mem_ker.mp (hs a ?_)⟩
  intro i hi
  exact Subgroup.mem_bot.mpr (hx i hi)

end MonoidHom
