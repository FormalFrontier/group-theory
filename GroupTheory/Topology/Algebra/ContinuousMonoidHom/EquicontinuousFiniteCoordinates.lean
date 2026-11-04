/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinates
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinateNeighborhood
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.ProductDecomposition
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.UniformFun
public import GroupTheory.Topology.UniformSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Common finite-coordinate kernels for equicontinuous families

An arbitrary family of ordinary homomorphisms from a product of groups to a
group with a given uniform space structure and no small subgroups, equicontinuous
at the identity, kills one common finite-coordinate kernel. No compatibility
between the operations and the uniformity is assumed. Each source factor has
only a group structure and a topology.

Equicontinuity at the identity supplies common control of target identity
neighborhoods. The no-small-subgroups condition passes to the canonical units,
whose open value neighborhood then gives one common finite-coordinate kernel.
The conclusion concerns the entire subgroup, including infinite tails outside
the chosen coordinates; it is not a finite-support statement and does not
assert global continuity.

When target multiplication is continuous at `(1, 1)`, a continuous family is
equicontinuous at one if and only if its coordinate families are equicontinuous
at one and the union of its canonical coefficient supports is finite.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe z u v w

section

variable {A : Type z} {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, MulOneClass (G i)] [∀ i, TopologicalSpace (G i)]
    [MulOneClass D] [UniformSpace D]

attribute [local instance] Classical.decEq

namespace MonoidHom

/-- A common finite truncation of a family of homomorphisms is equicontinuous at
one if its coordinate families are equicontinuous there and multiplication in
the target is continuous at `(1, 1)`. No continuity of the homomorphisms or of
source operations, no associativity, and no small-subgroups condition is needed. -/
theorem equicontinuousAt_one_coordinateTruncation
    (F : A → ((∀ i, G i) →* D)) (s : Finset ι)
    (hcoord : ∀ i ∈ s, EquicontinuousAt
      (fun a (x : G i) => (F a).coordinateHom i x) (1 : G i))
    (hmul : ContinuousAt (fun p : D × D => p.1 * p.2) (1, 1)) :
    EquicontinuousAt (fun a x => F a (coordinateTruncation s x)) (1 : ∀ i, G i) := by
  refine (equicontinuousAt_iff_forall_mem_nhds_of_eq
    (F := fun a x => F a (coordinateTruncation s x))
    (x₀ := (1 : ∀ i, G i)) (c := (1 : D))
    (fun a => by simp only [map_one])).mpr ?_
  revert hcoord
  induction s using Finset.induction_on with
  | empty =>
    intro _ W hW
    exact Filter.Eventually.of_forall fun x a => by
      simpa only [coordinateTruncation_empty, map_one] using mem_of_mem_nhds hW
  | @insert i s hi ih =>
    intro hcoord W hW
    have hpre : {p : D × D | p.1 * p.2 ∈ W} ∈ 𝓝 (1, 1) :=
      hmul.preimage_mem_nhds (by simpa only [one_mul] using hW)
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hpre
    have hc : ∀ᶠ y in 𝓝 (1 : G i), ∀ a, (F a).coordinateHom i y ∈ U :=
      (equicontinuousAt_iff_forall_mem_nhds_of_eq
        (F := fun a (y : G i) => (F a).coordinateHom i y)
        (x₀ := (1 : G i)) (c := (1 : D))
        (fun a => map_one ((F a).coordinateHom i))).mp
          (hcoord i (Finset.mem_insert_self i s)) U hU
    have hproj : Tendsto (fun x : ∀ j, G j => x i)
        (𝓝 (1 : ∀ j, G j)) (𝓝 (1 : G i)) :=
      (continuous_apply i).continuousAt
    have hhead : ∀ᶠ x in 𝓝 (1 : ∀ j, G j), ∀ a, (F a).coordinateHom i (x i) ∈ U :=
      hproj.eventually hc
    have htail := ih (fun j hj => hcoord j (Finset.mem_insert_of_mem hj)) V hV
    filter_upwards [hhead, htail] with x hx htx
    intro a
    rw [coordinateTruncation_insert s i hi x, map_mul]
    simpa [coordinateHom_apply] using
      hUV (show ((F a).coordinateHom i (x i), F a (coordinateTruncation s x)) ∈
        U ×ˢ V from ⟨hx a, htx a⟩)

end MonoidHom

end

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
  have hunits : NoSmallSubgroups Dˣ :=
    NoSmallSubgroups.of_injective (Units.coeHom D)
      Units.continuous_val.continuousAt (fun _ _ h => Units.ext h)
  let _ : NoSmallSubgroups Dˣ := hunits
  have hcontrol : ∀ W : Set D, W ∈ 𝓝 (1 : D) →
      ∃ U : Set (∀ i, G i), U ∈ 𝓝 (1 : ∀ i, G i) ∧
        ∀ a, Set.MapsTo (F a) U W := by
    intro W hW
    have hevent : ∀ᶠ x in 𝓝 (1 : ∀ i, G i), ∀ a, F a x ∈ W :=
      (equicontinuousAt_iff_forall_mem_nhds_of_eq
        (F := fun a x => F a x) (x₀ := (1 : ∀ i, G i)) (c := (1 : D))
        (fun a => map_one (F a))).mp hF W hW
    exact ⟨{x | ∀ a, F a x ∈ W}, hevent, fun a x hx => hx a⟩
  obtain ⟨s, hs⟩ :=
    exists_finset_forall_coordinateKernel_le_ker_toHomUnits F hcontrol
  refine ⟨s, fun a x hx => MonoidHom.mem_ker.mpr ?_⟩
  have hxunit : (F a).toHomUnits x = 1 := MonoidHom.mem_ker.mp (hs a hx)
  exact congrArg (fun z : Dˣ => (z : D)) hxunit

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

namespace ContinuousMonoidHom

section

attribute [local instance] Classical.decEq

/-- The union of the supports of the canonical coefficient families of continuous
homomorphisms equicontinuous at the identity is finite. No continuity of group
operations is required, and the indexing type may be arbitrary. -/
theorem finite_iUnion_support_productCoefficients_of_equicontinuousAt_one
    (F : A → ((∀ i, G i) →ₜ* D))
    (hF : EquicontinuousAt (fun a x => F a x) (1 : ∀ i, G i)) :
    (⋃ a : A, ((F a).productCoefficients.support : Set ι)).Finite := by
  classical
  obtain ⟨s, hs⟩ :=
    MonoidHom.exists_finset_forall_coordinateKernel_le_ker
      (fun a => (F a).toMonoidHom) hF
  refine s.finite_toSet.subset (Set.iUnion_subset fun a => ?_)
  exact (coordinateKernel_le_ker_iff_support_subset (F a) s).mp (hs a)

end

section

attribute [local instance] Classical.decEq

/-- A family of continuous homomorphisms from a product into a group with a uniform
space structure and no small subgroups is equicontinuous at one exactly when its
coordinate families are equicontinuous at one and their canonical supports have
finite union. Only multiplication continuity at `(1, 1)` is needed for the converse;
no compatibility between the group structure and the uniformity is required. -/
theorem equicontinuousAt_one_iff_coordinateHom_and_finite_iUnion_support
    (F : A → ((∀ i, G i) →ₜ* D))
    (hmul : ContinuousAt (fun p : D × D => p.1 * p.2) (1, 1)) :
    EquicontinuousAt (fun a x => F a x) (1 : ∀ i, G i) ↔
      (∀ i : ι, EquicontinuousAt
        (fun a (x : G i) => (F a).coordinateHom i x) (1 : G i)) ∧
      (⋃ a : A, ((F a).productCoefficients.support : Set ι)).Finite := by
  constructor
  · intro hF
    refine ⟨?_, finite_iUnion_support_productCoefficients_of_equicontinuousAt_one F hF⟩
    intro i
    have hone : (Pi.mulSingle i (1 : G i) : ∀ j, G j) = 1 := by simp
    have hins : Tendsto (fun y : G i => (Pi.mulSingle i y : ∀ j, G j))
        (𝓝 (1 : G i)) (𝓝 (1 : ∀ j, G j)) := by
      have hcont : Tendsto (fun y : G i => (Pi.mulSingle i y : ∀ j, G j))
          (𝓝 (1 : G i)) (𝓝 (Pi.mulSingle i (1 : G i))) :=
        (continuous_mulSingle i).continuousAt
      simpa only [hone] using hcont
    intro U hU
    simpa only [coordinateHom_apply, hone] using hins.eventually (hF U hU)
  · rintro ⟨hcoord, hsupport⟩
    let s : Finset ι := hsupport.toFinset
    have hs (a : A) : (F a).productCoefficients.support ⊆ s := by
      intro i hi
      exact hsupport.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨a, hi⟩)
    have htrunc (a : A) (x : ∀ i, G i) :
        F a (MonoidHom.coordinateTruncation s x) = F a x := by
      have hk := (coordinateKernel_le_ker_iff_support_subset (F a) s).mpr (hs a)
      calc
        F a (MonoidHom.coordinateTruncation s x) =
            (F a).finiteCoordinateFactor s (fun i => x i) := by
          rw [finiteCoordinateFactor_apply, MonoidHom.coordinateTruncation_apply]
          apply congrArg (fun y : ∀ i, G i => F a y)
          funext i
          by_cases hi : i ∈ s <;> simp [hi]
        _ = F a x := (F a).finiteCoordinateFactor_restrict s hk x
    have hfinite : EquicontinuousAt
        (fun a x => F a (MonoidHom.coordinateTruncation s x)) (1 : ∀ i, G i) := by
      refine MonoidHom.equicontinuousAt_one_coordinateTruncation
        (fun a => (F a).toMonoidHom) s ?_ hmul
      intro i hi
      simpa [MonoidHom.coordinateHom_apply, coordinateHom_apply] using hcoord i
    simpa only [htrunc] using hfinite

end

section

variable [ContinuousMul D]

attribute [local instance] Classical.decEq

/-- The coordinate-family and common-finite-support criterion when target
multiplication is continuous everywhere. -/
theorem equicontinuousAt_one_iff_coordinateHom_and_finite_iUnion_support_of_continuousMul
    (F : A → ((∀ i, G i) →ₜ* D)) :
    EquicontinuousAt (fun a x => F a x) (1 : ∀ i, G i) ↔
      (∀ i : ι, EquicontinuousAt
        (fun a (x : G i) => (F a).coordinateHom i x) (1 : G i)) ∧
      (⋃ a : A, ((F a).productCoefficients.support : Set ι)).Finite :=
  equicontinuousAt_one_iff_coordinateHom_and_finite_iUnion_support F
    continuous_mul.continuousAt

end

end ContinuousMonoidHom
