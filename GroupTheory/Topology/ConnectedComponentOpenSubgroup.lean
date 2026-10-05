/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.CompactOpenSubgroup
public import GroupTheory.Topology.ConnectedComponentQuotient
public import GroupTheory.Topology.OpenQuotient

/-!
# Identity components, open subgroups, and open images

In a locally compact topological group, the identity component is the intersection
of **all** open subgroups. An open surjective continuous homomorphism from such a
group has dense identity-component image in the identity component of its target.
Neither assertion requires a Hausdorff hypothesis on the original groups.

The first assertion corrects the open-*normal*-subgroup intersection printed in
Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
(1.1.9)(i): the latter fails for `ℚ₂ ⋊ ℤ`. The image assertion corrects the
continuous-surjection claim in (1.1.9)(iii), which fails for the identity
map from discrete to usual `ℝ`. Its closure cannot be omitted even for open
maps, as shown by a diagonal `ℤ` in `ℝ × ℤ₂`.

## References

* Neukirch, Schmidt, and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1, (1.1.9)(i),(iii).
* Van Dantzig's compact-open subgroup theorem; Mathlib's `OpenSubgroup`,
  `Subgroup.connectedComponentOfOne`, and open quotient APIs.
* The preceding `GroupTheory.Topology.CompactOpenSubgroup`,
  `GroupTheory.Topology.ConnectedComponentQuotient`, and
  `GroupTheory.Topology.OpenQuotient` formalizations.
-/

@[expose] public section

open scoped Topology

universe u v

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- The identity component of a locally compact topological group is the infimum
of all its open subgroups. Unlike the open-normal formulation in
Neukirch--Schmidt--Wingberg, *Cohomology of Number Fields*, Chapter I, §1,
(1.1.9)(i), normality of the open subgroups cannot be required. -/
theorem connectedComponentOfOne_eq_iInf_openSubgroup :
    connectedComponentOfOne G = ⨅ H : OpenSubgroup G, (H : Subgroup G) := by
  apply le_antisymm
  · apply le_iInf
    intro H element helement
    exact H.isClopen.connectedComponent_subset H.one_mem helement
  · intro element helement
    by_contra hnot
    have hquotient : (element : QuotientGroup.connectedComponentQuotient G) ≠ 1 := by
      intro heq
      exact hnot (QuotientGroup.eq_one_iff element |>.mp heq)
    obtain ⟨H, -, hH⟩ := OpenSubgroup.exists_compact_subset_nhds_one
      (isClosed_singleton.isOpen_compl.mem_nhds hquotient.symm)
    let K : OpenSubgroup G := H.comap
      (QuotientGroup.connectedComponentQuotientMk G).toMonoidHom
      (QuotientGroup.connectedComponentQuotientMk G).continuous_toFun
    have hK : element ∈ K := (Subgroup.mem_iInf.mp helement) K
    exact (hH ((OpenSubgroup.mem_comap).mp hK)) rfl

/-- A point belongs to the identity component exactly when every open subgroup
contains it. -/
theorem mem_connectedComponentOfOne_iff_forall_openSubgroup {element : G} :
    element ∈ connectedComponentOfOne G ↔ ∀ H : OpenSubgroup G, element ∈ H := by
  rw [connectedComponentOfOne_eq_iInf_openSubgroup]
  simp

/-- A point outside the identity component is excluded by an open subgroup. -/
theorem exists_openSubgroup_not_mem_of_not_mem_connectedComponentOfOne {element : G}
    (helement : element ∉ connectedComponentOfOne G) :
    ∃ H : OpenSubgroup G, element ∉ H := by
  simpa only [mem_connectedComponentOfOne_iff_forall_openSubgroup, not_forall] using helement

end Subgroup

namespace ContinuousMonoidHom

variable {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [LocallyCompactSpace A]
variable {B : Type v} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]

/-- For a continuous open surjective homomorphism of topological groups with
locally compact source, the closure of the image of its identity component
is the identity component of the target. Openness and closure are both essential;
no separation or local compactness hypothesis is imposed on the target. This
corrects the continuous-surjection formulation of Neukirch--Schmidt--Wingberg,
*Cohomology of Number Fields*, Chapter I, §1, (1.1.9)(iii). -/
theorem closure_image_connectedComponentOfOne (hom : A →ₜ* B)
    (hopen : IsOpenQuotientMap (hom : A → B)) :
    closure (hom '' (Subgroup.connectedComponentOfOne A : Set A)) =
      (Subgroup.connectedComponentOfOne B : Set B) := by
  let J : Subgroup B :=
    ((Subgroup.connectedComponentOfOne A).map hom.toMonoidHom).topologicalClosure
  let _ : ((Subgroup.connectedComponentOfOne A).map hom.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance hom.toMonoidHom hopen.surjective
  let _ : J.Normal := Subgroup.is_normal_topologicalClosure _
  have hJclosed : IsClosed (J : Set B) := Subgroup.isClosed_topologicalClosure _
  have hImage : (Subgroup.connectedComponentOfOne A).map hom.toMonoidHom ≤
      Subgroup.connectedComponentOfOne B := by
    intro element helement
    rcases helement with ⟨source, hsource, rfl⟩
    have hconnected : hom source ∈ connectedComponent (hom (1 : A)) :=
      (hom.continuous_toFun.image_connectedComponent_subset (1 : A))
        ⟨source, hsource, rfl⟩
    change hom source ∈ connectedComponent (1 : B)
    simpa only [map_one] using hconnected
  have hJle : J ≤ Subgroup.connectedComponentOfOne B :=
    Subgroup.topologicalClosure_minimal _ hImage
      (Subgroup.isClosed_connectedComponentOfOne B)
  have hcomponent : Subgroup.connectedComponentOfOne A ≤ J.comap hom.toMonoidHom := by
    intro element helement
    exact (Subgroup.le_topologicalClosure _) ⟨element, helement, rfl⟩
  let induced : QuotientGroup.connectedComponentQuotient A →ₜ* B ⧸ J := {
    toMonoidHom := QuotientGroup.map (Subgroup.connectedComponentOfOne A) J
      hom.toMonoidHom hcomponent
    continuous_toFun := by
      apply QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
      change Continuous (fun element : A => ((hom element : B) : B ⧸ J))
      exact QuotientGroup.continuous_mk.comp hom.continuous_toFun }
  have hquotient : IsOpenQuotientMap
      (QuotientGroup.mk : A → QuotientGroup.connectedComponentQuotient A) :=
    QuotientGroup.isOpenQuotientMap_mk
  have hinduced : IsOpenQuotientMap
      (induced : QuotientGroup.connectedComponentQuotient A → B ⧸ J) := by
    apply hquotient.of_comp_iff.mp
    have hcomp : IsOpenQuotientMap
        ((QuotientGroup.mk : B → B ⧸ J) ∘ (hom : A → B)) :=
      QuotientGroup.isOpenQuotientMap_mk.comp hopen
    exact hcomp
  let _ : TotallyDisconnectedSpace (B ⧸ J) :=
    totallyDisconnectedSpace_of_isOpenQuotientMap induced hinduced
  let projection : B →ₜ* B ⧸ J := {
    toMonoidHom := QuotientGroup.mk' J
    continuous_toFun := QuotientGroup.continuous_mk }
  have hleJ : Subgroup.connectedComponentOfOne B ≤ J := by
    intro element helement
    have hker := Subgroup.connectedComponentOfOne_le_ker B projection helement
    exact (QuotientGroup.eq_one_iff element).mp hker
  change (J : Set B) = (Subgroup.connectedComponentOfOne B : Set B)
  exact congrArg (fun subgroup : Subgroup B => (subgroup : Set B))
    (le_antisymm hJle hleJ)

end ContinuousMonoidHom
