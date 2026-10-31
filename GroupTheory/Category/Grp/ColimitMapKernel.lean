/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Category.Grp.ColimitMap

/-!
# Surjectivity and kernels of maps between group-diagram colimits

An objectwise surjective compatible family of group homomorphisms induces a
surjection between the canonical colimits. Its kernel is the normal closure of
the images of the component kernels under the source generator maps.

The source and target diagrams may have independent object-group universes, and
no restriction is imposed on the indexing category. In particular, the results
also apply to the empty diagram.

The proofs use the generator and descent API of `GrpCat.Colimits`: the target
generator images lie in the range of the induced map, while quotienting the
source colimit by the component kernels allows descent from the target diagram.

## References

* Mathlib's subgroup and surjective homomorphism factorization API, formalized by
  Kexing Ying, and quotient groups, formalized by Kevin Buzzard and Patrick Massot,
  supply the normal closure, factorization and quotient universal properties.
-/

@[expose] public section

universe uJ vJ uF uG

open CategoryTheory

namespace GrpCat.Colimits

variable {J : Type uJ} [Category.{vJ} J]
  {F : J ⥤ GrpCat.{uF}} {G : J ⥤ GrpCat.{uG}}
  (α : ∀ j, F.obj j →* G.obj j)
  (hα : ∀ {j k : J} (f : j ⟶ k),
    (α k).comp (F.map f).hom = (G.map f).hom.comp (α j))

/-- Objectwise surjective compatible homomorphisms induce a surjection between
canonical group colimits. No nonemptiness assumption on the indexing category is
needed. -/
theorem map_surjective (hs : ∀ j, Function.Surjective (α j)) :
    Function.Surjective (map α hα) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← iSup_range_ι G]
  refine iSup_le fun j => ?_
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := hs j b
  exact ⟨ι F j a, map_ι α hα j a⟩

/-- The kernel of the colimit map induced by objectwise surjective compatible
homomorphisms is the normal closure of the images of their kernels in the source
colimit. The source and target object groups may lie in independent universes. -/
theorem ker_map (hs : ∀ j, Function.Surjective (α j)) :
    (map α hα).ker = Subgroup.normalClosure
      (⋃ j, ι F j '' ((α j).ker : Set (F.obj j))) := by
  let K : Subgroup (ColimitType F) := Subgroup.normalClosure
    (⋃ j, ι F j '' ((α j).ker : Set (F.obj j)))
  have hK : K ≤ (map α hα).ker := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, a, ha, rfl⟩
    change map α hα (ι F j a) = 1
    rw [map_ι α hα j a, (α j).mem_ker.mp ha, map_one]
  let q : ColimitType F →* ColimitType F ⧸ K := QuotientGroup.mk' K
  have hq : q.ker = K := QuotientGroup.ker_mk' K
  have hkill (j : J) : (α j).ker ≤ (q.comp (ι F j)).ker := by
    intro a ha
    change ι F j a ∈ q.ker
    rw [hq]
    exact Subgroup.subset_normalClosure
      (Set.mem_iUnion.mpr ⟨j, ⟨a, ha, rfl⟩⟩)
  let β : ∀ j, G.obj j →* ColimitType F ⧸ K := fun j =>
    MonoidHom.liftOfSurjective (α j) (hs j) ⟨q.comp (ι F j), hkill j⟩
  have hβ_comp (j : J) : (β j).comp (α j) = q.comp (ι F j) := by
    exact MonoidHom.liftOfRightInverse_comp (α j)
      (Function.surjInv (hs j)) (Function.rightInverse_surjInv (hs j))
      ⟨q.comp (ι F j), hkill j⟩
  have hβ : ∀ {j k : J} (f : j ⟶ k),
      (β k).comp (G.map f).hom = β j := by
    intro j k f
    apply MonoidHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hs j b
    change β k ((G.map f).hom (α j a)) = β j (α j a)
    calc
      β k ((G.map f).hom (α j a)) = β k (α k ((F.map f).hom a)) :=
        congrArg (β k) (DFunLike.congr_fun (hα f) a).symm
      _ = q (ι F k ((F.map f).hom a)) :=
        DFunLike.congr_fun (hβ_comp k) ((F.map f).hom a)
      _ = q (ι F j a) := congrArg q (ι_map F f a)
      _ = β j (α j a) := (DFunLike.congr_fun (hβ_comp j) a).symm
  let ψ : ColimitType G →* ColimitType F ⧸ K := desc G β hβ
  have hψ : ψ.comp (map α hα) = q := by
    apply hom_ext F
    intro j
    rw [MonoidHom.comp_assoc, map_comp_ι α hα j, ← MonoidHom.comp_assoc]
    change ((desc G β hβ).comp (ι G j)).comp (α j) = q.comp (ι F j)
    rw [desc_comp_ι G β hβ j]
    exact hβ_comp j
  change (map α hα).ker = K
  apply le_antisymm ?_ hK
  intro x hx
  rw [← hq]
  change q x = 1
  rw [← hψ, MonoidHom.comp_apply, (map α hα).mem_ker.mp hx, map_one]

end GrpCat.Colimits
