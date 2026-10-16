/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Kernels of quotient maps induced by group equivalences

Let `N` and `M` be normal subgroups of groups `G` and `H`, and let
`f : G ≃* H` satisfy `N.map f.toMonoidHom ≤ M`. The kernel of the induced
map `G ⧸ N →* H ⧸ M` is canonically isomorphic to `M ⧸ f(N)`, where `f(N)`
is viewed as a subgroup of `M` using `Subgroup.subgroupOf`.

The construction applies Mathlib's first isomorphism theorem to the homomorphism
`M →* G ⧸ N` sending `m` to `[f.symm m]`, then transports its kernel and range
and inverts the resulting equivalence. On representatives, the comparison sends
`[g]` to `[f g]`; its inverse sends `[m]` to `[f.symm m]`.

The ambient groups may be noncommutative and lie in independent universes.
The additive versions are in `QuotientAddGroup`.

## References

* Mathlib's `QuotientGroup.quotientKerEquivRange` supplies the first-isomorphism
  construction; `QuotientGroup.ker_map`, the subgroup map/comap identities,
  `QuotientGroup.quotientMulEquivOfEq`, and `MulEquiv.subgroupCongr` supply the
  endpoint identifications.
-/

@[expose] public section

universe u v

namespace Subgroup

/-- The image of a normal subgroup under a group equivalence is normal. -/
@[to_additive AddSubgroup.normal_map_equiv
  /-- The image of a normal additive subgroup under an additive equivalence is normal. -/]
instance (priority := 100) normal_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] (N : Subgroup G) [N.Normal] (f : G ≃* H) :
    (N.map f.toMonoidHom).Normal :=
  Subgroup.Normal.map (inferInstance : N.Normal) f.toMonoidHom f.surjective

end Subgroup

namespace QuotientGroup

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Subgroup G) [N.Normal] (M : Subgroup H) [M.Normal]
variable (f : G ≃* H) (h : N.map f.toMonoidHom ≤ M)

/-- An ambient group equivalence identifies the kernel of the induced quotient map
with the quotient of `M` by the image of `N` inside `M`. The comparison sends
`[g]` to `[f g]`, and its inverse sends `[m]` to `[f.symm m]`. -/
@[to_additive QuotientAddGroup.kerMapEquivQuotientOfEquiv
  /-- An ambient additive equivalence identifies the kernel of the induced quotient map
  with the quotient of `M` by the image of `N` inside `M`. The comparison sends
  `[g]` to `[f g]`, and its inverse sends `[m]` to `[f.symm m]`. -/]
noncomputable def kerMapEquivQuotientOfEquiv :
    (map N M f.toMonoidHom (Subgroup.map_le_iff_le_comap.mp h)).ker ≃*
      M ⧸ (N.map f.toMonoidHom).subgroupOf M := by
  let ψ : M →* G ⧸ N := (mk' N).comp (f.symm.toMonoidHom.comp M.subtype)
  have hker : ψ.ker = (N.map f.toMonoidHom).subgroupOf M := by
    dsimp only [ψ]
    rw [← MonoidHom.comap_ker, ker_mk', ← Subgroup.comap_comap,
      ← Subgroup.map_equiv_eq_comap_symm' f N]
    rfl
  have hrange : ψ.range =
      (map N M f.toMonoidHom (Subgroup.map_le_iff_le_comap.mp h)).ker := by
    calc
      ψ.range = (M.map f.symm.toMonoidHom).map (mk' N) := by
        dsimp only [ψ]
        rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
      _ = (M.comap f.toMonoidHom).map (mk' N) := by
        rw [Subgroup.map_equiv_eq_comap_symm', MulEquiv.symm_symm]
      _ = (map N M f.toMonoidHom (Subgroup.map_le_iff_le_comap.mp h)).ker :=
        (ker_map N M f.toMonoidHom (Subgroup.map_le_iff_le_comap.mp h)).symm
  exact ((quotientMulEquivOfEq hker.symm).trans
    ((quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))).symm

/-- The inverse sends the class of `m` to the class of `f.symm m` in `G ⧸ N`. -/
@[to_additive (attr := simp) QuotientAddGroup.kerMapEquivQuotientOfEquiv_symm_apply_mk
  /-- The inverse sends the class of `m` to the class of `f.symm m` in `G ⧸ N`. -/]
theorem kerMapEquivQuotientOfEquiv_symm_apply_mk (m : M) :
    ((kerMapEquivQuotientOfEquiv N M f h).symm
      (m : M ⧸ (N.map f.toMonoidHom).subgroupOf M) : G ⧸ N) =
        ((f.symm (m : H) : G) : G ⧸ N) := by
  rfl

/-- A kernel class represented by `g` maps to the class represented by `f g` in `M`. -/
@[to_additive (attr := simp) QuotientAddGroup.kerMapEquivQuotientOfEquiv_apply_mk
  /-- A kernel class represented by `g` maps to the class represented by `f g` in `M`. -/]
theorem kerMapEquivQuotientOfEquiv_apply_mk (g : G) (hg : f g ∈ M) :
    kerMapEquivQuotientOfEquiv N M f h
        ⟨(g : G ⧸ N), by
          change ((f g : H) : H ⧸ M) = 1
          exact (eq_one_iff (f g)).mpr hg⟩ =
      ((⟨f g, hg⟩ : M) : M ⧸ (N.map f.toMonoidHom).subgroupOf M) := by
  apply (kerMapEquivQuotientOfEquiv N M f h).symm.injective
  apply Subtype.ext
  simp only [MulEquiv.symm_apply_apply, kerMapEquivQuotientOfEquiv_symm_apply_mk]

end QuotientGroup
