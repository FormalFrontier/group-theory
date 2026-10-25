/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Kernels of quotient maps induced by group equivalences

Let `N` and `M` be normal subgroups of groups `G` and `H`, and let
`f : G ≃* H` satisfy `N.map (f : G →* H) ≤ M`. The kernel of the induced
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
@[to_additive
  /-- The image of a normal additive subgroup under an additive equivalence is normal. -/]
instance (priority := 100) normal_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] (N : Subgroup G) [N.Normal] (f : G ≃* H) :
    (N.map (f : G →* H)).Normal :=
  Subgroup.Normal.map (inferInstance : N.Normal) (f : G →* H) f.surjective

end Subgroup

namespace QuotientGroup

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Subgroup G) [N.Normal] (M : Subgroup H) [M.Normal]
variable (f : G ≃* H) (h : N.map (f : G →* H) ≤ M)

/-- An ambient group equivalence identifies the kernel of the induced quotient map
with the quotient of `M` by the image of `N` inside `M`. The comparison sends
`[g]` to `[f g]`, and its inverse sends `[m]` to `[f.symm m]`. -/
@[to_additive
  /-- An ambient additive equivalence identifies the kernel of the induced quotient map
  with the quotient of `M` by the image of `N` inside `M`. The comparison sends
  `[g]` to `[f g]`, and its inverse sends `[m]` to `[f.symm m]`. -/]
noncomputable def kerMapEquivQuotientOfEquiv :
    (map N M (f : G →* H) (Subgroup.map_le_iff_le_comap.mp h)).ker ≃*
      M ⧸ (N.map (f : G →* H)).subgroupOf M := by
  let ψ : M →* G ⧸ N := (mk' N).comp ((f.symm : H →* G).comp M.subtype)
  have hker : ψ.ker = (N.map (f : G →* H)).subgroupOf M := by
    dsimp only [ψ]
    rw [← MonoidHom.comap_ker, ker_mk', ← Subgroup.comap_comap,
      ← Subgroup.map_equiv_eq_comap_symm f N]
    rfl
  have hrange : ψ.range =
      (map N M (f : G →* H) (Subgroup.map_le_iff_le_comap.mp h)).ker := by
    calc
      ψ.range = (M.map (f.symm : H →* G)).map (mk' N) := by
        dsimp only [ψ]
        rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
      _ = (M.comap (f : G →* H)).map (mk' N) := by
        rw [Subgroup.map_equiv_eq_comap_symm, MulEquiv.symm_symm]
      _ = (map N M (f : G →* H) (Subgroup.map_le_iff_le_comap.mp h)).ker :=
        (ker_map N M (f : G →* H) (Subgroup.map_le_iff_le_comap.mp h)).symm
  exact ((quotientMulEquivOfEq hker.symm).trans
    ((quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))).symm

/-- The inverse sends the class of `m` to the class of `f.symm m` in `G ⧸ N`. -/
@[to_additive (attr := simp)
  /-- The inverse sends the class of `m` to the class of `f.symm m` in `G ⧸ N`. -/]
theorem kerMapEquivQuotientOfEquiv_symm_apply_mk (m : M) :
    ((kerMapEquivQuotientOfEquiv N M f h).symm
      (m : M ⧸ (N.map (f : G →* H)).subgroupOf M) : G ⧸ N) =
        ((f.symm (m : H) : G) : G ⧸ N) := by
  rfl

/-- A kernel class represented by `g` maps to the class represented by `f g` in `M`. -/
@[to_additive (attr := simp)
  /-- A kernel class represented by `g` maps to the class represented by `f g` in `M`. -/]
theorem kerMapEquivQuotientOfEquiv_apply_mk (g : G) (hg : f g ∈ M) :
    kerMapEquivQuotientOfEquiv N M f h
        ⟨(g : G ⧸ N), by
          change ((f g : H) : H ⧸ M) = 1
          exact (eq_one_iff (f g)).mpr hg⟩ =
      ((⟨f g, hg⟩ : M) : M ⧸ (N.map (f : G →* H)).subgroupOf M) := by
  apply (kerMapEquivQuotientOfEquiv N M f h).symm.injective
  apply Subtype.ext
  simp only [MulEquiv.symm_apply_apply, kerMapEquivQuotientOfEquiv_symm_apply_mk]

universe u' v'

/-- The kernel-quotient equivalences commute with a commuting square of ambient group
homomorphisms preserving the normal subgroups. The kernel map is the restriction of
the quotient map induced by `a`, and the map on the quotients of `M` and `M'` is
induced by the restriction of `b`. -/
@[to_additive
  /-- The kernel-quotient equivalences commute with a commuting square of ambient additive
  group homomorphisms preserving the normal subgroups. The kernel map is the restriction of
  the quotient map induced by `a`, and the map on the quotients of `M` and `M'` is
  induced by the restriction of `b`. -/]
theorem kerMapEquivQuotientOfEquiv_naturality {G' : Type u'} {H' : Type v'}
    [Group G'] [Group H'] (N' : Subgroup G') [N'.Normal]
    (M' : Subgroup H') [M'.Normal] (f' : G' ≃* H')
    (h' : N'.map (f' : G' →* H') ≤ M') (a : G →* G') (b : H →* H')
    (ha : N ≤ N'.comap a) (hb : M ≤ M'.comap b)
    (hcomm : ∀ g : G, f' (a g) = b (f g)) :
    let qA : G ⧸ N →* G' ⧸ N' := map N N' a ha
    let kernelMap :
        (map N M (f : G →* H) (Subgroup.map_le_iff_le_comap.mp h)).ker →*
          (map N' M' (f' : G' →* H') (Subgroup.map_le_iff_le_comap.mp h')).ker :=
      MonoidHom.restrict (f := qA) (by
        intro x hx
        obtain ⟨g, rfl⟩ := mk'_surjective N x
        change ((f g : H) : H ⧸ M) = 1 at hx
        change ((f' (a g) : H') : H' ⧸ M') = 1
        apply (eq_one_iff (f' (a g))).mpr
        rw [hcomm]
        exact hb ((eq_one_iff (f g)).mp hx))
    let subgroupMap : M →* M' :=
      MonoidHom.restrict (f := b) (by intro y hy; exact hb hy)
    let latticeMap : M ⧸ (N.map (f : G →* H)).subgroupOf M →*
        M' ⧸ (N'.map (f' : G' →* H')).subgroupOf M' :=
      map _ _ subgroupMap (by
        intro y hy
        change b (y : H) ∈ N'.map (f' : G' →* H')
        change (y : H) ∈ N.map (f : G →* H) at hy
        obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_map.mpr
          ⟨a n, ha hn, (hcomm n).trans (congrArg b hny)⟩)
    latticeMap.comp (kerMapEquivQuotientOfEquiv N M f h).toMonoidHom =
      (kerMapEquivQuotientOfEquiv N' M' f' h').toMonoidHom.comp kernelMap := by
  dsimp only
  apply MonoidHom.ext
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := mk'_surjective N x
  have hg : f g ∈ M := by
    apply (eq_one_iff (f g)).mp
    exact hx
  have hg' : f' (a g) ∈ M' := by
    rw [hcomm]
    exact hb hg
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hrep :
      kerMapEquivQuotientOfEquiv N M f h ⟨(mk' N) g, hx⟩ =
        ((⟨f g, hg⟩ : M) : M ⧸ (N.map (f : G →* H)).subgroupOf M) :=
    kerMapEquivQuotientOfEquiv_apply_mk N M f h g hg
  rw [hrep, map_mk]
  change
    ((⟨b (f g), hb hg⟩ : M') : M' ⧸ (N'.map (f' : G' →* H')).subgroupOf M') =
      kerMapEquivQuotientOfEquiv N' M' f' h'
        ⟨((a g : G') : G' ⧸ N'), by
          change ((f' (a g) : H') : H' ⧸ M') = 1
          exact (eq_one_iff (f' (a g))).mpr hg'⟩
  rw [kerMapEquivQuotientOfEquiv_apply_mk N' M' f' h' (a g) hg']
  apply congrArg (fun m : M' => (m : M' ⧸ (N'.map (f' : G' →* H')).subgroupOf M'))
  apply Subtype.ext
  exact (hcomm g).symm

end QuotientGroup
