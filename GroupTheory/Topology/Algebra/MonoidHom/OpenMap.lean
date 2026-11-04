/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, FormalFrontier
-/
module

public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Open homomorphisms from groups to monoids

A quotient homomorphism from a group to a monoid is open if the original left translations
of the source are continuous. A homomorphism with a continuous function right inverse is
also open, without requiring continuity of the homomorphism or algebraic properties of the
right inverse. The additive version applies to continuous semilinear maps.

The quotient criterion generalizes Mathlib's
`MonoidHom.isOpenQuotientMap_of_isQuotientMap`. The saturation argument is adapted from
its proof: using left translations and source group identities avoids requiring inverses
in the target. No continuity of inversion or joint multiplication is needed in the source.
-/

@[expose] public section

open Set Topology

universe uG uH uF uR uS uE uP

@[to_additive isOpen_preimage_image_of_fiber_additions]
private theorem isOpen_preimage_image_of_fiber_multiplications
    {G : Type uG} {H : Type uH}
    [Group G] [TopologicalSpace G] [Monoid H]
    {F : Type uF} [FunLike F G H] [MonoidHomClass F G H] {f : F}
    (hK : ∀ k : G, f k = 1 → Continuous (fun x : G => k * x))
    {U : Set G} (hU : IsOpen U) :
    IsOpen ((f : G → H) ⁻¹' ((f : G → H) '' U)) := by
  have hsat : (f : G → H) ⁻¹' ((f : G → H) '' U) =
      ⋃ (k : G) (_ : f k = 1), (fun x : G => k * x) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hk : f (y * x⁻¹) = 1 := by
        rw [map_mul, hyx, ← map_mul, mul_inv_cancel, map_one]
      refine Set.mem_iUnion_of_mem (y * x⁻¹) (Set.mem_iUnion_of_mem hk ?_)
      change (y * x⁻¹) * x ∈ U
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hy
    · intro hx
      obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hk, hx⟩ := Set.mem_iUnion.mp hx
      refine ⟨k * x, hx, ?_⟩
      rw [map_mul, hk, one_mul]
  rw [hsat]
  exact isOpen_iUnion fun k => isOpen_iUnion fun hk =>
    (hK k hk).isOpen_preimage U hU

/-- A quotient homomorphism from a group with continuous left translations to a monoid
with its given topology is an open quotient map. -/
@[to_additive
  /-- A quotient additive homomorphism from an additive group with continuous left
  translations to an additive monoid with its given topology is an open quotient map. -/]
theorem Topology.IsQuotientMap.isOpenQuotientMap_of_monoidHom
    {G : Type uG} {H : Type uH}
    [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    [Monoid H] [TopologicalSpace H]
    {F : Type uF} [FunLike F G H] [MonoidHomClass F G H] {f : F}
    (hq : IsQuotientMap (f : G → H)) :
    IsOpenQuotientMap (f : G → H) where
  surjective := hq.surjective
  continuous := hq.continuous
  isOpenMap := by
    intro U hU
    rw [← hq.isOpen_preimage]
    exact isOpen_preimage_image_of_fiber_multiplications (f := f)
      (fun k _ => by
        simpa only [smul_eq_mul] using
          (continuous_const_smul k : Continuous (fun x : G => k • x))) hU

/-- A homomorphism from a group with continuous left translations to a monoid is open
if it has a continuous function right inverse; the homomorphism need not be continuous. -/
@[to_additive
  /-- An additive homomorphism from an additive group with continuous left translations
  to an additive monoid is open if it has a continuous function right inverse; the
  homomorphism need not be continuous. -/]
theorem MonoidHom.isOpenMap_of_continuous_rightInverse
    {G : Type uG} {H : Type uH}
    [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
    [Monoid H] [TopologicalSpace H]
    {F : Type uF} [FunLike F G H] [MonoidHomClass F G H] {f : F}
    {s : H → G} (hs : Continuous s)
    (hsec : Function.RightInverse s (f : G → H)) :
    IsOpenMap (f : G → H) := by
  intro U hU
  have hsat : IsOpen ((f : G → H) ⁻¹' ((f : G → H) '' U)) :=
    isOpen_preimage_image_of_fiber_multiplications (f := f)
      (fun k _ => by
        simpa only [smul_eq_mul] using
          (continuous_const_smul k : Continuous (fun x : G => k • x))) hU
  have himage : (f : G → H) '' U =
      s ⁻¹' ((f : G → H) ⁻¹' ((f : G → H) '' U)) := by
    ext y
    change y ∈ (f : G → H) '' U ↔ f (s y) ∈ (f : G → H) '' U
    rw [hsec y]
  rw [himage]
  exact hs.isOpen_preimage _ hsat

private theorem isOpenQuotientMap_of_isQuotientMap_compat
    {G : Type uG} {H : Type uH}
    [Group G] [TopologicalSpace G] [ContinuousMul G]
    [Group H] [TopologicalSpace H]
    {F : Type uF} [FunLike F G H] [MonoidHomClass F G H] {f : F}
    (hq : IsQuotientMap (f : G → H)) :
    IsOpenQuotientMap (f : G → H) :=
  hq.isOpenQuotientMap_of_monoidHom

/-- A continuous semilinear map with a continuous function right inverse is open when
left addition in its source is continuous. The target only needs an additive monoid,
and the right inverse need not be additive or semilinear. Taking the scalar homomorphism
to be the identity gives the continuous-linear statement over a single semiring. -/
theorem ContinuousLinearMap.isOpenMap_of_continuous_rightInverse
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {σ : R →+* S}
    {E : Type uE} [AddCommGroup E] [TopologicalSpace E]
    [ContinuousConstVAdd E E]
    {P : Type uP} [AddCommMonoid P] [TopologicalSpace P]
    [Module R E] [Module S P]
    (f : E →SL[σ] P) {s : P → E}
    (hs : Continuous s) (hsec : Function.RightInverse s f) :
    IsOpenMap f :=
  AddMonoidHom.isOpenMap_of_continuous_rightInverse
    (f := f.toLinearMap.toAddMonoidHom) hs hsec
