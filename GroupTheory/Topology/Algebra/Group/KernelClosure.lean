/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Maps.Basic

/-!
# Kernels in dense commuting squares

Consider continuous homomorphisms `j : M →* C` and `F : C →* Q`, with `j` dense,
and a homomorphism `q : M →* Q` satisfying the whole triangle `F.comp j = q`.
If `q` is a quotient map, the kernel of `F` lies in the closure of the image of
the kernel of `q`. Consequently these two sets have the same closure; if the
kernel of `F` is closed, it equals that closure.

Only `C` is required to be a topological group. The group operations on `M`
need not be continuous. The target may be any unital magma with a topology;
neither associativity nor continuity of its multiplication is required. No
separation hypothesis is imposed. A separate version assumes that `q` is open,
without assuming that it is surjective.

## References

The saturation argument is adapted from Mathlib's
`MonoidHom.isOpenQuotientMap_of_isQuotientMap`. Continuity after `j`, followed by
right multiplication in `C`, replaces continuity of multiplication in `M`.
-/

@[expose] public section

open Set Topology

universe uM uC uQ

namespace MonoidHom

@[to_additive]
private theorem isOpen_image_preimage_of_isQuotientMap
    {M : Type uM} {C : Type uC} {Q : Type uQ}
    [Group M] [TopologicalSpace M] [Group C] [TopologicalSpace C]
    [MulOneClass Q] [TopologicalSpace Q] [IsTopologicalGroup C]
    (j : M →* C) (q : M →* Q) (hj : Continuous (j : M → C))
    (hq : Topology.IsQuotientMap (q : M → Q)) {V : Set C} (hV : IsOpen V) :
    IsOpen ((q : M → Q) '' ((j : M → C) ⁻¹' V)) := by
  rw [← hq.isOpen_preimage]
  have hsat :
      (q : M → Q) ⁻¹' ((q : M → Q) '' ((j : M → C) ⁻¹' V)) =
        ⋃ k ∈ (q.ker : Set M), (fun m : M ↦ j m * j k) ⁻¹' V := by
    apply Set.ext
    intro m
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, hqa⟩
      refine ⟨m⁻¹ * a, ?_, ?_⟩
      · apply MonoidHom.mem_ker.mpr
        rw [map_mul, hqa, ← map_mul, inv_mul_cancel, map_one]
      · simpa only [map_mul, map_inv, ← mul_assoc, mul_inv_cancel, one_mul] using ha
    · rintro ⟨k, hk, hmk⟩
      refine ⟨m * k, ?_, ?_⟩
      · simpa only [map_mul] using hmk
      · rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]
  rw [hsat]
  exact isOpen_biUnion fun k _ ↦ hV.preimage (hj.mul_const (j k))

variable {M : Type uM} {C : Type uC} {Q : Type uQ}
  [Group M] [TopologicalSpace M] [Group C] [TopologicalSpace C]
  [MulOneClass Q] [TopologicalSpace Q] [IsTopologicalGroup C]

omit [TopologicalSpace M] in
@[to_additive]
private theorem ker_subset_closure_image_ker_of_denseRange_of_isOpen_image_preimage
    (j : M →* C) (F : C →* Q) (q : M →* Q)
    (hd : DenseRange (j : M → C)) (hF : Continuous (F : C → Q))
    (hcomp : F.comp j = q)
    (hopen : ∀ V : Set C, IsOpen V →
      IsOpen ((q : M → Q) '' ((j : M → C) ⁻¹' V))) :
    (F.ker : Set C) ⊆ closure ((j : M → C) '' (q.ker : Set M)) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro O hO hxO
  have hdiv : IsOpen ((fun p : C × C => p.1 / p.2) ⁻¹' O) :=
    hO.preimage continuous_div'
  obtain ⟨U, V, hU, hxU, hV, h1V, hUV⟩ := mem_nhds_prod_iff'.mp
    (hdiv.mem_nhds (show (x, 1) ∈ (fun p : C × C => p.1 / p.2) ⁻¹' O by
      simpa only [Set.mem_preimage, div_one] using hxO))
  have h1 : (1 : Q) ∈ (q : M → Q) '' ((j : M → C) ⁻¹' V) :=
    ⟨1, by simpa only [Set.mem_preimage, map_one] using h1V, map_one q⟩
  have hP : IsOpen (U ∩ (F : C → Q) ⁻¹' ((q : M → Q) '' ((j : M → C) ⁻¹' V))) :=
    hU.inter ((hopen V hV).preimage hF)
  have hxP : x ∈ U ∩ (F : C → Q) ⁻¹' ((q : M → Q) '' ((j : M → C) ⁻¹' V)) :=
    ⟨hxU, by simpa only [Set.mem_preimage, mem_ker.mp hx] using h1⟩
  obtain ⟨y, hy, hyP⟩ := Dense.exists_mem_open hd hP ⟨x, hxP⟩
  rcases hy with ⟨m, rfl⟩
  rcases hyP with ⟨hmU, a, haV, haQ⟩
  have hqa : q a = q m := haQ.trans (DFunLike.congr_fun hcomp m)
  -- Right correction preserves the order needed in a noncommutative group.
  have hma : m * a⁻¹ ∈ q.ker := by
    apply mem_ker.mpr
    rw [map_mul, ← hqa, ← map_mul, mul_inv_cancel, map_one]
  have hcorr : j m / j a ∈ O :=
    hUV (show (j m, j a) ∈ U ×ˢ V from ⟨hmU, haV⟩)
  refine ⟨j (m * a⁻¹), ?_, m * a⁻¹, hma, rfl⟩
  simpa only [map_mul, map_inv, div_eq_mul_inv] using hcorr

/-- In a dense commuting square of continuous homomorphisms, an open source map
makes the kernel of the extension lie in the closure of the image of the source
kernel. Surjectivity of the open map is not required. -/
@[to_additive /-- In a dense commuting square of continuous additive homomorphisms,
an open source map makes the kernel of the extension lie in the closure of the
image of the source kernel. Surjectivity of the open map is not required. -/]
theorem ker_subset_closure_image_ker_of_denseRange_isOpenMap
    (j : M →* C) (F : C →* Q) (q : M →* Q)
    (hj : Continuous (j : M → C)) (hd : DenseRange (j : M → C))
    (hF : Continuous (F : C → Q)) (hcomp : F.comp j = q)
    (hq : IsOpenMap (q : M → Q)) :
    (F.ker : Set C) ⊆ closure ((j : M → C) '' (q.ker : Set M)) :=
  ker_subset_closure_image_ker_of_denseRange_of_isOpen_image_preimage j F q hd hF hcomp
    fun _ hV => hq _ (hV.preimage hj)

/-- In a dense commuting square of continuous homomorphisms whose source map is
quotient, the kernel of the extension lies in the closure of the image of the
source kernel. Only the intermediate group needs continuous group operations. -/
@[to_additive /-- In a dense commuting square of continuous additive homomorphisms
whose source map is quotient, the kernel of the extension lies in the closure of
the image of the source kernel. Only the intermediate additive group needs
continuous group operations. -/]
theorem ker_subset_closure_image_ker_of_denseRange_isQuotientMap
    (j : M →* C) (F : C →* Q) (q : M →* Q)
    (hj : Continuous (j : M → C)) (hd : DenseRange (j : M → C))
    (hF : Continuous (F : C → Q)) (hcomp : F.comp j = q)
    (hq : Topology.IsQuotientMap (q : M → Q)) :
    (F.ker : Set C) ⊆ closure ((j : M → C) '' (q.ker : Set M)) :=
  ker_subset_closure_image_ker_of_denseRange_of_isOpen_image_preimage j F q hd hF hcomp
    fun V hV => isOpen_image_preimage_of_isQuotientMap j q hj hq (V := V) hV

/-- The kernel of an extension along a continuous dense homomorphism and the
image of the source kernel have the same closure when the source map is quotient.
No closedness of the extension's kernel is assumed. -/
@[to_additive /-- The kernel of an extension along a continuous dense additive
homomorphism and the image of the source kernel have the same closure when the
source map is quotient. No closedness of the extension's kernel is assumed. -/]
theorem closure_ker_eq_closure_image_ker_of_denseRange_isQuotientMap
    (j : M →* C) (F : C →* Q) (q : M →* Q)
    (hj : Continuous (j : M → C)) (hd : DenseRange (j : M → C))
    (hF : Continuous (F : C → Q)) (hcomp : F.comp j = q)
    (hq : Topology.IsQuotientMap (q : M → Q)) :
    closure (F.ker : Set C) = closure ((j : M → C) '' (q.ker : Set M)) := by
  apply le_antisymm
  · exact closure_minimal
      (ker_subset_closure_image_ker_of_denseRange_isQuotientMap j F q hj hd hF hcomp hq)
      isClosed_closure
  · apply closure_mono
    rintro _ ⟨m, hm, rfl⟩
    apply mem_ker.mpr
    exact (DFunLike.congr_fun hcomp m).trans (mem_ker.mp hm)

/-- A closed kernel of an extension along a continuous dense homomorphism is
exactly the closure of the image of the source kernel when the source map is
quotient. Closedness is a separate hypothesis, not a consequence of continuity
into an arbitrary target equipped with a topology. -/
@[to_additive /-- A closed kernel of an extension along a continuous dense
additive homomorphism is exactly the closure of the image of the source kernel
when the source map is quotient. Closedness is a separate hypothesis, not a
consequence of continuity into an arbitrary additive target equipped with a topology. -/]
theorem ker_eq_closure_image_ker_of_denseRange_isQuotientMap
    (j : M →* C) (F : C →* Q) (q : M →* Q)
    (hj : Continuous (j : M → C)) (hd : DenseRange (j : M → C))
    (hF : Continuous (F : C → Q)) (hcomp : F.comp j = q)
    (hq : Topology.IsQuotientMap (q : M → Q)) (hker : IsClosed (F.ker : Set C)) :
    (F.ker : Set C) = closure ((j : M → C) '' (q.ker : Set M)) := by
  rw [← hker.closure_eq]
  exact closure_ker_eq_closure_image_ker_of_denseRange_isQuotientMap j F q hj hd hF hcomp hq

end MonoidHom
