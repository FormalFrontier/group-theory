/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Units
public import GroupTheory.Topology.ContinuousMap.CompactOpen

/-!
# Compact-open continuity of lifting homomorphisms to units

The existing lift of a continuous monoid homomorphism from a group to a monoid is
continuous as a map of homomorphism spaces if either the source or the canonical units
space is R1. The source needs only continuous inversion for this assertion. In particular,
it holds for every topological source group with an arbitrarily topologized target
monoid, or for every topological target monoid with no separation assumption.

The argument uses the embedding of units into the product of the monoid and its
multiplicative opposite. Its two function-space coordinates are fixed postcomposition
and precomposition maps; no joint evaluation map or local compactness is used. The units
construction and the induced topologies on continuous homomorphism spaces are unchanged
from Mathlib and the imported units API.
-/

@[expose] public section

open Topology

universe u v

namespace ContinuousMonoidHom

section

variable {G : Type u} {D : Type v} [Group G] [TopologicalSpace G] [ContinuousInv G]
  [Monoid D] [TopologicalSpace D]

private theorem continuous_toHomUnits_of_postcomp_prod
    (hPostcomp : ∀ (j₁ : C(Dˣ, D)) (j₂ : C(Dˣ, Dᵐᵒᵖ)),
      IsEmbedding (fun a => (j₁ a, j₂ a)) →
      IsEmbedding (fun h : C(G, Dˣ) => (j₁.comp h, j₂.comp h))) :
    Continuous (fun f : G →ₜ* D => f.toHomUnits) := by
  let j₁ : C(Dˣ, D) := ⟨Units.val, Units.continuous_val⟩
  let j₂ : C(Dˣ, Dᵐᵒᵖ) :=
    ⟨fun a => MulOpposite.op ((a⁻¹ : Dˣ) : D),
      Units.isEmbedding_embedProduct.continuous.snd⟩
  have hj : IsEmbedding (fun a : Dˣ => (j₁ a, j₂ a)) :=
    Units.isEmbedding_embedProduct
  have hJ := hPostcomp j₁ j₂ hj
  let inversion : C(G, G) := ⟨Inv.inv, continuous_inv⟩
  let op : C(D, Dᵐᵒᵖ) := ⟨MulOpposite.op, MulOpposite.continuous_op⟩
  have hcoe : Continuous (fun f : G →ₜ* D => (f : C(G, D))) :=
    continuous_induced_dom
  have h₂ : Continuous (fun f : G →ₜ* D => op.comp ((f : C(G, D)).comp inversion)) :=
    (ContinuousMap.continuous_postcomp op).comp
      ((ContinuousMap.continuous_precomp inversion).comp hcoe)
  apply continuous_induced_rng.mpr
  apply hJ.isInducing.continuous_iff.mpr
  change Continuous (fun f : G →ₜ* D =>
    (j₁.comp (f.toHomUnits : C(G, Dˣ)), j₂.comp (f.toHomUnits : C(G, Dˣ))))
  convert hcoe.prodMk h₂ using 1
  funext f
  apply Prod.ext <;> ext g
  · simp [j₁]
  · change MulOpposite.op (((f.toHomUnits g)⁻¹ : Dˣ) : D) =
        MulOpposite.op (f g⁻¹)
    simp

/-- Lifting continuous monoid homomorphisms from a group to units is continuous in the
compact-open topology whenever the canonical units space is R1. No local compactness or
continuity of multiplication is required. -/
theorem continuous_toHomUnits_of_r1Space [R1Space Dˣ] :
    Continuous (fun f : G →ₜ* D => f.toHomUnits) := by
  apply continuous_toHomUnits_of_postcomp_prod
  intro j₁ j₂ hj
  exact ContinuousMap.isEmbedding_postcomp_prod j₁ j₂ hj

/-- For a topological monoid, lifting continuous monoid homomorphisms from a group to
units is continuous in the compact-open topology, with no separation assumption on the
monoid. -/
theorem continuous_toHomUnits_of_continuousMul [ContinuousMul D] :
    Continuous (fun f : G →ₜ* D => f.toHomUnits) :=
  continuous_toHomUnits_of_r1Space

/-- Lifting continuous monoid homomorphisms from an R1 group with continuous inversion
to units is continuous in the compact-open topology. Neither source multiplication
continuity nor any separation or multiplication continuity of the target is required. -/
theorem continuous_toHomUnits_of_r1Space_domain [R1Space G] :
    Continuous (fun f : G →ₜ* D => f.toHomUnits) := by
  apply continuous_toHomUnits_of_postcomp_prod
  intro j₁ j₂ hj
  exact ContinuousMap.isEmbedding_postcomp_prod_of_r1Space_domain j₁ j₂ hj

end

variable {G : Type u} {D : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Monoid D] [TopologicalSpace D]

/-- Lifting continuous monoid homomorphisms from a topological group to units is
continuous in the compact-open topology for any topologized monoid. No separation
assumption or continuity of target multiplication is required. -/
theorem continuous_toHomUnits_of_isTopologicalGroup :
    Continuous (fun f : G →ₜ* D => f.toHomUnits) :=
  continuous_toHomUnits_of_r1Space_domain

end ContinuousMonoidHom
