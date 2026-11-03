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
continuous as a map of homomorphism spaces if the canonical units space is R1. In
particular, this holds for every topological monoid, without a separation assumption.

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

variable {G : Type u} {D : Type v} [Group G] [TopologicalSpace G] [ContinuousInv G]
  [Monoid D] [TopologicalSpace D]

/-- Lifting continuous monoid homomorphisms from a group to units is continuous in the
compact-open topology whenever the canonical units space is R1. No local compactness or
continuity of multiplication is required. -/
theorem continuous_toHomUnits_of_r1Space [R1Space Dˣ] :
    Continuous (fun f : G →ₜ* D => f.toHomUnits) := by
  let j₁ : C(Dˣ, D) := ⟨Units.val, Units.continuous_val⟩
  let j₂ : C(Dˣ, Dᵐᵒᵖ) :=
    ⟨fun a => MulOpposite.op ((a⁻¹ : Dˣ) : D),
      Units.isEmbedding_embedProduct.continuous.snd⟩
  have hj : IsEmbedding (fun a : Dˣ => (j₁ a, j₂ a)) :=
    Units.isEmbedding_embedProduct
  have hJ := ContinuousMap.isEmbedding_postcomp_prod (X := G) j₁ j₂ hj
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

/-- For a topological monoid, lifting continuous monoid homomorphisms from a group to
units is continuous in the compact-open topology, with no separation assumption on the
monoid. -/
theorem continuous_toHomUnits_of_continuousMul [ContinuousMul D] :
    Continuous (fun f : G →ₜ* D => f.toHomUnits) :=
  continuous_toHomUnits_of_r1Space

end ContinuousMonoidHom
