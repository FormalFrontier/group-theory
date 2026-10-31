/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Irreducible

/-!
# Actions of preirreducible groups

For a group with a preirreducible topology and continuous inversion, a jointly continuous action
has inseparable orbit points. Conversely, orbitwise inseparability makes the action map continuous
by comparison with the second projection. The target topology is arbitrary, and the domain carries
the ordinary product topology. No continuity of multiplication in the acting group is required.

The necessity argument intersects an open rectangle at the identity with the open inverse-orbit
preimage of its target neighborhood. The converse uses Mathlib's
`continuous_congr_of_inseparable`.
-/

@[expose] public section

universe u v

namespace MulAction

/-- An action of a preirreducible group with continuous inversion is jointly continuous exactly
when every orbit point is inseparable from the point acted on. The target topology is arbitrary. -/
@[to_additive
  /-- An action of a preirreducible additive group with continuous negation is jointly continuous
  exactly when every orbit point is inseparable from the point acted on. The target topology is
  arbitrary. -/]
theorem continuous_smul_iff_inseparable
    {G : Type u} {X : Type v} [Group G] [act : MulAction G X]
    [tG : TopologicalSpace G] [tX : TopologicalSpace X]
    [PreirreducibleSpace G] [ContinuousInv G] :
    Continuous (fun p : G × X => p.1 • p.2) ↔
      ∀ (g : G) (x : X), Inseparable (g • x) x := by
  constructor
  · intro h
    have mem_open : ∀ (g : G) (x : X) (U : Set X), IsOpen U → x ∈ U → g • x ∈ U := by
      intro g x U hU hx
      obtain ⟨N, V, hN, hV, h1, hxV, hsub⟩ :=
        isOpen_prod_iff.mp (hU.preimage h) 1 x
          (show (1 : G) • x ∈ U from by simpa only [one_smul] using hx)
      have hβ : Continuous (fun k : G => k⁻¹ • (g • x)) :=
        h.comp (continuous_inv.prodMk continuous_const)
      have hβV : IsOpen ((fun k : G => k⁻¹ • (g • x)) ⁻¹' V) := hV.preimage hβ
      have hgV : g ∈ (fun k : G => k⁻¹ • (g • x)) ⁻¹' V := by
        simpa only [Set.mem_preimage, inv_smul_smul] using hxV
      obtain ⟨k, hkN, hkV⟩ :=
        nonempty_preirreducible_inter hN hβV ⟨1, h1⟩ ⟨g, hgV⟩
      have hkU : k • (k⁻¹ • (g • x)) ∈ U :=
        hsub (show (k, k⁻¹ • (g • x)) ∈ N ×ˢ V from ⟨hkN, hkV⟩)
      simpa only [smul_inv_smul] using hkU
    intro g x
    refine inseparable_iff_forall_isOpen.mpr fun U hU => ⟨?_, mem_open g x U hU⟩
    intro hgU
    simpa only [inv_smul_smul] using mem_open g⁻¹ (g • x) U hU hgU
  · intro h
    exact (continuous_congr_of_inseparable (fun p : G × X => h p.1 p.2)).mpr continuous_snd

end MulAction
