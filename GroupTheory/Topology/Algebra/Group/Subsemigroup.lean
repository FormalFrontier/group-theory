/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Order.Zorn
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.NoetherianSpace
public import GroupTheory.Topology.ClosedEmbedding

/-!
# Inverse closure of closed subsemigroups

A closed subsemigroup of a group is closed under inverses if fixed left translations
are continuous and its carrier is compact. The same conclusion holds if its induced
topology is Noetherian, or if it is preirreducible and strict inclusion of ambient
irreducible closed subsets is well-founded. The subsemigroup may be empty; no
continuity of right translations or of inversion is needed.

The compact case follows by choosing a minimal nonempty closed right ideal and
considering its left translates. The Noetherian case follows from compactness of the
original subsemigroup, not of the ambient group. The preirreducible case uses
surjectivity of closed self-embeddings with finitely many irreducible components;
well-foundedness transfers to the subsemigroup through the map on irreducible closed
sets induced by its inclusion.

For a submonoid, the same result says that each of its elements is a unit in the
submonoid.

## Acknowledgements

The inverse-closure arguments by minimal left translates and by compactness were
developed by Formal Frontier Agents.
-/

@[expose] public section

universe u

open TopologicalSpace
open scoped Pointwise

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

@[to_additive]
private theorem Subsemigroup.inv_mem_of_isClosed_of_finite_irreducibleComponents
    (S : Subsemigroup G) (hS : IsClosed (S : Set G))
    (hfin : (irreducibleComponents S).Finite)
    [WellFoundedLT (IrreducibleCloseds S)] {a : G} (ha : a ∈ S) : a⁻¹ ∈ S := by
  let f : S → S := fun y => ⟨a * y, S.mul_mem ha y.property⟩
  have hf : Topology.IsClosedEmbedding f :=
    Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
      ((Homeomorph.smul (α := G) a).isClosedEmbedding.comp hS.isClosedEmbedding_subtypeVal)
  have hsurj : Function.Surjective f :=
    hf.surjective_of_finite_irreducibleComponents hfin
  have hshift : (S : Set G) ⊆ a • (S : Set G) := by
    intro y hy
    obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
    exact ⟨(z : G), z.property, congrArg Subtype.val hz⟩
  have hone : (1 : G) ∈ S := by
    simpa only [smul_eq_mul, inv_mul_cancel, SetLike.mem_coe] using
      (Set.mem_smul_set_iff_inv_smul_mem.mp (hshift ha))
  simpa only [smul_eq_mul, mul_one, SetLike.mem_coe] using
    (Set.mem_smul_set_iff_inv_smul_mem.mp (hshift hone))

/-- A closed preirreducible subsemigroup is closed under inverses if strict inclusion
of ambient irreducible closed subsets is well-founded and fixed left translations are
continuous. -/
@[to_additive /-- A closed preirreducible additive subsemigroup is closed under negation
if strict inclusion of ambient irreducible closed subsets is well-founded and fixed left
translations are continuous. -/]
theorem Subsemigroup.inv_mem_of_isClosed_of_isPreirreducible
    [WellFoundedLT (TopologicalSpace.IrreducibleCloseds G)] (S : Subsemigroup G)
    (hS : IsClosed (S : Set G)) (hirr : IsPreirreducible (S : Set G))
    {a : G} (ha : a ∈ S) : a⁻¹ ∈ S := by
  let : IrreducibleSpace S := Subtype.irreducibleSpace ⟨⟨a, ha⟩, hirr⟩
  let : WellFoundedLT (IrreducibleCloseds S) :=
    (IrreducibleCloseds.map_strictMono_of_isInducing
      hS.isClosedEmbedding_subtypeVal.isInducing).wellFoundedLT
  exact S.inv_mem_of_isClosed_of_finite_irreducibleComponents hS
    (by rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _) ha

omit [ContinuousConstSMul G G] in
@[to_additive]
private theorem Subsemigroup.exists_minimal_closed_right_ideal (S : Subsemigroup G)
    (hclosed : IsClosed (S : Set G)) (hcompact : IsCompact (S : Set G))
    (hne : (S : Set G).Nonempty) :
    ∃ I : Set G, Minimal (fun I : Set G => I ⊆ (S : Set G) ∧ IsClosed I ∧ I.Nonempty ∧
      ∀ a ∈ I, ∀ b ∈ S, a * b ∈ I) I := by
  -- A chain of nonempty closed right ideals has the finite-intersection property.
  -- Compactness makes its intersection nonempty, providing the lower bounds for Zorn.
  apply zorn_superset
  intro c hc hchain
  rcases c.eq_empty_or_nonempty with rfl | hcne
  · exact ⟨(S : Set G), ⟨Set.Subset.rfl, hclosed, hne,
      fun _ ha _ hb => S.mul_mem ha hb⟩, by simp⟩
  obtain ⟨J, hJ⟩ := hcne
  have hnonempty : (⋂₀ c).Nonempty := by
    let : Nonempty c := ⟨⟨J, hJ⟩⟩
    apply IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    · intro A hA B hB
      rcases eq_or_ne A B with rfl | hne
      · exact ⟨A, hA, Set.Subset.rfl, Set.Subset.rfl⟩
      · rcases hchain hA hB hne with hAB | hBA
        · exact ⟨A, hA, Set.Subset.rfl, hAB⟩
        · exact ⟨B, hB, hBA, Set.Subset.rfl⟩
    · exact fun A hA => (hc hA).2.2.1
    · exact fun A hA => hcompact.of_isClosed_subset (hc hA).2.1 (hc hA).1
    · exact fun A hA => (hc hA).2.1
  refine ⟨⋂₀ c, ⟨?_, ?_, hnonempty, ?_⟩, ?_⟩
  · exact (Set.sInter_subset_of_mem hJ).trans (hc hJ).1
  · exact isClosed_sInter fun A hA => (hc hA).2.1
  · intro a ha b hb
    exact Set.mem_sInter.mpr fun A hA =>
      (hc hA).2.2.2 a (Set.mem_sInter.mp ha A hA) b hb
  · exact fun A hA => Set.sInter_subset_of_mem hA

/-- A closed compact subsemigroup is closed under inverses, provided fixed left
translations in the ambient group are continuous. -/
@[to_additive /-- A closed compact additive subsemigroup is closed under negation, provided
fixed left translations in the ambient additive group are continuous. -/]
theorem Subsemigroup.inv_mem_of_isClosed_of_isCompact (S : Subsemigroup G)
    (hclosed : IsClosed (S : Set G)) (hcompact : IsCompact (S : Set G))
    {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  obtain ⟨I, ⟨hIS, _, ⟨a, ha⟩, hright⟩, hmin⟩ :=
    S.exists_minimal_closed_right_ideal hclosed hcompact ⟨x, hx⟩
  have htranslate : ∀ b ∈ I, b • (S : Set G) = I := by
    intro b hb
    have hsub : b • (S : Set G) ⊆ I := by
      rintro _ ⟨c, hc, rfl⟩
      exact hright b hb c hc
    -- The right-ideal condition gives bS ⊆ I. Closedness of bS uses only the
    -- homeomorphism given by fixed left translation, not right continuity.
    refine Set.Subset.antisymm hsub (hmin ?_ hsub)
    refine ⟨hsub.trans hIS, hclosed.smul b, ⟨b * x, x, hx, rfl⟩, ?_⟩
    rintro _ ⟨c, hc, rfl⟩ d hd
    exact ⟨c * d, S.mul_mem hc hd, by simp only [smul_eq_mul, mul_assoc]⟩
  have hax : a * x ∈ I := hright a ha x hx
  have hamem : a ∈ (a * x) • (S : Set G) := by
    rw [htranslate (a * x) hax]
    exact ha
  obtain ⟨b, hb, hab⟩ := hamem
  have hab' : a * (x * b) = a * 1 := by
    simpa only [smul_eq_mul, mul_assoc, mul_one] using hab
  have hxb : x * b = 1 := mul_left_cancel hab'
  have hb_inv : b = x⁻¹ := by
    calc
      b = x⁻¹ * (x * b) := by simp only [← mul_assoc, inv_mul_cancel, one_mul]
      _ = x⁻¹ := by rw [hxb, mul_one]
  exact hb_inv ▸ hb

/-- A closed subsemigroup with Noetherian induced topology is closed under inverses,
provided fixed left translations in the ambient group are continuous. -/
@[to_additive /-- A closed additive subsemigroup with Noetherian induced topology is closed
under negation, provided fixed left translations in the ambient group are continuous. -/]
theorem Subsemigroup.inv_mem_of_isClosed_of_noetherianSpace (S : Subsemigroup G)
    (hS : IsClosed (S : Set G)) [NoetherianSpace S] {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  exact S.inv_mem_of_isClosed_of_isCompact hS
    ((noetherianSpace_set_iff (S : Set G)).mp ‹NoetherianSpace S› _ Set.Subset.rfl) hx

/-- Every element of a closed compact submonoid is a unit in that submonoid, provided
fixed left translations in the ambient group are continuous. -/
@[to_additive /-- Every element of a closed compact additive submonoid is an additive unit
in that submonoid, provided fixed left translations in the ambient additive group are
continuous. -/]
theorem Submonoid.isUnit_of_isClosed_of_isCompact (S : Submonoid G)
    (hclosed : IsClosed (S : Set G)) (hcompact : IsCompact (S : Set G)) (x : S) : IsUnit x := by
  have hinv : (x : G)⁻¹ ∈ S :=
    S.toSubsemigroup.inv_mem_of_isClosed_of_isCompact hclosed hcompact x.property
  exact isUnit_iff_exists.mpr
    ⟨⟨(x : G)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel (x : G)),
      Subtype.ext (inv_mul_cancel (x : G))⟩

/-- Every element of a closed submonoid with Noetherian induced topology is a unit
in that submonoid, provided fixed left translations in the ambient group are continuous. -/
@[to_additive /-- Every element of a closed additive submonoid with Noetherian induced topology
is an additive unit in that submonoid, provided fixed left translations in the ambient group
are continuous. -/]
theorem Submonoid.isUnit_of_isClosed_of_noetherianSpace (S : Submonoid G)
    (hS : IsClosed (S : Set G)) [NoetherianSpace S] (x : S) : IsUnit x := by
  exact S.isUnit_of_isClosed_of_isCompact hS
    ((noetherianSpace_set_iff (S : Set G)).mp ‹NoetherianSpace S› _ Set.Subset.rfl) x
