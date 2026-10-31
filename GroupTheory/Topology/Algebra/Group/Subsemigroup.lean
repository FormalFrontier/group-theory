/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.NoetherianSpace
public import GroupTheory.Topology.ClosedEmbedding

/-!
# Inverse closure of closed subsemigroups

A closed subsemigroup of a group is closed under inverses if fixed left translations
are continuous and either its induced topology is Noetherian, or it is preirreducible
and strict inclusion of ambient irreducible closed subsets is well-founded. The
subsemigroup may be empty; no continuity of right translations or of inversion is needed.

Both results follow by restricting a fixed left translation to the closed subsemigroup
and applying surjectivity of closed self-embeddings with finitely many irreducible
components. The Noetherian condition is required only on the original subsemigroup,
not on the ambient group. In the preirreducible case, well-foundedness transfers to
the subsemigroup through the map on irreducible closed sets induced by its inclusion.

For a submonoid, the same result says that each of its elements is a unit in the
submonoid.

## Acknowledgements

The inverse-closure argument by minimal left translates is due to Flint.
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

/-- A closed subsemigroup with Noetherian induced topology is closed under inverses,
provided fixed left translations in the ambient group are continuous. -/
@[to_additive /-- A closed additive subsemigroup with Noetherian induced topology is closed
under negation, provided fixed left translations in the ambient group are continuous. -/]
theorem Subsemigroup.inv_mem_of_isClosed_of_noetherianSpace (S : Subsemigroup G)
    (hS : IsClosed (S : Set G)) [NoetherianSpace S] {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  let : WellFoundedLT (IrreducibleCloseds S) :=
    (show StrictMono (fun C : IrreducibleCloseds S =>
      (⟨(C : Set S), C.isClosed⟩ : Closeds S)) from fun _ _ h => h).wellFoundedLT
  exact S.inv_mem_of_isClosed_of_finite_irreducibleComponents hS
    NoetherianSpace.finite_irreducibleComponents hx

/-- Every element of a closed submonoid with Noetherian induced topology is a unit
in that submonoid, provided fixed left translations in the ambient group are continuous. -/
@[to_additive /-- Every element of a closed additive submonoid with Noetherian induced topology
is an additive unit in that submonoid, provided fixed left translations in the ambient group
are continuous. -/]
theorem Submonoid.isUnit_of_isClosed_of_noetherianSpace (S : Submonoid G)
    (hS : IsClosed (S : Set G)) [NoetherianSpace S] (x : S) : IsUnit x := by
  have hinv : (x : G)⁻¹ ∈ S :=
    S.toSubsemigroup.inv_mem_of_isClosed_of_noetherianSpace hS x.property
  exact isUnit_iff_exists.mpr
    ⟨⟨(x : G)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel (x : G)),
      Subtype.ext (inv_mul_cancel (x : G))⟩
