/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Total boundedness from a subgroup neighborhood basis

A left-uniform group with a basis of subgroups at the identity is totally bounded
exactly when every subgroup occurring in the basis has finite index. The additive
version applies in particular to ideal-power neighborhood bases in topological rings.
The uniformity and its induced topology are the given ones; no normality or
separation assumption is needed.

## Implementation notes

The left-uniform compatibility relates identity neighborhoods to entourages via
`(x, y) ↦ x⁻¹ * y`. Finite coset covers express finite index without placing a
topology on the quotient. Full uniform continuity of the group operations is not
required. The index type and its predicate are arbitrary.

The finite-index condition cannot be dropped: in the discrete additive group of
integers, the zero subgroup is a neighborhood basis by itself, but its quotient is
infinite and the group is not totally bounded.

## References

* Mathlib's `uniformity_eq_comap_inv_mul_nhds_one`, `Filter.HasBasis.comap` and
  `Filter.HasBasis.totallyBounded_iff` give the uniform-space approach.
* Mathlib's `QuotientGroup.univ_eq_iUnion_smul` and
  `Subgroup.finiteIndex_iff_finite_quotient` give the algebraic coset interfaces.
-/

@[expose] public section

open scoped Topology

universe u v

namespace Filter.HasBasis

/-- A left-uniform group with a subgroup basis at the identity is totally bounded
if and only if every subgroup in that basis has finite index. -/
@[to_additive
/-- A left-uniform additive group with an additive-subgroup basis at zero is
totally bounded if and only if every additive subgroup in that basis has finite index. -/]
theorem totallyBounded_univ_iff_subgroup_finiteIndex
    {G : Type u} [Group G] [UniformSpace G] [IsLeftUniformGroup G]
    {ι : Type v} {p : ι → Prop} {H : ι → Subgroup G}
    (B : (nhds (1 : G)).HasBasis p (fun i => (H i : Set G))) :
    TotallyBounded (Set.univ : Set G) ↔ ∀ i, p i → (H i).FiniteIndex := by
  classical
  have U : (uniformity G).HasBasis p
      (fun i => {z : G × G | z.1⁻¹ * z.2 ∈ H i}) := by
    rw [uniformity_eq_comap_inv_mul_nhds_one]
    exact B.comap _
  rw [U.totallyBounded_iff]
  constructor
  · intro h i hi
    obtain ⟨t, ht, hcover⟩ := h i hi
    apply (Subgroup.finiteIndex_iff_finite_quotient (H := H i)).2
    apply Set.finite_univ_iff.1
    refine (ht.image (fun x : G => (x : G ⧸ H i))).subset ?_
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover (Set.mem_univ x))
    -- The entourage condition is equality of left cosets, with the opposite orientation.
    exact ⟨y, hy, ((QuotientGroup.eq (s := H i)).2 hxy).symm⟩
  · intro h i hi
    let : Finite (G ⧸ H i) :=
      (Subgroup.finiteIndex_iff_finite_quotient (H := H i)).1 (h i hi)
    refine ⟨(fun q : G ⧸ H i => q.out) '' Set.univ,
      Set.finite_univ.image _, ?_⟩
    intro x _
    apply Set.mem_iUnion₂.2
    refine ⟨(x : G ⧸ H i).out, ⟨(x : G ⧸ H i), Set.mem_univ _, rfl⟩, ?_⟩
    exact QuotientGroup.eq.1 (QuotientGroup.out_eq' (x : G ⧸ H i)).symm

end Filter.HasBasis
