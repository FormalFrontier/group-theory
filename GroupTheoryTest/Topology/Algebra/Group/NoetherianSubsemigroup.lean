/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory

/-!
# A subgroup from a closed Noetherian subsemigroup

For a nonempty closed Noetherian subsemigroup, inverse closure supplies the division
closure needed by `Subgroup.ofDiv`. The resulting subgroup has the original carrier,
so its identity and inverse membership API apply to the original subsemigroup.
-/

@[expose] public section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

example (S : Subsemigroup G) (hS : IsClosed (S : Set G))
    [TopologicalSpace.NoetherianSpace S] (hne : (S : Set G).Nonempty) :
    (1 : G) ∈ S ∧ ∀ x ∈ S, x⁻¹ ∈ S := by
  let H := Subgroup.ofDiv (S : Set G) hne fun a ha b hb =>
    S.mul_mem ha (S.inv_mem_of_isClosed_of_noetherianSpace hS hb)
  have hcarrier : (H : Set G) = (S : Set G) := rfl
  have hmem (x : G) : x ∈ H ↔ x ∈ S := Set.ext_iff.mp hcarrier x
  constructor
  · exact (hmem 1).mp H.one_mem
  · intro x hx
    exact (hmem x⁻¹).mp (H.inv_mem ((hmem x).mpr hx))
