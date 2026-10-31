/-
SPDX-License-Identifier: Apache-2.0
-/

module

public import GroupTheory.Topology.Algebra.Group.Subsemigroup
public import Mathlib.Topology.ContinuousOn

/-!
# Inverse closure of a subsemigroup's topological closure

The closure of a subsemigroup is stable under multiplication if fixed left
multiplications are continuous and right multiplication by each member of the
subsemigroup is continuous on its closure. If the closure has Noetherian induced
topology, the closed-subsemigroup inverse theorem then makes it stable under inverses.

Only the original right factors in the subsemigroup need the stated continuity.
Neither ambient Noetherianity nor continuity of inversion is required.
-/

@[expose] public section

universe u

open TopologicalSpace

namespace Subsemigroup

private theorem mul_mem_closure_of_continuousOn_right
    {M : Type u} [Mul M] [TopologicalSpace M]
    (S : Subsemigroup M)
    (hL : ∀ x ∈ _root_.closure (S : Set M),
      ContinuousOn (fun t : M => x * t) (_root_.closure (S : Set M)))
    (hR : ∀ s ∈ S, ContinuousOn (fun x : M => x * s) (_root_.closure (S : Set M)))
    {x y : M} (hx : x ∈ _root_.closure (S : Set M)) (hy : y ∈ _root_.closure (S : Set M)) :
    x * y ∈ _root_.closure (S : Set M) := by
  have hright : ∀ s ∈ S, x * s ∈ _root_.closure (S : Set M) := by
    intro s hs
    refine closure_minimal ?_ isClosed_closure ((hR s hs).image_closure ?_)
    · rintro _ ⟨t, ht, rfl⟩
      exact _root_.subset_closure (S.mul_mem ht hs)
    · exact ⟨x, hx, rfl⟩
  have hleft := hL x hx
  refine closure_minimal ?_ isClosed_closure (hleft.image_closure ?_)
  · rintro _ ⟨s, hs, rfl⟩
    exact hright s hs
  · exact ⟨y, hy, rfl⟩

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

/-- The topological closure of a subsemigroup is closed under inverses if its induced
 topology is Noetherian and right multiplication by each original member is continuous
 on the closure. Fixed left multiplications are continuous in the given regular action. -/
theorem inv_mem_closure_of_noetherianSpace (S : Subsemigroup G)
    (hR : ∀ s ∈ S, ContinuousOn (fun x : G => x * s) (_root_.closure (S : Set G)))
    [NoetherianSpace {x : G // x ∈ _root_.closure (S : Set G)}]
    {x : G} (hx : x ∈ _root_.closure (S : Set G)) : x⁻¹ ∈ _root_.closure (S : Set G) := by
  let T : Subsemigroup G :=
    { carrier := _root_.closure (S : Set G)
      mul_mem' := fun ha hb =>
        mul_mem_closure_of_continuousOn_right S
          (fun x _ => (continuous_id.const_smul x).continuousOn) hR ha hb }
  exact T.inv_mem_of_isClosed_of_noetherianSpace isClosed_closure hx

end Subsemigroup
