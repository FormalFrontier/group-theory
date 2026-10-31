/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.NoetherianSpace

/-!
# Closed Noetherian subsemigroups

A closed subsemigroup of a group is closed under inverses if its induced topology is
Noetherian and fixed left translations are continuous. The subsemigroup may be empty;
no continuity of right translations or of inversion is needed.

The proof chooses a minimal closed left translate among the translates by natural
powers of a fixed element. Multiplication closure makes consecutive translates nested,
and minimality then allows cancellation. Noetherianity is required only on the original
subsemigroup, not on the ambient group.

For a submonoid, the same result says that each of its elements is a unit in the
submonoid.

## Acknowledgements

The descending-translate argument is due to Flint.
-/

@[expose] public section

universe u

open TopologicalSpace

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

/-- A closed subsemigroup with Noetherian induced topology is closed under inverses,
provided fixed left translations in the ambient group are continuous. -/
@[to_additive /-- A closed additive subsemigroup with Noetherian induced topology is closed
under negation, provided fixed left translations in the ambient group are continuous. -/]
theorem Subsemigroup.inv_mem_of_isClosed_of_noetherianSpace (S : Subsemigroup G)
    (hS : IsClosed (S : Set G)) [NoetherianSpace S] {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  classical
  let C : ℕ → Closeds S := fun n =>
    ⟨(Subtype.val : S → G) ⁻¹' ((fun y : G => x ^ n * y) '' (S : Set G)),
      (isClosedMap_smul (x ^ n) (S : Set G) hS).preimage continuous_subtype_val⟩
  have hstep (n : ℕ) : C (n + 1) ≤ C n := by
    rintro y ⟨z, hz, hy⟩
    exact ⟨x * z, S.mul_mem hx hz, by simpa only [pow_succ, mul_assoc] using hy⟩
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    (wellFounded_lt : WellFounded ((· < ·) : Closeds S → Closeds S → Prop)).has_min
      (Set.range C) (Set.range_nonempty C)
  have heq : C (n + 1) = C n := by
    apply le_antisymm (hstep n)
    by_contra h
    exact hn _ ⟨n + 1, rfl⟩ (lt_of_le_not_ge (hstep n) h)
  have hmul (k : ℕ) {y : G} (hy : y ∈ S) : x ^ k * y ∈ S := by
    induction k with
    | zero => simpa only [pow_zero, one_mul] using hy
    | succ k ih => simpa only [pow_succ', mul_assoc] using S.mul_mem hx ih
  have hsurj {y : G} (hy : y ∈ S) : ∃ z ∈ S, x * z = y := by
    have hyC : (⟨x ^ n * y, hmul n hy⟩ : S) ∈ C n := ⟨y, hy, rfl⟩
    rw [← heq] at hyC
    obtain ⟨z, hz, hz_eq⟩ := hyC
    have hz_eq' : x ^ n * (x * z) = x ^ n * y := by
      simpa only [pow_succ, mul_assoc] using hz_eq
    exact ⟨z, hz, mul_left_cancel hz_eq'⟩
  obtain ⟨y, hy, hxy⟩ := hsurj hx
  have hy_one : y = 1 := mul_left_cancel (hxy.trans (mul_one x).symm)
  have hone : (1 : G) ∈ S := by simpa only [hy_one] using hy
  obtain ⟨z, hz, hxz⟩ := hsurj hone
  have hz_inv : z = x⁻¹ := mul_left_cancel (hxz.trans (mul_inv_cancel x).symm)
  simpa only [hz_inv] using hz

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
