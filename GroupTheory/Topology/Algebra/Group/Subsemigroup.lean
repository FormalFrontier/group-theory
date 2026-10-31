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
# Inverse closure of closed subsemigroups

A closed subsemigroup of a group is closed under inverses if fixed left translations
are continuous and either its induced topology is Noetherian, or it is preirreducible
and strict inclusion of ambient irreducible closed subsets is well-founded. The
subsemigroup may be empty; no continuity of right translations or of inversion is needed.

Both proofs choose a minimal closed left translate among the translates by natural
powers of a fixed element. Multiplication closure makes consecutive translates nested,
and minimality then allows cancellation. The Noetherian condition is required only on
the original subsemigroup, not on the ambient group. In the preirreducible case, the
translates are irreducible closed subsets of the ambient group.

For a submonoid, the same result says that each of its elements is a unit in the
submonoid.

## Acknowledgements

The descending-translate argument is due to Flint.
-/

@[expose] public section

universe u

open TopologicalSpace
open scoped Pointwise

variable {G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

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
  classical
  let C : ℕ → IrreducibleCloseds G := fun n =>
    ⟨(fun y : G => a ^ n * y) '' (S : Set G),
      ⟨⟨a ^ n * a, a, ha, rfl⟩,
        hirr.image _ (continuous_const_smul (a ^ n)).continuousOn⟩,
      isClosedMap_smul (a ^ n) (S : Set G) hS⟩
  have hstep (n : ℕ) : C (n + 1) ≤ C n := by
    rintro y ⟨z, hz, hy⟩
    exact ⟨a * z, S.mul_mem ha hz, by simpa only [pow_succ, mul_assoc] using hy⟩
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ :=
    (wellFounded_lt : WellFounded ((· < ·) : IrreducibleCloseds G →
      IrreducibleCloseds G → Prop)).has_min (Set.range C) (Set.range_nonempty C)
  have heq : C (n + 1) = C n := by
    apply le_antisymm (hstep n)
    by_contra h
    exact hn _ ⟨n + 1, rfl⟩ (lt_of_le_not_ge (hstep n) h)
  have hshift : (S : Set G) ⊆ a • (S : Set G) := by
    apply (Set.smul_set_subset_smul_set_iff (a := a ^ n)).mp
    have hle : C n ≤ C (n + 1) := le_of_eq heq.symm
    change a ^ n • (S : Set G) ⊆ a ^ (n + 1) • (S : Set G) at hle
    simpa only [pow_succ, mul_smul] using hle
  have hone : (1 : G) ∈ S := by
    simpa only [smul_eq_mul, inv_mul_cancel, SetLike.mem_coe] using
      (Set.mem_smul_set_iff_inv_smul_mem.mp (hshift ha))
  simpa only [smul_eq_mul, mul_one, SetLike.mem_coe] using
    (Set.mem_smul_set_iff_inv_smul_mem.mp (hshift hone))

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
  have hshift : (S : Set G) ⊆ x • (S : Set G) := by
    intro y hy
    have hyC : (⟨x ^ n * y, hmul n hy⟩ : S) ∈ C n := ⟨y, hy, rfl⟩
    rw [← heq] at hyC
    obtain ⟨z, hz, hz_eq⟩ := hyC
    have hz_eq' : x ^ n * (x * z) = x ^ n * y := by
      simpa only [pow_succ, mul_assoc] using hz_eq
    exact ⟨z, hz, mul_left_cancel hz_eq'⟩
  have hone : (1 : G) ∈ S := by
    simpa only [smul_eq_mul, inv_mul_cancel, SetLike.mem_coe] using
      (Set.mem_smul_set_iff_inv_smul_mem.mp (hshift hx))
  simpa only [smul_eq_mul, mul_one, SetLike.mem_coe] using
    (Set.mem_smul_set_iff_inv_smul_mem.mp (hshift hone))

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
