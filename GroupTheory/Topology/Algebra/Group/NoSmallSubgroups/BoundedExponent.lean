/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Compactness.Compact

/-!
# Bounded-exponent groups with no small subgroups

A group with continuous multiplication, no small subgroups and a uniform positive exponent
is discrete. If it is also compact, it is finite. No continuity of inversion is needed:
continuity of the finitely many power maps isolates the identity, and fixed translations
then isolate every point.
-/

@[expose] public section

open Filter Topology

universe u

variable {G : Type u} [Group G]

private theorem zpowers_subset_of_pow_eq_one
    {g : G} {n : ℕ} (hn : n ≠ 0) (hpow : g ^ n = 1)
    {U : Set G} (hU : ∀ k : Fin n, g ^ (k : ℕ) ∈ U) :
    (Subgroup.zpowers g : Set G) ⊆ U := by
  have hg : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨n, Nat.pos_of_ne_zero hn, hpow⟩
  intro y hy
  obtain ⟨k, rfl⟩ := hg.mem_powers_iff_mem_zpowers.mpr hy
  change g ^ k ∈ U
  rw [pow_eq_pow_mod k hpow]
  exact hU ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩

variable [TopologicalSpace G] [ContinuousMul G]

private theorem eventually_pow_mem_nhds_one {U : Set G}
    (hU : U ∈ 𝓝 (1 : G)) (n : ℕ) :
    ∀ᶠ g in 𝓝 (1 : G), ∀ k : Fin n, g ^ (k : ℕ) ∈ U := by
  apply Filter.eventually_all.2
  intro k
  have hk : ContinuousAt (fun g : G => g ^ (k : ℕ)) (1 : G) :=
    (continuous_pow (k : ℕ)).continuousAt
  exact hk.preimage_mem_nhds (by simpa only [one_pow] using hU)

variable [NoSmallSubgroups G]

/-- An NSS group with continuous multiplication and a uniform positive exponent is discrete. -/
theorem NoSmallSubgroups.discreteTopology_of_pow_eq_one
    (n : ℕ) (hn : n ≠ 0) (hpow : ∀ g : G, g ^ n = 1) :
    DiscreteTopology G := by
  obtain ⟨U, hU, hNSS⟩ := noSmallSubgroups_iff.mp ‹NoSmallSubgroups G›
  apply discreteTopology_iff_isOpen_singleton_one.2
  refine isOpen_iff_mem_nhds.2 ?_
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  filter_upwards [eventually_pow_mem_nhds_one hU n] with g hg
  have hz := hNSS (Subgroup.zpowers g) (zpowers_subset_of_pow_eq_one hn (hpow g) hg)
  simpa only [Set.mem_singleton_iff, hz, Subgroup.mem_bot] using Subgroup.mem_zpowers g

variable [CompactSpace G]

/-- A compact NSS group with continuous multiplication and a uniform positive exponent is finite. -/
theorem NoSmallSubgroups.finite_of_pow_eq_one
    (n : ℕ) (hn : n ≠ 0) (hpow : ∀ g : G, g ^ n = 1) :
    Finite G := by
  let : DiscreteTopology G := NoSmallSubgroups.discreteTopology_of_pow_eq_one n hn hpow
  exact finite_of_compact_of_discrete
