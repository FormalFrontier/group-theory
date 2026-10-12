/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Submonoid.Finite
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Constructions

/-!
# Finite cylinders inside open normal subgroups of products

Every open normal subgroup of a product contains a cylinder determined by open
normal subgroups in finitely many factors. The index type is arbitrary, and the
factor topologies need not make the group operations continuous. For a constant
family, one open normal subgroup controls all the selected coordinates.

The finite set is retained in the containment statements: coordinates outside
it are unrestricted. These cylinders are open in the product topology, whereas
a subgroup imposing the same proper constraint on infinitely many coordinates
need not be open.

## References

- Mathlib, `Mathlib.Topology.Algebra.OpenSubgroup`, for continuous pullbacks and
  finite intersections of open subgroups.
- Mathlib, `Mathlib.Algebra.Group.Pi.Lemmas`,
  `Mathlib.Topology.Constructions`, and `Mathlib.Order.Filter.Pi`, for coordinate
  embeddings and finite-supported product neighborhoods.
- Monica Omar's finite-supported product-membership API in
  `Mathlib.Algebra.Group.Submonoid.Finite`, in particular
  `Submonoid.pi_mem_of_mulSingle_mem_aux`, which also applies to subgroups.
-/

@[expose] public section

namespace OpenNormalSubgroup

universe uI uG

/-- An open normal subgroup of a dependent product contains a cylinder defined
by open normal subgroups in finitely many factors. No continuity of the group
operations is required. The selected finite set may be empty. -/
theorem exists_finset_pi_subset
    {I : Type uI} {A : I → Type uG} [∀ i, Group (A i)]
    [∀ i, TopologicalSpace (A i)] (M : OpenNormalSubgroup (∀ i, A i)) :
    ∃ (s : Finset I) (N : ∀ i : s, OpenNormalSubgroup (A i)),
      ∀ x : (∀ i, A i), (∀ i : s, x i ∈ N i) → x ∈ M := by
  classical
  have hM := M.toOpenSubgroup.mem_nhds_one
  rw [nhds_pi, Filter.mem_pi'] at hM
  obtain ⟨s, U, hU, hUM⟩ := hM
  -- Coordinate insertion is continuous even without continuous group operations.
  let N : ∀ i : s, OpenNormalSubgroup (A i) := fun i =>
    { toOpenSubgroup := M.toOpenSubgroup.comap (MonoidHom.mulSingle A (i : I))
        (continuous_mulSingle (A := A) (i : I))
      isNormal' := M.isNormal'.comap (MonoidHom.mulSingle A (i : I)) }
  refine ⟨s, N, ?_⟩
  intro x hx
  -- Separate the finitely supported part from the unrestricted tail.
  have ht : s.piecewise x 1 ∈ M := by
    refine Submonoid.pi_mem_of_mulSingle_mem_aux s (s.piecewise x 1) ?_ ?_
    · intro i hi
      simp [hi]
    · intro i hi
      have hiM : Pi.mulSingle i (x i) ∈ M := hx ⟨i, hi⟩
      simpa only [Finset.piecewise_eq_of_mem s x 1 hi] using hiM
  have hr : s.piecewise (1 : ∀ i, A i) x ∈ M := by
    apply hUM
    intro i hi
    rw [Finset.piecewise_eq_of_mem s (1 : ∀ i, A i) x (Finset.mem_coe.mp hi)]
    exact mem_of_mem_nhds (hU i)
  have hx_eq : x = s.piecewise x 1 * s.piecewise (1 : ∀ i, A i) x := by
    ext i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [hx_eq]
  exact mul_mem ht hr

/-- An open normal subgroup of a power contains a finite cylinder using one
open normal subgroup of the factor group on every selected coordinate.
Coordinates outside the selected finite set remain unrestricted. -/
theorem exists_finset_uniform_pi_subset
    {I : Type uI} {G : Type uG} [Group G] [TopologicalSpace G]
    (M : OpenNormalSubgroup (I → G)) :
    ∃ (s : Finset I) (N : OpenNormalSubgroup G),
      ∀ x : I → G, (∀ i : s, x i ∈ N) → x ∈ M := by
  obtain ⟨s, N, hN⟩ := exists_finset_pi_subset M
  -- The finite intersection is the whole group when the selected set is empty.
  let K : OpenNormalSubgroup G :=
    { toOpenSubgroup := OpenSubgroup.iInfOfFinite (fun i : s => (N i).toOpenSubgroup)
      isNormal' := Subgroup.normal_iInf_normal (fun i : s => (N i).isNormal') }
  refine ⟨s, K, ?_⟩
  intro x hx
  apply hN x
  intro i
  exact OpenSubgroup.iInfOfFinite_le (fun j : s => (N j).toOpenSubgroup) i (hx i)

end OpenNormalSubgroup
