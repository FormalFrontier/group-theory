/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.MulAction
public import GroupTheory.Topology.FiniteIndex
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Automatic continuity of homomorphisms and discrete actions

Let the source be a compact Hausdorff commutative topological group with a specified dense
finitely generated subgroup. An abstract homomorphism to a compact nonarchimedean group is
continuous. The target need not be commutative or Hausdorff, and the homomorphism need not have
finite image. An abstract action of the same source on an arbitrary discrete space is jointly
continuous if each orbit is finite. The additive action counterpart likewise needs no additive
structure on the carrier.

Both proofs use finite-index openness in the source. For homomorphisms, open subgroups of the
compact target have finite index, as do their algebraic comaps, which test continuity at the
identity. For actions, orbit–stabilizer gives finite index of each stabilizer, hence openness and
joint continuity. Finiteness of individual orbits does not require a finite total action image.

## References

The proofs combine `Subgroup.isOpen_of_finiteIndex_of_dense_fg` with Mathlib's compact open-subgroup
coset-finiteness, relative-index comap, nonarchimedean neighborhood-basis, and group-homomorphism
continuity APIs, its orbit–stabilizer equivalence, and the discrete-action stabilizer criterion in
`GroupTheory.Topology.Algebra.MulAction`.
-/

@[expose] public section

open Filter Topology

universe u v

/-- An abstract homomorphism from a compact Hausdorff commutative topological group with a
specified dense finitely generated subgroup to a compact nonarchimedean group is continuous. -/
@[to_additive /-- An abstract additive homomorphism from a compact Hausdorff commutative topological
additive group with a specified dense finitely generated subgroup to a compact nonarchimedean
additive group is continuous. -/]
theorem MonoidHom.continuous_of_dense_fg
    {G : Type u} {H : Type v}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    [Group H] [TopologicalSpace H] [CompactSpace H] [NonarchimedeanGroup H]
    (f : G →* H) (D : Subgroup G) (hD_fg : D.FG) (hD_dense : Dense (D : Set G)) :
    Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  change Tendsto f (𝓝 (1 : G)) (𝓝 (f 1))
  rw [map_one]
  refine Filter.tendsto_def.mpr ?_
  intro W hW
  obtain ⟨U, hUW⟩ := NonarchimedeanGroup.is_nonarchimedean W hW
  let : U.toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  have hU_rel : U.toSubgroup.IsFiniteRelIndex (⊤ : Subgroup H) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hcomap_rel : (U.toSubgroup.comap f).IsFiniteRelIndex (⊤ : Subgroup G) := by
    simpa using Subgroup.IsFiniteRelIndex.comap f hU_rel
  let : (U.toSubgroup.comap f).FiniteIndex :=
    Subgroup.isFiniteRelIndex_top_iff.mp hcomap_rel
  have hopen : IsOpen (U.toSubgroup.comap f : Set G) :=
    Subgroup.isOpen_of_finiteIndex_of_dense_fg D hD_fg hD_dense (U.toSubgroup.comap f)
  exact Filter.mem_of_superset
    (hopen.mem_nhds (show (1 : G) ∈ U.toSubgroup.comap f from
      (U.toSubgroup.comap f).one_mem))
    (fun _ hx => hUW hx)

/-- An abstract action of a compact Hausdorff commutative topological group with a specified
dense finitely generated subgroup on an arbitrary discrete space is jointly continuous if
each orbit is finite. -/
@[to_additive /-- An abstract additive action of a compact Hausdorff commutative
  topological additive group with a specified dense finitely generated subgroup on an arbitrary
  discrete space is jointly
  continuous if each orbit is finite. No additive structure on the carrier is required. -/]
theorem MulAction.continuousSMul_of_finite_orbits_of_dense_fg
    {G : Type u} {β : Type v}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    [TopologicalSpace β] [DiscreteTopology β] [MulAction G β]
    (D : Subgroup G) (hD_fg : D.FG) (hD_dense : Dense (D : Set G))
    (h_orbit : ∀ b : β, (MulAction.orbit G b).Finite) : ContinuousSMul G β := by
  refine MulAction.continuousSMul_iff_stabilizer_isOpen.mpr ?_
  intro b
  let : Finite (MulAction.orbit G b) := (h_orbit b).to_subtype
  let : Finite (G ⧸ MulAction.stabilizer G b) :=
    Finite.of_equiv (MulAction.orbit G b) (MulAction.orbitEquivQuotientStabilizer G b)
  let : (MulAction.stabilizer G b).FiniteIndex :=
    Subgroup.finiteIndex_iff_finite_quotient.mpr inferInstance
  exact Subgroup.isOpen_of_finiteIndex_of_dense_fg D hD_fg hD_dense (MulAction.stabilizer G b)
