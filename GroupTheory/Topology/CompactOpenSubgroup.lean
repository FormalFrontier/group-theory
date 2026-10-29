/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Compact open subgroups of totally disconnected locally compact groups

The left-translation stabilizer of any compact open set is an open subgroup. When the set
contains the identity, the stabilizer is compact and contained in it. Such subgroups form
an identity-neighborhood basis in a totally disconnected locally compact topological group.
No ambient compactness or separation assumption is needed for the stabilizer construction.
The corresponding additive constructions and nonarchimedean group constructors are included.

## References

* Van Dantzig's compact-open subgroup theorem, used by Neukirch, Schmidt, and Wingberg,
  *Cohomology of Number Fields*, Chapter I, §1, in the identity-component discussion.
* Mathlib's `OpenSubgroup`, `MulAction.stabilizer`, `compact_open_separated_mul_left`,
  `exists_compact_subset`, and `loc_compact_Haus_tot_disc_of_zero_dim` provide the
  underlying algebraic and topological interfaces.

The stabilizer argument independently assembles these ingredients; it does not transcribe
either of the other works cited for the theorem in the source.
-/

@[expose] public section

open Filter
open scoped Pointwise Topology

universe u

namespace OpenSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The open subgroup fixing a compact open set by left translation.
Its carrier agrees with Mathlib's action stabilizer of the underlying set. -/
@[to_additive /-- The open additive subgroup fixing a compact open set by translation.
Its carrier agrees with the additive-action stabilizer of the underlying set. -/]
def leftStabilizer [IsTopologicalGroup G] (K : Set G) (hK : IsCompact K)
    (hK_open : IsOpen K) : OpenSubgroup G where
  toSubgroup := MulAction.stabilizer G K
  isOpen' := by
    obtain ⟨V, hV, hVK⟩ := compact_open_separated_mul_left hK hK_open (Set.Subset.rfl)
    have hmul (g : G) (hg : g ∈ V) : g • K ⊆ K :=
      (Set.smul_set_subset_mul hg).trans hVK
    apply Subgroup.isOpen_of_mem_nhds (MulAction.stabilizer G K)
    refine Filter.mem_of_superset (Filter.inter_mem hV (inv_mem_nhds_one G hV)) ?_
    intro g hg
    change g ∈ MulAction.stabilizer G K
    rw [MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm (hmul g hg.1)
    exact Set.subset_smul_set_iff.mpr (hmul g⁻¹ (Set.mem_inv.mp hg.2))

/-- Membership in the left-translation stabilizer means preserving the set exactly. -/
@[to_additive (attr := simp) /-- Membership in the additive translation stabilizer means
preserving the set exactly. -/]
theorem mem_leftStabilizer_iff [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) (hK_open : IsOpen K) {g : G} :
    g ∈ leftStabilizer K hK hK_open ↔ g • K = K :=
  MulAction.mem_stabilizer_iff

/-- The translation stabilizer of an identity-containing set lies in that set. -/
@[to_additive /-- The translation stabilizer of a zero-containing set lies in that set. -/]
theorem leftStabilizer_subset [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) (hK_open : IsOpen K)
    (hone : (1 : G) ∈ K) :
    (leftStabilizer K hK hK_open : Set G) ⊆ K := by
  intro g hg
  have hfix : g • K = K := (mem_leftStabilizer_iff hK hK_open).mp hg
  have hmem : g • (1 : G) ∈ g • K := Set.smul_mem_smul_set_iff.mpr hone
  simpa only [hfix, smul_eq_mul, mul_one] using hmem

/-- The translation stabilizer is compact, without assuming the ambient group Hausdorff. -/
@[to_additive /-- The additive translation stabilizer is compact without an ambient
Hausdorff assumption. -/]
theorem isCompact_leftStabilizer [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) (hK_open : IsOpen K)
    (hone : (1 : G) ∈ K) :
    IsCompact (leftStabilizer K hK hK_open : Set G) :=
  hK.of_isClosed_subset (leftStabilizer K hK hK_open).isClosed
    (leftStabilizer_subset hK hK_open hone)

/-- A compact open set containing the identity contains a compact open subgroup. -/
@[to_additive /-- A compact open set containing zero contains a compact open additive
subgroup. -/]
theorem exists_compact_subset_of_compact_open [IsTopologicalGroup G]
    {K : Set G} (hK : IsCompact K)
    (hK_open : IsOpen K) (hone : (1 : G) ∈ K) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ K :=
  ⟨leftStabilizer K hK hK_open, isCompact_leftStabilizer hK hK_open hone,
    leftStabilizer_subset hK hK_open hone⟩

/-- In a compact ambient group, the compactness refinement agrees with the existential
conclusion of Mathlib's `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`.
This equivalence does not require the containing set itself to be clopen. -/
@[to_additive /-- In a compact ambient additive group, requiring the open subgroup to be
compact does not change the existence of one contained in a given set. -/]
theorem exists_compact_subset_iff_exists_subset [CompactSpace G]
    [SeparatelyContinuousMul G] {W : Set G} :
    (∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ W) ↔
      ∃ H : OpenSubgroup G, (H : Set G) ⊆ W := by
  constructor
  · rintro ⟨H, -, hHW⟩
    exact ⟨H, hHW⟩
  · rintro ⟨H, hHW⟩
    exact ⟨H, H.isClosed.isCompact, hHW⟩

/-- Van Dantzig's compact-open subgroup theorem, used in Neukirch, Schmidt, and Wingberg,
*Cohomology of Number Fields*, Chapter I, §1: every identity neighborhood contains a compact
open subgroup, even when the neighborhood is not open. Total disconnectedness supplies
Hausdorffness for topological groups; it is not an extra hypothesis. -/
@[to_additive /-- Van Dantzig's compact-open subgroup theorem: every zero neighborhood in a
locally compact totally disconnected additive topological group contains a compact open
additive subgroup. No extra Hausdorff hypothesis is needed. -/]
theorem exists_compact_subset_nhds_one [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ W := by
  have hT2 : T2Space G :=
    IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton
  obtain ⟨U, hUW, hUopen, hUone⟩ := mem_nhds_iff.mp hW
  obtain ⟨S, hScompact, hSone, hSU⟩ := exists_compact_subset hUopen hUone
  have hBasis : TopologicalSpace.IsTopologicalBasis {K : Set G | IsClopen K} :=
    @loc_compact_Haus_tot_disc_of_zero_dim G _ _ hT2 _
  obtain ⟨K, hKclopen, hKone, hKS⟩ :=
    hBasis.mem_nhds_iff.mp (isOpen_interior.mem_nhds hSone)
  have hKcompact : IsCompact K :=
    hScompact.of_isClosed_subset hKclopen.1 (hKS.trans interior_subset)
  obtain ⟨H, hHcompact, hHK⟩ :=
    exists_compact_subset_of_compact_open hKcompact hKclopen.2 hKone
  exact ⟨H, hHcompact, hHK.trans (hKS.trans (interior_subset.trans (hSU.trans hUW)))⟩

/-- The neighborhood-basis form of van Dantzig's theorem, used in Neukirch, Schmidt, and
Wingberg, *Cohomology of Number Fields*, Chapter I, §1: compact open subgroups form a basis
of identity neighborhoods. -/
@[to_additive /-- Van Dantzig's neighborhood-basis theorem: compact open additive subgroups
form a basis of zero neighborhoods in a locally compact totally disconnected additive
topological group. -/]
theorem nhds_one_hasBasis_compact [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] :
    (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G => IsCompact (H : Set G))
      (fun H => (H : Set G)) := by
  constructor
  intro W
  constructor
  · exact exists_compact_subset_nhds_one
  · rintro ⟨H, -, hHW⟩
    exact mem_of_superset H.mem_nhds_one hHW

end OpenSubgroup

/-- A locally compact totally disconnected topological group is nonarchimedean,
by van Dantzig's compact-open subgroup theorem. The group need not be commutative
or compact, and no extra separation hypothesis is required. -/
@[to_additive /-- A locally compact totally disconnected additive topological group is
nonarchimedean, by van Dantzig's compact-open subgroup theorem. Neither commutativity,
compactness nor an extra separation hypothesis is required. -/]
theorem NonarchimedeanGroup.of_locallyCompactSpace {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] : NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨H, -, hHU⟩ := OpenSubgroup.exists_compact_subset_nhds_one hU
    exact ⟨H, hHU⟩

end
