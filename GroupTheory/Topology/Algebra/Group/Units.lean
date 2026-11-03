/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Topology of units

A unit-reflecting monoid homomorphism with dense range induces a dense map on units
when the target's unit coercion is an open embedding. No topology on the source monoid
is needed. We use Mathlib's canonical unit topology and unit-reflection class.

## Closed identity

For a topological monoid, the canonical units embedding into the product with the
multiplicative opposite is closed exactly when the identity singleton is closed.
This condition also gives local compactness of the units when the monoid is locally
compact, and gives Hausdorffness of the units without a separation assumption on the
monoid. These results use Mathlib's units topology, range description and transfer of
local compactness along closed embeddings.
-/

@[expose] public section

universe u v

/-- A dense monoid homomorphism that reflects units has dense range on units if the
coercion from the target's units is an open embedding. -/
theorem DenseRange.units_map
    {M : Type u} {N : Type v} [Monoid M] [Monoid N] [TopologicalSpace N]
    {f : M →* N} [IsLocalHom f] (hf : DenseRange f)
    (hval : Topology.IsOpenEmbedding (Units.val : Nˣ → N)) :
    DenseRange (Units.map f) := by
  have hd : Dense ((Units.val : Nˣ → N) ⁻¹' Set.range f) :=
    Dense.preimage hf hval.isOpenMap
  refine hd.mono ?_
  rintro u ⟨m, hm⟩
  have hfm : IsUnit (f m) := ⟨u, hm.symm⟩
  obtain ⟨v, hv⟩ := (isUnit_map_iff f m).mp hfm
  refine ⟨v, Units.ext ?_⟩
  exact (Units.coe_map f v).trans ((congrArg f hv).trans hm)

namespace Units

open MulOpposite Topology

variable {D : Type v} [Monoid D] [TopologicalSpace D] [ContinuousMul D]

/-- The canonical embedding of units into `D × Dᵐᵒᵖ` is closed exactly when the
identity singleton of `D` is closed. The topology on units is induced by both the
value and the opposite of the inverse value. -/
theorem isClosedEmbedding_embedProduct_iff_isClosed_one :
    IsClosedEmbedding (embedProduct D) ↔ IsClosed ({1} : Set D) := by
  constructor
  · intro h
    have hslice : Continuous (fun d : D => (d, op (1 : D))) :=
      continuous_id.prodMk continuous_const
    convert h.isClosed_range.preimage hslice using 1
    ext d
    simp [range_embedProduct]
  · intro hOne
    refine ⟨isEmbedding_embedProduct, ?_⟩
    rw [range_embedProduct]
    exact (hOne.preimage
      (continuous_fst.mul (continuous_unop.comp continuous_snd))).inter
      (hOne.preimage
        ((continuous_unop.comp continuous_snd).mul continuous_fst))

/-- The units of a locally compact topological monoid are locally compact if its
identity singleton is closed. No separation hypothesis on the monoid is needed. -/
theorem locallyCompactSpace_of_isClosed_one [LocallyCompactSpace D]
    (hOne : IsClosed ({1} : Set D)) : LocallyCompactSpace Dˣ :=
  ((isClosedEmbedding_embedProduct_iff_isClosed_one (D := D)).2 hOne).locallyCompactSpace

/-- The units of a topological monoid are Hausdorff if the identity singleton in
the monoid is closed. This does not require the monoid itself to be Hausdorff. -/
theorem t2Space_of_isClosed_one (hOne : IsClosed ({1} : Set D)) : T2Space Dˣ := by
  have hUnits : IsClosed ({1} : Set Dˣ) := by
    convert hOne.preimage (continuous_val : Continuous ((↑) : Dˣ → D)) using 1
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, val_eq_one]
  rw [t2_iff_isClosed_diagonal]
  convert hUnits.preimage
    (continuous_fst.inv.mul continuous_snd :
      Continuous (fun p : Dˣ × Dˣ => p.1⁻¹ * p.2)) using 1
  ext p
  simp [Set.diagonal, _root_.inv_mul_eq_one]

private theorem isClosedEmbedding_embedProduct_eq_of_t1 [T1Space D] :
    (isClosedEmbedding_embedProduct_iff_isClosed_one (D := D)).2
        (isClosed_singleton : IsClosed ({1} : Set D)) =
      isClosedEmbedding_embedProduct (α := D) :=
  Subsingleton.elim _ _

private theorem locallyCompactSpace_of_isClosed_one_eq_of_t1
    [T1Space D] [LocallyCompactSpace D] :
    locallyCompactSpace_of_isClosed_one (isClosed_singleton : IsClosed ({1} : Set D)) =
      (inferInstance : LocallyCompactSpace Dˣ) :=
  Subsingleton.elim _ _

end Units
