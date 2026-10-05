/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Separation.Profinite

/-!
# Open quotients of compact totally disconnected spaces

An open quotient of a compact Hausdorff totally disconnected space is totally
disconnected when its codomain is Hausdorff. This general topology result was
first formalized in Formal Frontier's Profinite Groups library.

The proof uses Mathlib's clopen basis of a compact Hausdorff totally
disconnected space and its transport along an open quotient map.

## References

- Formal Frontier, *Profinite Groups*, continuous sections of profinite coset
  projections (original formalization of the open-quotient theorem).
- Mathlib, `Mathlib.Topology.Separation.Profinite` and
  `Mathlib.Topology.Bases` (clopen basis and open-quotient basis transport).
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped Topology

universe u v

namespace Topology.IsOpenQuotientMap

/-- An open Hausdorff quotient of a compact Hausdorff totally disconnected
space is totally disconnected. -/
theorem totallyDisconnectedSpace
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsOpenQuotientMap f) : TotallyDisconnectedSpace Y := by
  have hb := hf.isTopologicalBasis (isTopologicalBasis_isClopen (X := X))
  have hbc : Set.image f '' {U : Set X | IsClopen U} ⊆ {V : Set Y | IsClopen V} := by
    rintro _ ⟨U, hU, rfl⟩
    exact ⟨(hU.1.isCompact.image hf.continuous).isClosed, hf.isOpenMap U hU.2⟩
  let _ : TotallySeparatedSpace Y := totallySeparatedSpace_of_t0_of_basis_clopen <|
    hb.of_isOpen_of_subset (fun _ h ↦ h.2) hbc
  infer_instance

end Topology.IsOpenQuotientMap
