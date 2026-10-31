/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Separation.Basic

/-!
# Finite open sets in R₀ spaces

A finite open set in an R₀ space is closed: it contains the closure of each of its points,
and hence is a finite union of closed point closures. Dually, a closed set with finite
complement is open. Neither statement requires the ambient space to be finite.

In a finite R₀ space, open and closed sets therefore coincide, and every point closure is
clopen. No separation assumption stronger than R₀ is needed.

## Main results

* `IsOpen.isClosed_of_finite`: a finite open set in an R₀ space is closed.
* `IsClosed.isOpen_of_finite_compl`: a closed set with finite complement is open.
* `isOpen_iff_isClosed_of_finite`: open and closed sets coincide in a finite R₀ space.
* `isClopen_closure_singleton_of_finite`: point closures in a finite R₀ space are clopen.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X] [R0Space X]

/-- A finite open set in an R₀ space is closed. -/
theorem IsOpen.isClosed_of_finite {s : Set X} (hs : IsOpen s) (hfin : s.Finite) :
    IsClosed s := by
  have hs_eq : s = ⋃ x ∈ s, closure ({x} : Set X) := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · intro hy
      exact ⟨y, hy, subset_closure (by simp)⟩
    · rintro ⟨x, hx, hy⟩
      have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
      exact mem_of_mem_nhds (hxy.symm (hs.mem_nhds hx))
  rw [hs_eq]
  exact hfin.isClosed_biUnion fun _ _ ↦ isClosed_closure

/-- A closed set with finite complement in an R₀ space is open. -/
theorem IsClosed.isOpen_of_finite_compl {s : Set X} (hs : IsClosed s)
    (hfin : sᶜ.Finite) : IsOpen s := by
  simpa only [compl_compl] using (hs.isOpen_compl.isClosed_of_finite hfin).isOpen_compl

/-- In a finite R₀ space, a set is open if and only if it is closed. -/
theorem isOpen_iff_isClosed_of_finite [Finite X] {s : Set X} :
    IsOpen s ↔ IsClosed s :=
  ⟨fun hs ↦ hs.isClosed_of_finite (Set.toFinite s),
    fun hs ↦ hs.isOpen_of_finite_compl (Set.toFinite sᶜ)⟩

/-- The closure of a singleton in a finite R₀ space is clopen. -/
theorem isClopen_closure_singleton_of_finite [Finite X] (x : X) :
    IsClopen (closure ({x} : Set X)) := by
  have hclosed : IsClosed (closure ({x} : Set X)) := isClosed_closure
  have hopen : IsOpen (closure ({x} : Set X)) :=
    hclosed.isOpen_of_finite_compl (Set.toFinite _)
  constructor <;> assumption
