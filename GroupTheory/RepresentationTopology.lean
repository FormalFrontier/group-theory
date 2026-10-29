/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.RepresentationInvariants
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Closed fixed submodules

The fixed submodule of a representation by continuous operators is closed when
its carrier is Hausdorff. No topology on the acting monoid or scalars is required.

## References

The proof uses Mathlib's closed-equalizer theorem `isClosed_eq` and
closed-intersection theorem `isClosed_iInter`.
-/

@[expose] public section

universe u v w

namespace Representation

variable {R : Type u} {G : Type v} {V : Type w}
  [Semiring R] [Monoid G] [AddCommMonoid V] [Module R V]
  [TopologicalSpace V] [T2Space V]

/-- The fixed submodule of a representation by continuous maps is closed. -/
theorem isClosed_fixedSubmodule (ρ : Representation R G V)
    (hρ : ∀ g, Continuous (ρ g)) : IsClosed (ρ.fixedSubmodule : Set V) := by
  have hfixed : (ρ.fixedSubmodule : Set V) = ⋂ g, {v | ρ g v = v} := by
    ext v
    simp
  rw [hfixed]
  exact isClosed_iInter fun g => isClosed_eq (hρ g) continuous_id

end Representation
