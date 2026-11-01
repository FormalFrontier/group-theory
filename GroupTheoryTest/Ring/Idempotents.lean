/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import GroupTheory.Ring.Idempotents

/-!
# Unit-coordinate selection for finite products

The standard coordinate idempotents, mapped by an ordinary ring homomorphism to a
local semiring, have exactly one unit image. Source fibres may be trivial; the
decidable equality is used only for the coordinate insertions `Pi.single`.
-/

@[expose] public section

universe u v w

example {ι : Type u} {R : ι → Type v} {S : Type w}
    [Fintype ι] [DecidableEq ι] [∀ i, Semiring (R i)]
    [Semiring S] [IsLocalRing S] (f : (∀ i, R i) →+* S) :
    ∃! i : ι, IsUnit (f (Pi.single i (1 : R i))) := by
  exact ((CompleteOrthogonalIdempotents.single R).map f).existsUnique_isUnit
