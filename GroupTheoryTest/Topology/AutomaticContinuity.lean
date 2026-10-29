/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.AutomaticContinuity
public import GroupTheoryTest.Topology.PadicDenseIntegers
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Automatic continuity for endomorphisms and actions of the 2-adic integers

The additive endpoints apply to arbitrary abstract additive endomorphisms and to abstract additive
actions with finite individual orbits on arbitrary discrete spaces, using the existing canonical
dense finitely generated subgroup of embedded integers. The endomorphism result is not restricted
to finite-image homomorphisms: the identity is an infinite-image specialization. The action result
requires neither an additive structure on the carrier nor a finite total action image.
-/

@[expose] public section

namespace GroupTheoryTest.Topology.AutomaticContinuity

open GroupTheoryTest.Topology.PadicDenseIntegers

universe v

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Every abstract additive endomorphism of the 2-adic integers is continuous. -/
private theorem padicInt_endomorphism_continuous (f : ℤ_[2] →+ ℤ_[2]) : Continuous f :=
  f.continuous_of_dense_fg padicIntegers padicIntegers_fg padicIntegers_dense

/-- Every abstract additive action of the 2-adic integers on a discrete space with finite
individual orbits is jointly continuous. -/
private theorem padicInt_action_continuous {β : Type v}
    [TopologicalSpace β] [DiscreteTopology β] [AddAction ℤ_[2] β]
    (h_orbit : ∀ b : β, (AddAction.orbit ℤ_[2] b).Finite) : ContinuousVAdd ℤ_[2] β :=
  AddAction.continuousVAdd_of_finite_orbits_of_dense_fg
    padicIntegers padicIntegers_fg padicIntegers_dense h_orbit

end GroupTheoryTest.Topology.AutomaticContinuity
