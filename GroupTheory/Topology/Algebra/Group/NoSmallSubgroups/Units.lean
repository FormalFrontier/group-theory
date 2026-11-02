/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Analysis.Normed.Ring.PowerDetection
public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import Mathlib.Topology.Algebra.Constructions
import Mathlib.Tactic.NormNum

/-!
# No small subgroups in the units of a normed ring

The units of a normed ring with norm-homogeneous canonical integer multiplication
have no small subgroups in their usual topology induced by value and inverse value.
The identity-neighborhood is the value-preimage of the ball of radius `1 / 2` about
one. Uniform positive-power detection in the ring proves that only the identity
can have all its positive powers in this neighborhood.

In particular this applies to normed rings that are real normed spaces, with no
compatibility assumption between real scalar multiplication and ring
multiplication. The integer-homogeneity instance in the power-detection module
supplies the required mixin. Neither completeness nor openness of the unit locus
is needed. The proof uses Mathlib's continuous value map and units power API, and
the general positive-powers criterion for `NoSmallSubgroups`.
-/

@[expose] public section

universe u

/-- The units of a normed ring with norm-homogeneous canonical integer action have
no small subgroups. The witness is the value-preimage of the ball of radius
`1 / 2` about one, in the original units topology. -/
instance Units.noSmallSubgroups {A : Type u} [NormedRing A] [NormSMulClass ℤ A] :
    NoSmallSubgroups Aˣ := by
  apply NoSmallSubgroups.of_nhds_one_pow
    (U := (Units.val : Aˣ → A) ⁻¹' Metric.ball (1 : A) (1 / 2 : ℝ))
  · apply (Metric.isOpen_ball.preimage Units.continuous_val).mem_nhds
    change (1 : A) ∈ Metric.ball (1 : A) (1 / 2 : ℝ)
    exact Metric.mem_ball_self (by norm_num)
  · intro u hu
    apply Units.val_eq_one.mp
    apply NormedRing.eq_one_of_forall_norm_pow_sub_one_le (u : A) (1 / 2) (by norm_num)
    intro n hn
    have hmem : ((u ^ n : Aˣ) : A) ∈ Metric.ball (1 : A) (1 / 2 : ℝ) := hu n hn
    have hnorm : ‖((u ^ n : Aˣ) : A) - 1‖ < (1 / 2 : ℝ) := mem_ball_iff_norm.mp hmem
    simpa only [Units.val_pow_eq_pow_val] using hnorm.le
