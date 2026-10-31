/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.Group.ConnectedComponent

/-!
# Identity components of products

For groups whose fixed left translations are continuous, the identity component of a
product is the product of the identity components. No continuity of right translations,
multiplication as a two-variable map, or inversion is required.
-/

@[expose] public section

universe u v

section

variable (G : Type u) (H : Type v)
  [Monoid G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [Monoid H] [TopologicalSpace H] [ContinuousConstSMul H H]

/-- Fixed left translations on a product of monoids are continuous if they are continuous
on each factor. -/
@[to_additive continuousConstVAdd_prod_self
  /-- Fixed left translations on a product of additive monoids are continuous if they are
  continuous on each factor. -/]
theorem continuousConstSMul_prod_self :
    ContinuousConstSMul (G × H) (G × H) :=
  ⟨fun g =>
    ((continuous_const_smul g.1).comp continuous_fst).prodMk
      ((continuous_const_smul g.2).comp continuous_snd)⟩

end

attribute [local instance] continuousConstSMul_prod_self continuousConstVAdd_prod_self

variable (G : Type u) (H : Type v)
  [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [Group H] [TopologicalSpace H] [ContinuousConstSMul H H]

namespace Subgroup

/-- The identity component of a product is the product of the identity components,
assuming only continuity of fixed left translations in each factor. -/
@[to_additive connectedComponentOfZeroOfContinuousConstVAdd_prod
  /-- The zero component of a product is the product of the zero components,
  assuming only continuity of fixed left translations in each factor. -/]
theorem connectedComponentOfOneOfContinuousConstSMul_prod :
    connectedComponentOfOneOfContinuousConstSMul (G × H) =
      (connectedComponentOfOneOfContinuousConstSMul G).prod
        (connectedComponentOfOneOfContinuousConstSMul H) := by
  apply le_antisymm
  · intro x hx
    -- The two projections send the identity component into the factor components.
    exact ⟨
      map_connectedComponentOfOneOfContinuousConstSMul_le
        (MonoidHom.fst G H) continuous_fst ⟨x, hx, rfl⟩,
      map_connectedComponentOfOneOfContinuousConstSMul_le
        (MonoidHom.snd G H) continuous_snd ⟨x, hx, rfl⟩⟩
  · -- The product subgroup is preconnected, so it lies in the identity component.
    exact le_connectedComponentOfOneOfContinuousConstSMul
      ((connectedComponentOfOneOfContinuousConstSMul G).prod
        (connectedComponentOfOneOfContinuousConstSMul H))
      ((isConnected_connectedComponentOfOneOfContinuousConstSMul (G := G)).isPreconnected.prod
        (isConnected_connectedComponentOfOneOfContinuousConstSMul (G := H)).isPreconnected)

end Subgroup
