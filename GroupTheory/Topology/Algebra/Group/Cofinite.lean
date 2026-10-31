/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Separation.Hausdorff
public import GroupTheory.MonoidHom.Finite
public import GroupTheory.Topology.Cofinite
public import GroupTheory.Topology.Algebra.MulAction.Irreducible
import Mathlib.Topology.WithTopology

/-!
# Cofinite topologies on groups

For an arbitrary group with the cofinite topology, inversion and every fixed left or right
translation are continuous. In contrast, joint multiplication is continuous exactly when the group
is finite. More generally, an action between cofinite topologies is jointly continuous exactly
when the actor is finite or the action is pointwise trivial; its target is any type.
The domain of joint multiplication carries the **product of two cofinite topologies**,
not the cofinite topology on the set of pairs. The finite case includes the trivial group, and no
commutativity assumption is needed.

A homomorphism from a group to a type with multiplication and identity, both with their cofinite
topologies, is continuous exactly when it is trivial or has finite kernel. More generally, finite
kernel gives continuity from any T1 source to a cofinite target, while a nontrivial continuous
homomorphism from a cofinite source to any T0 target has finite kernel. Consequently, a continuous
finite-range homomorphism from an infinite cofinite group to a T0 target is trivial. The target
needs only `MulOneClass`, with no associativity or inverse requirement. The additive counterparts
use `AddGroup` and `AddZeroClass`, without a commutativity assumption.

The coset quotient by a finite subgroup has the cofinite topology, while the coset quotient by
an infinite subgroup has the indiscrete topology. Thus the quotient topology is cofinite exactly
when the subgroup is finite or the quotient is subsingleton. These statements use the coset
space of any subgroup, without a normality assumption. The canonical action on the coset space
is jointly continuous exactly when the acting group is finite or the subgroup is infinite.
A surjective homomorphism with finite kernel likewise coinduces the cofinite topology, with only
`MulOneClass` on the target.

## Implementation notes

The cofinite filter and neighborhood API turn a map with finite fibers into a continuous map
from a T1 source to a cofinite target. Injectivity supplies this filter condition for inversion
and translations. The homomorphism criterion uses `MonoidHom.finite_ker_iff_finite_fibers`.
For necessity, a T0 open separator of a nonidentity image and the identity has a nonempty open
preimage with finite complement. The kernel either lies in that complement or injects into it
by a fixed translation.
For infinite cofinite actors, preirreducibility and continuous inversion reduce joint action
continuity to orbitwise inseparability, which is equality in a cofinite target. For finite actors,
the discrete-left product criterion and continuity of fixed scalar permutations suffice.
The multiplication criterion is the regular-action case of this action criterion.

The quotient results use Mathlib's characteristic coinduced-topology equation for the coset
projection. Mathlib's equivalence between a left coset and its subgroup supplies the finite or
infinite fibers. The cofinite finite-fiber and infinite-fiber results then identify the coinduced
topology; the infinite-fiber result follows the dense-fiber approach in
`GroupTheory.Topology.DenseFibers`.

All statements use the given operations and topologies. Cofinite hypotheses are expressed as
equalities of topologies. `WithTopology` transfers topological facts, not any group structure.

## References

- Mathlib's cofinite filter and topology API: `Function.Injective.tendsto_cofinite`,
  `Filter.Tendsto.cofinite_of_finite_preimage_singleton`, `CofiniteTopology.continuous_of`,
  and `CofiniteTopology.nhds_eq`.
- Mathlib's weak kernel API, `exists_isOpen_xor_mem`, `Set.Finite.of_injOn`,
  and `Set.Finite.preimage'`.
- Mathlib's cofinite T1 and irreducibility instances, `continuous_prod_of_discrete_left`,
  and `MulAction.injective`, together with the orbit-inseparability criterion in
  `GroupTheory.Topology.Algebra.MulAction.Irreducible`.
- Mathlib's `QuotientGroup.isQuotientMap_mk`, `Topology.IsCoinducing.eq_coinduced`,
  `QuotientGroup.eq_class_eq_leftCoset`, and `Subgroup.leftCosetEquivSubgroup`.
- The finite-fiber cofinite and dense-fiber coinduced-topology results in
  `GroupTheory.Topology.Cofinite` and `GroupTheory.Topology.DenseFibers`.
-/

@[expose] public section

universe u v

namespace CofiniteTopology

open scoped Topology

private theorem t1Space_of_eq_cofinite {X : Type u} [t : TopologicalSpace X]
    (hcofinite : t = TopologicalSpace.cofinite) : T1Space X :=
  t1Space_iff_continuous_cofinite_of.mpr (by
    rw [hcofinite]
    exact WithTopology.continuous_toTopology _)

private theorem continuous_of_tendsto_cofinite {X : Type u} {Y : Type v}
    [TopologicalSpace X] [tY : TopologicalSpace Y] [T1Space X]
    (hY : tY = TopologicalSpace.cofinite) {f : X → Y}
    (hf : Filter.Tendsto f Filter.cofinite Filter.cofinite) : Continuous f := by
  let F : CofiniteTopology X → CofiniteTopology Y := fun x =>
    WithTopology.toTopology TopologicalSpace.cofinite (f (WithTopology.ofTopology x))
  have hF_cofinite : Filter.Tendsto F Filter.cofinite Filter.cofinite :=
    (WithTopology.toTopology_injective _).tendsto_cofinite.comp
      (hf.comp (WithTopology.ofTopology_injective _).tendsto_cofinite)
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    change Filter.Tendsto F (𝓝 x) (𝓝 (F x))
    rw [nhds_eq, nhds_eq]
    exact (Filter.tendsto_pure_pure F x).sup_sup hF_cofinite
  have hto : Continuous (WithTopology.toTopology (X := X) TopologicalSpace.cofinite) :=
    CofiniteTopology.continuous_of
  have hfrom : Continuous
      (WithTopology.ofTopology (X := Y) (t := TopologicalSpace.cofinite)) := by
    rw [hY]
    exact WithTopology.continuous_ofTopology _
  exact hfrom.comp (hF.comp hto)

section Group

variable {G : Type u} [Group G] [t : TopologicalSpace G]

/-- Inversion is continuous for the cofinite topology on any group, independently of joint
continuity of multiplication. -/
@[to_additive /-- Negation is continuous for the cofinite topology on any additive group,
independently of joint continuity of addition. -/]
theorem continuous_inv (hcofinite : t = TopologicalSpace.cofinite) :
    Continuous (fun g : G => g⁻¹) := by
  have : T1Space G := t1Space_of_eq_cofinite hcofinite
  exact continuous_of_tendsto_cofinite hcofinite inv_injective.tendsto_cofinite

/-- Every fixed left translation is continuous for the cofinite topology on any group. -/
theorem continuous_mul_left (hcofinite : t = TopologicalSpace.cofinite) (a : G) :
    Continuous (fun g : G => a * g) := by
  have : T1Space G := t1Space_of_eq_cofinite hcofinite
  exact continuous_of_tendsto_cofinite hcofinite (mul_right_injective a).tendsto_cofinite

/-- Every fixed right translation is continuous for the cofinite topology on any group. -/
theorem continuous_mul_right (hcofinite : t = TopologicalSpace.cofinite) (a : G) :
    Continuous (fun g : G => g * a) := by
  have : T1Space G := t1Space_of_eq_cofinite hcofinite
  exact continuous_of_tendsto_cofinite hcofinite (mul_left_injective a).tendsto_cofinite

end Group

section MulAction

variable {G : Type u} {X : Type v} [Group G] [act : MulAction G X]
  [tG : TopologicalSpace G] [tX : TopologicalSpace X]

/-- An action between given cofinite topologies is jointly continuous exactly when the acting
group is finite or the action is pointwise trivial. The target is an arbitrary type. -/
@[to_additive /-- An additive action between given cofinite topologies is jointly continuous exactly
when the acting additive group is finite or the action is pointwise trivial. The target is an
arbitrary type. -/]
theorem continuous_smul_iff
    (hG : tG = TopologicalSpace.cofinite) (hX : tX = TopologicalSpace.cofinite) :
    Continuous (fun p : G × X => p.1 • p.2) ↔
      Finite G ∨ ∀ (g : G) (x : X), g • x = x := by
  have : T1Space G := t1Space_of_eq_cofinite hG
  have : T1Space X := t1Space_of_eq_cofinite hX
  constructor
  · intro h
    by_cases hfinite : Finite G
    · exact Or.inl hfinite
    · let : Infinite G := not_finite_iff_infinite.mp hfinite
      have hfrom : Continuous
          (WithTopology.ofTopology (X := G) (t := TopologicalSpace.cofinite)) := by
        rw [hG]
        exact WithTopology.continuous_ofTopology _
      let : IrreducibleSpace G :=
        (WithTopology.ofTopology_surjective TopologicalSpace.cofinite).irreducibleSpace hfrom
      let : ContinuousInv G := ⟨continuous_inv hG⟩
      exact Or.inr fun g x =>
        ((MulAction.continuous_smul_iff_inseparable.mp h) g x).eq
  · rintro (hfinite | htrivial)
    · let : Finite G := hfinite
      let : DiscreteTopology G := inferInstance
      exact continuous_prod_of_discrete_left.mpr fun g =>
        continuous_of_tendsto_cofinite hX (MulAction.injective g).tendsto_cofinite
    · simpa only [htrivial] using (continuous_snd : Continuous (fun p : G × X => p.2))

end MulAction

section Group

variable {G : Type u} [Group G] [t : TopologicalSpace G]

/-- Multiplication from the product of two copies of a group's cofinite topology to its cofinite
topology is continuous exactly when the group is finite, including the trivial group. -/
theorem continuous_mul_iff_finite (hcofinite : t = TopologicalSpace.cofinite) :
    Continuous (fun p : G × G => p.1 * p.2) ↔ Finite G := by
  rw [show (fun p : G × G => p.1 * p.2) = (fun p : G × G => p.1 • p.2) from rfl,
    continuous_smul_iff hcofinite hcofinite]
  constructor
  · rintro (hfinite | htrivial)
    · exact hfinite
    · have : Subsingleton G := ⟨fun a b => by
        have ha := htrivial a 1
        have hb := htrivial b 1
        simpa only [smul_eq_mul, mul_one] using ha.trans hb.symm⟩
      infer_instance
  · exact Or.inl

end Group

section Hom

variable {G : Type u} {M : Type v} [Group G] [MulOneClass M]
  [tG : TopologicalSpace G] [tM : TopologicalSpace M]

/-- A homomorphism with finite kernel from a group with a T1 topology to a cofinite target is
continuous. Only multiplication and identity are required on the target. -/
@[to_additive /-- An additive homomorphism with finite kernel from an additive group with a T1
topology to a cofinite target is continuous. Only addition and zero are required on the target. -/]
theorem continuous_monoidHom_of_finite_ker [T1Space G]
    (hM : tM = TopologicalSpace.cofinite) (f : G →* M)
    (hker : Finite f.ker) : Continuous f :=
  continuous_of_tendsto_cofinite hM
    (Filter.Tendsto.cofinite_of_finite_preimage_singleton
      (f.finite_ker_iff_finite_fibers.mp hker))

/-- A nontrivial continuous homomorphism from a cofinite group to a T0 target has finite kernel.
Only multiplication and identity are required on the target. -/
@[to_additive /-- A nontrivial continuous additive homomorphism from a cofinite additive group
to a T0 target has finite kernel. Only addition and zero are required on the target. -/]
theorem finite_ker_of_continuous_monoidHom [T0Space M]
    (hG : tG = TopologicalSpace.cofinite) (f : G →* M)
    (hf : Continuous f) (hne : f ≠ 1) : Finite f.ker := by
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hne
  obtain ⟨s, hs, hsep⟩ := exists_isOpen_xor_mem (show f a ≠ 1 from ha)
  have hpre : IsOpen (f ⁻¹' s) := hs.preimage hf
  rw [hG] at hpre
  change (f ⁻¹' s).Nonempty → ((f ⁻¹' s)ᶜ).Finite at hpre
  change (f.ker : Set G).Finite
  rcases hsep with ⟨haS, h1S⟩ | ⟨h1S, haS⟩
  · refine (hpre ⟨a, haS⟩).subset ?_
    intro k hk
    change f k ∉ s
    simpa only [f.mem_ker.mp hk] using h1S
  · have hfinite := hpre ⟨1, by simpa only [Set.mem_preimage, map_one] using h1S⟩
    refine Set.Finite.of_injOn (f := fun k : G => a * k) ?_
      (mul_right_injective a).injOn hfinite
    intro k hk
    change f (a * k) ∉ s
    simpa only [map_mul, f.mem_ker.mp hk, mul_one] using haS

/-- A homomorphism between cofinite topologies is continuous exactly when it is trivial or has
finite kernel. Only multiplication and identity are required on the target. -/
@[to_additive /-- An additive homomorphism between cofinite topologies is continuous exactly when
it is trivial or has finite kernel. Only addition and zero are required on the target. -/]
theorem continuous_monoidHom_iff
    (hG : tG = TopologicalSpace.cofinite) (hM : tM = TopologicalSpace.cofinite) (f : G →* M) :
    Continuous f ↔ f = 1 ∨ Finite f.ker := by
  constructor
  · intro hf
    by_cases htrivial : f = 1
    · exact Or.inl htrivial
    · have : T1Space M := t1Space_of_eq_cofinite hM
      exact Or.inr (finite_ker_of_continuous_monoidHom hG f hf htrivial)
  · rintro (rfl | hker)
    · exact continuous_const
    · have : T1Space G := t1Space_of_eq_cofinite hG
      exact continuous_monoidHom_of_finite_ker hM f hker

/-- A continuous homomorphism with finite range from an infinite cofinite group to a T0 target
is trivial. Only multiplication and identity are required on the target. -/
@[to_additive /-- A continuous additive homomorphism with finite range from an infinite cofinite
additive group to a T0 target is trivial. Only addition and zero are required on the target. -/]
theorem eq_one_of_continuous_monoidHom_of_finite_range [Infinite G] [T0Space M]
    (hG : tG = TopologicalSpace.cofinite) (f : G →* M)
    (hf : Continuous f) (hfinite : (Set.range f).Finite) : f = 1 := by
  by_contra hne
  have hfibers := f.finite_ker_iff_finite_fibers.mp
    (finite_ker_of_continuous_monoidHom hG f hf hne)
  have hfiniteG : (Set.univ : Set G).Finite := by
    simpa only [Set.preimage_range] using hfinite.preimage' (fun y _ => hfibers y)
  exact Set.infinite_univ hfiniteG

end Hom

end CofiniteTopology

namespace QuotientGroup

variable {G : Type u} [Group G] [tG : TopologicalSpace G]

/-- The coset quotient of a cofinite group by a finite subgroup has the cofinite topology. -/
@[to_additive /-- The coset quotient of a cofinite additive group by a finite additive subgroup
has the cofinite topology. -/]
theorem topology_eq_cofinite_of_finite (H : Subgroup G)
    (hG : tG = TopologicalSpace.cofinite) [Finite H] :
    (QuotientGroup.instTopologicalSpace H : TopologicalSpace (G ⧸ H)) =
      TopologicalSpace.cofinite := by
  rw [(isQuotientMap_mk H).eq_coinduced, hG]
  refine CofiniteTopology.coinduced_eq_cofinite_of_finite_fibers
    (mk : G → G ⧸ H) mk_surjective ?_
  intro q
  refine QuotientGroup.induction_on q ?_
  intro a
  change {x : G | (x : G ⧸ H) = (a : G ⧸ H)}.Finite
  rw [eq_class_eq_leftCoset H a]
  exact (Subgroup.leftCosetEquivSubgroup (s := H) a).finite_iff.mpr inferInstance

/-- The coset quotient of a cofinite group by an infinite subgroup has the indiscrete topology. -/
@[to_additive /-- The coset quotient of a cofinite additive group by an infinite additive subgroup
has the indiscrete topology. -/]
theorem topology_eq_top_of_infinite (H : Subgroup G)
    (hG : tG = TopologicalSpace.cofinite) [Infinite H] :
    (QuotientGroup.instTopologicalSpace H : TopologicalSpace (G ⧸ H)) = ⊤ := by
  rw [(isQuotientMap_mk H).eq_coinduced, hG]
  refine CofiniteTopology.coinduced_eq_top_of_infinite_fibers (mk : G → G ⧸ H) ?_
  intro q
  refine QuotientGroup.induction_on q ?_
  intro a
  change {x : G | (x : G ⧸ H) = (a : G ⧸ H)}.Infinite
  rw [eq_class_eq_leftCoset H a]
  exact Set.infinite_coe_iff.mp
    ((Subgroup.leftCosetEquivSubgroup (s := H) a).infinite_iff.mpr inferInstance)

/-- The coset quotient of a cofinite group is cofinite exactly when the subgroup is finite
or the quotient is subsingleton. -/
@[to_additive /-- The coset quotient of a cofinite additive group is cofinite exactly when the
additive subgroup is finite or the quotient is subsingleton. -/]
theorem topology_eq_cofinite_iff (H : Subgroup G)
    (hG : tG = TopologicalSpace.cofinite) :
    (QuotientGroup.instTopologicalSpace H : TopologicalSpace (G ⧸ H)) =
      TopologicalSpace.cofinite ↔ Finite H ∨ Subsingleton (G ⧸ H) := by
  constructor
  · intro hQ
    by_cases hfinite : Finite H
    · exact Or.inl hfinite
    · let : Infinite H := not_finite_iff_infinite.mp hfinite
      have htop := topology_eq_top_of_infinite H hG
      have : T1Space (G ⧸ H) := CofiniteTopology.t1Space_of_eq_cofinite hQ
      have : IndiscreteTopology (G ⧸ H) := ⟨htop⟩
      exact Or.inr (subsingleton_iff_indiscreteTopology.mpr inferInstance)
  · rintro (hfinite | hsubsingleton)
    · let : Finite H := hfinite
      exact topology_eq_cofinite_of_finite H hG
    · let : Subsingleton (G ⧸ H) := hsubsingleton
      exact Subsingleton.elim _ _

/-- The canonical action of a cofinite group on its coset quotient is jointly continuous exactly
when the group is finite or the subgroup is infinite. The quotient has its coinduced topology,
and the domain has the product topology; no normality assumption is needed. -/
@[to_additive
  /-- The canonical action of a cofinite additive group on its coset quotient is jointly continuous
  exactly when the group is finite or the additive subgroup is infinite. The quotient has its
  coinduced topology, and the domain has the product topology; no commutativity assumption is
  needed. -/]
theorem continuous_smul_iff (H : Subgroup G) (hG : tG = TopologicalSpace.cofinite) :
    Continuous (fun p : G × (G ⧸ H) => p.1 • p.2) ↔ Finite G ∨ Infinite H := by
  constructor
  · intro hcontinuous
    by_cases hfiniteH : Finite H
    · let : Finite H := hfiniteH
      rcases (CofiniteTopology.continuous_smul_iff hG
        (topology_eq_cofinite_of_finite H hG)).mp hcontinuous with hfiniteG | htrivial
      · exact Or.inl hfiniteG
      · have htop : H = ⊤ := by
          rw [← MulAction.stabilizer_quotient H]
          apply top_unique
          intro g _
          exact MulAction.mem_stabilizer_iff.mpr (htrivial g _)
        have hsurj : Function.Surjective (Subtype.val : H → G) := by
          intro g
          refine ⟨⟨g, ?_⟩, rfl⟩
          rw [htop]
          exact Subgroup.mem_top g
        exact Or.inl (Finite.of_surjective _ hsurj)
    · exact Or.inr (not_finite_iff_infinite.mp hfiniteH)
  · rintro (hfiniteG | hinfiniteH)
    · let : Finite G := hfiniteG
      let : Finite H := inferInstance
      exact (CofiniteTopology.continuous_smul_iff hG
        (topology_eq_cofinite_of_finite H hG)).mpr (Or.inl hfiniteG)
    · let : Infinite H := hinfiniteH
      let : IndiscreteTopology (G ⧸ H) := ⟨topology_eq_top_of_infinite H hG⟩
      exact continuous_of_indiscreteTopology

end QuotientGroup

namespace MonoidHom

variable {G : Type u} {M : Type v} [Group G] [MulOneClass M]
  [tG : TopologicalSpace G]

/-- A surjective homomorphism with finite kernel from a cofinite group coinduces the
cofinite topology. Only multiplication and identity are required on the target. -/
@[to_additive /-- A surjective additive homomorphism with finite kernel from a cofinite additive
group coinduces the cofinite topology. Only addition and zero are required on the target. -/]
theorem coinduced_eq_cofinite_of_finite_ker (f : G →* M)
    (hG : tG = TopologicalSpace.cofinite) (hf : Function.Surjective f)
    (hker : Finite f.ker) :
    TopologicalSpace.coinduced (f : G → M) tG = TopologicalSpace.cofinite := by
  rw [hG]
  exact CofiniteTopology.coinduced_eq_cofinite_of_finite_fibers (f : G → M) hf
    (f.finite_ker_iff_finite_fibers.mp hker)

end MonoidHom
