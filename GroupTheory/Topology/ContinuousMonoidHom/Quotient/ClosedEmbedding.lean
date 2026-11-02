/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import Mathlib.Topology.Constructions

public import GroupTheory.Topology.ContinuousMap.CompactLifting
public import GroupTheory.Topology.ContinuousMonoidHom.Quotient
public import GroupTheory.Topology.Function.FactorsThrough

/-!
# Closed embeddings from quotient pullback

Pullback along a compact-covering quotient homomorphism is a closed embedding into the
original compact-open continuous-hom space when the target is Hausdorff. Its image consists
of homomorphisms constant on the quotient fibres. No continuity of the monoid operations is
required.

For an open quotient homomorphism with weakly locally compact source and Hausdorff quotient,
compact covering follows from compact lifting. Neither result requires a Hausdorff source,
a section, properness, compact fibres, or a different topology on a hom space.

## References

The descent homeomorphism and its forward composition API are provided by
`ContinuousMonoidHom.quotientPullbackHomeomorph`. Closedness of its fibreconstant image uses
`Function.isClosed_setOf_factorsThrough` and the Mathlib community's continuous point
evaluations on hom spaces in `Mathlib.Topology.Algebra.Group.CompactOpen`. Compact lifting
for the open-quotient specialization is provided by
`IsOpenQuotientMap.exists_compact_lift`.
-/

@[expose] public section

open Set Topology

universe u v w

namespace ContinuousMonoidHom

variable {G : Type u} {H : Type v} {K : Type w}
  [Monoid G] [Monoid H] [Monoid K]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K] [T2Space K]

/-- Pullback along a compact-covering quotient homomorphism is a closed embedding into the
original continuous-hom space, with no continuity assumption on the monoid operations. -/
@[to_additive /-- Pullback along a compact-covering quotient additive homomorphism is a
closed embedding into the original continuous-hom space, with no continuity assumption on
the additive monoid operations. -/]
theorem isClosedEmbedding_comp_left_of_isQuotientMap (q : G →ₜ* H)
    (hq : IsQuotientMap q)
    (hcompact : ∀ s : Set H, IsCompact s →
      ∃ l : Set G, IsCompact l ∧ Set.image q l = s) :
    IsClosedEmbedding (fun f : H →ₜ* K ↦ f.comp q) := by
  have hclosed : IsClosed {g : G →ₜ* K | Function.FactorsThrough g q} :=
    Function.isClosed_setOf_factorsThrough q (fun g : G →ₜ* K ↦ (g : G → K))
      (fun x ↦ continuous_eval_const x)
  have hval : IsClosedEmbedding
      (Subtype.val : {g : G →ₜ* K // Function.FactorsThrough g q} → G →ₜ* K) :=
    hclosed.isClosedEmbedding_subtypeVal
  simpa only [Function.comp_def, coe_quotientPullbackHomeomorph_apply] using
    hval.comp (quotientPullbackHomeomorph q hq hcompact).isClosedEmbedding

/-- Pullback along an open quotient homomorphism with weakly locally compact source and
Hausdorff quotient is a closed embedding into the original continuous-hom space. -/
@[to_additive /-- Pullback along an open quotient additive homomorphism with weakly locally
compact source and Hausdorff quotient is a closed embedding into the original continuous-hom
space. -/]
theorem isClosedEmbedding_comp_left_of_isOpenQuotientMap
    [WeaklyLocallyCompactSpace G] [T2Space H] (q : G →ₜ* H)
    (hq : IsOpenQuotientMap q) :
    IsClosedEmbedding (fun f : H →ₜ* K ↦ f.comp q) := by
  exact isClosedEmbedding_comp_left_of_isQuotientMap q hq.isQuotientMap
    (fun _ hs ↦ hq.exists_compact_lift hs)

end ContinuousMonoidHom
