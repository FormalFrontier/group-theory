<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-->

# No small subgroups and discreteness

For a totally disconnected topological group in which every point has a compact
neighborhood, having **no small subgroups** (NSS) is equivalent to discreteness. If the
group is compact, the same condition is equivalent to finiteness of its carrier.
The route to these criteria passes through open subgroups, via van Dantzig's
theorem.

Throughout, `G : Type u` has a group structure and a given `TopologicalSpace G`.
All conclusions concern that topology. Commutativity and nontriviality are not
required.

## The general criterion

[The definition module](../GroupTheory/Topology/Algebra/Group/NoSmallSubgroups.lean)
defines `NoSmallSubgroups G`: there is a neighborhood `U` of `1` such that every
subgroup contained in `U` is the trivial subgroup. The definition requires no
continuity of multiplication or inversion. The instance
`NoSmallSubgroups.of_discreteTopology` supplies this property for a discrete
topology, using the singleton `{1}`.

`NonarchimedeanGroup G` includes `IsTopologicalGroup G` and says that every
identity-neighborhood contains an open subgroup. In
[the nonarchimedean criterion module](../GroupTheory/Topology/Algebra/Group/NoSmallSubgroups/Nonarchimedean.lean),
`noSmallSubgroups_iff_discreteTopology_of_nonarchimedean` gives
`NoSmallSubgroups G ↔ DiscreteTopology G` under precisely this additional class.

The forward theorem is
`NoSmallSubgroups.discreteTopology_of_nonarchimedean`. An open subgroup inside
an NSS neighborhood must be trivial, so `{1}` is open; translation then makes
every singleton open. This implication is an explicit theorem, not a global
instance. The equivalence is not a global simp rule: downstream proofs can
introduce the resulting `DiscreteTopology G` locally, without an instance-search
cycle with the discrete-to-NSS constructor.

## Obtaining open subgroups

[The open-subgroup module](../GroupTheory/Topology/Algebra/Nonarchimedean/TotallyDisconnected.lean)
provides `TotallyDisconnectedSpace.nonarchimedeanGroup G`, assuming
`IsTopologicalGroup G`, `TotallyDisconnectedSpace G`, and
`WeaklyLocallyCompactSpace G`. The last class means that each point admits a
compact neighborhood, not that a compact-neighborhood basis is supplied.
This theorem uses no NSS hypothesis and no ambient `CompactSpace G` assumption.

Here is the geometric argument. Total disconnectedness supplies T₁ separation.
The compatible right uniformity of the given group topology supplies regularity;
these yield Hausdorffness and the separation needed to upgrade weak local
compactness to local compactness. These structures are introduced locally in
the proof, without replacing the topology.

Inside any identity-neighborhood `U`, refine a compact neighborhood to a compact
clopen neighborhood `C` of `1`. Compact-set multiplication separation gives an
identity-neighborhood `V` with `V * C ⊆ C`. For `w ∈ V ∩ V⁻¹`, both `w` and its
inverse send `C` into itself, hence `w * C = C`. Thus the stabilizer of `C` under
the canonical left-translation action contains a neighborhood of `1` and is an
open subgroup. Because `1 ∈ C`, that stabilizer lies in `C`, hence in `U`.
No topology or continuity of an action on `Set G` is needed, and `V` need not be
open.

## Discreteness and the compact consequence

[The totally disconnected criterion module](../GroupTheory/Topology/Algebra/Group/NoSmallSubgroups/TotallyDisconnected.lean)
combines the preceding results:

- `noSmallSubgroups_iff_discreteTopology` assumes `IsTopologicalGroup G`,
  `TotallyDisconnectedSpace G`, and `WeaklyLocallyCompactSpace G`, and concludes
  `NoSmallSubgroups G ↔ DiscreteTopology G`.
- `noSmallSubgroups_iff_finite` assumes `IsTopologicalGroup G`,
  `TotallyDisconnectedSpace G`, and `CompactSpace G`, and concludes
  `NoSmallSubgroups G ↔ Finite G`.

No separate Hausdorff or open-subgroup-basis hypothesis is required. The compact
criterion uses the discreteness criterion in its forward direction, followed by
finiteness of a compact discrete space. Conversely, total disconnectedness gives
T₁ separation, so a finite carrier has discrete topology and therefore NSS.
Finiteness alone would not justify this step for an arbitrary topology: a
nontrivial finite indiscrete group is a counterexample.

For downstream arguments, the first equivalence turns an NSS assumption into a
local discreteness hypothesis. With compactness, the second turns the same
assumption into finiteness, so neither a separate open-subgroup construction nor
an extra separation assumption is needed at the point of use.

## Uniformly bounded exponent

[The bounded-exponent module](../GroupTheory/Topology/Algebra/Group/NoSmallSubgroups/BoundedExponent.lean)
proves `NoSmallSubgroups.discreteTopology_of_pow_eq_one`. For a group with its given
topology, continuous multiplication and NSS, a single natural number `n ≠ 0` with
`g ^ n = 1` for every `g` forces discreteness. No continuity of inversion,
separation, local compactness or commutativity is assumed.

A neighborhood containing no nontrivial subgroup can be pulled back along the
finitely many power maps with exponents below `n`. Each point in the resulting
neighborhood generates a cyclic subgroup inside the original neighborhood, so it
is the identity. Fixed translations then isolate every point. The exponent must
be uniform: pointwise torsion alone does not give this conclusion.

With `CompactSpace G`, `NoSmallSubgroups.finite_of_pow_eq_one` then gives `Finite G`
by the compact-discrete finiteness theorem. Neither implication is a global
instance, and the finiteness conclusion requires compactness.

## Credit

The open-subgroup theorem is classical van Dantzig theory. The formalization
follows Mathlib's nonarchimedean-group API, compatible right-uniformity
construction, clopen-basis and compact-set separation methods, and canonical
group-action stabilizer API. The compact consequence uses Mathlib's compact
discrete finiteness and finite T₁ discreteness results. This guide and the
formalization are AI-assisted work by Formal Frontier Agents.

## License

Apache-2.0. Authors: Formal Frontier Agents.
