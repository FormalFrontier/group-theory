# Results

[Back to the overview](../README.md).

The following results are available in this library.

## Guide navigation

- [Cofinite topologies](#cofinite-topologies)
- [Dense fibers and quotient topologies](#dense-fibers-and-quotient-topologies)
- [Actions, cosets and fixed vectors](#actions-cosets-and-fixed-vectors)
- [Coefficient sums and pushouts](#coefficient-sums-and-pushouts)
- [Topological refinements](#topological-refinements)
- [Finite-index openness and automatic continuity](#finite-index-openness-and-automatic-continuity)
- [Further topological constructions](#further-topological-constructions)
- [Grothendieck extensions](#grothendieck-extensions)
- [Abelian arithmetic](#abelian-arithmetic)
- [Closed Noetherian subsemigroups](#closed-noetherian-subsemigroups)

## Cofinite topologies

- **[Cofinite group topologies](../GroupTheory/Topology/Algebra/Group/Cofinite.lean).**
  On any group with the cofinite topology, inversion and every fixed left or right
  translation are continuous. Joint multiplication is continuous exactly when the
  group is finite, including the trivial group and finite noncommutative groups.
  More generally, an action on an arbitrary cofinite space is jointly continuous
  exactly when the acting cofinite group is finite or the action is pointwise trivial.
  Both statements use the ordinary product topology, not the cofinite topology on
  the set of pairs. No group structure on the action target, commutativity or
  topological-group assumption is needed. A homomorphism from a group to a type with multiplication
  and identity (`MulOneClass`), both carrying their cofinite topologies, is continuous
  exactly when it is trivial or its kernel is finite. More generally, finite kernel
  gives continuity from any group with a T1 topology to a cofinite target. A nontrivial
  continuous homomorphism from a cofinite group to any T0 target has finite kernel;
  consequently, a continuous finite-range homomorphism from an infinite cofinite group
  to a T0 target is trivial. The ambient target need not be finite. The additive
  statements use possibly noncommutative additive groups and `AddZeroClass` targets.
  The underlying [finite-kernel/fiber bridge](../GroupTheory/MonoidHom/Finite.lean) needs
  no topology or target associativity or inverses.
  For any subgroup `H`, the usual left-coset quotient of a cofinite group has the
  cofinite topology when `H` is finite and the indiscrete topology when `H` is infinite.
  It is cofinite exactly when `H` is finite **or the quotient is subsingleton**; in
  particular, the whole subgroup of an infinite group is an essential exception to
  the finite-subgroup converse. No normality, separation or continuity of group
  operations is required. The canonical left action on this quotient is jointly
  continuous exactly when the acting group is finite or `H` is infinite, with no
  normality assumption. For every `H` it is continuous separately in each variable.
  The same results hold for arbitrary additive groups. The
  [integer action on its quotient by twice the integers](../GroupTheoryTest/Topology/Cofinite.lean)
  has distinct inseparable orbit points in the canonical indiscrete topology.
  More generally, a [surjection with finite fibers](../GroupTheory/Topology/Cofinite.lean)
  coinduces the cofinite topology from a cofinite source, while a map with every fiber
  infinite coinduces the indiscrete topology. A surjective homomorphism with finite
  kernel gives the first case with only `MulOneClass` on the target, or `AddZeroClass`
  additively, without a target topology hypothesis. A
  [paired integer-projection example](../GroupTheoryTest/Topology/Cofinite.lean) compares
  finite and infinite kernels, using cofinite topology on each whole product carrier,
  not product topology.

## Dense fibers and quotient topologies

- **[Ultrafilter-limit homomorphisms](../GroupTheory/Topology/Ultrafilter.lean).** For any
  compact Hausdorff monoid with continuous multiplication, taking the limit along a
  fixed ultrafilter defines a surjective abstract homomorphism from its power. When
  the ultrafilter contains all cofinite sets, every fiber is dense; for a nontrivial
  target the map is not continuous at the constant identity family. The direct
  additive API uses an additive monoid with continuous addition. A
  [countable-power example](../GroupTheoryTest/Topology/Ultrafilter.lean) uses the original
  addition and Mathlib discrete topology on `ZMod 3` to give a surjective finite-image
  noncontinuous homomorphism with dense proper zero fiber.
  For any infinite index type `ι` and finite group `H` with its given discrete topology,
  `MonoidHom.exists_surjective_dense_ker_pi` gives a surjective abstract homomorphism
  `(ι → H) →* H` whose normal kernel is dense and has index `Nat.card H`.
  The group need not be commutative, and the two types may lie in independent universes.
  If `H` is nontrivial, the kernel is proper and neither open nor closed; for trivial `H`
  the basic result instead has whole kernel and index one. There is a direct additive
  counterpart, and the original `ℕ → ZMod 3` example has kernel index exactly three,
  neither open nor closed. The homomorphisms are abstract, not assumed continuous.

- **[Dense subgroups and quotient topologies](../GroupTheory/Topology/QuotientGroup.lean).**
  In a group with separately continuous multiplication, the usual left-coset space
  `G/H` has the indiscrete topology exactly when `H` is dense. No normality or
  separation hypothesis is needed. The additive counterpart gives an
  [indiscrete, nondiscrete quotient of index three](../GroupTheoryTest/Topology/QuotientGroup.lean)
  of the original product `ℕ → ZMod 3`. More generally, an open continuous surjection
  has an indiscrete target exactly when all its fibers are dense.

## Actions, cosets and fixed vectors

**Equivariant maps from cosets.** For any group `G`, subgroup `H` and `G`-set `X`,
[`MulActionHom.quotientEquivFixedPoints`](../GroupTheory/GroupAction/Quotient.lean)
constructs `((G ⧸ H) →[G] X) ≃ {x : X // H ≤ MulAction.stabilizer G x}`.
The group and target universes are independent. The forward map evaluates at
`QuotientGroup.mk (1 : G)`; the inverse sends the coset of `g` to `g • x`.
Neither normality of `H` nor transitivity or nonemptiness of `X` is required.
This is a plain equivalence: the `H`-fixed points need not be stable under `G`.
Evaluation formulas, extensionality, uniqueness, target naturality and agreement
with Mathlib's map from stabilizer cosets characterize the construction.
The [permutation-action clients](../GroupTheoryTest/CosetActionHom.lean) recover both
an orbit map and a constant map, with empty-target and one-point boundaries.
For any two subgroups `H, K`,
`MulActionHom.nonempty_quotient_iff_exists_le_map_conj` gives
`Nonempty ((G ⧸ H) →[G] (G ⧸ K)) ↔ ∃ g : G, H ≤ K.map (MulAut.conj g).toMonoidHom`.
Thus a map exists exactly when `H ≤ gKg⁻¹` for some `g`; the corresponding map
sends `[x]` to `[x * g]`. Neither subgroup needs to be normal, and no finiteness
assumption is imposed. The existing
[three-point permutation examples](../GroupTheoryTest/Topology/Algebra/Group/Quotient.lean)
take `K = ⟨(01)⟩` and `g = (12)`: there is an equivariant map
`G ⧸ (gKg⁻¹) → G ⧸ K` even though `gKg⁻¹ ≰ K`, whereas there is no
equivariant map `G ⧸ K → G ⧸ ⊥`.

**Coset-action isomorphisms and conjugacy.** For any group `G : Type u` and
subgroups `H, K`, `Action.nonempty_quotient_iso_iff_exists_eq_map_conj` states

```lean
Nonempty (Action.ofMulAction G (G ⧸ H) ≅ Action.ofMulAction G (G ⧸ K)) ↔
  ∃ g : G, H = K.map (MulAut.conj g).toMonoidHom
```

Thus the canonical left-coset `G`-sets are isomorphic exactly when the subgroups
are conjugate. The group may be infinite and the subgroups need not be normal;
no topology, freeness or faithfulness is assumed.
Given `h : H = K.map (MulAut.conj g).toMonoidHom`,
`Action.quotientIsoOfEqMapConj H K g h` constructs the isomorphism
`[z] ↦ [z * g]`, with inverse `[z] ↦ [z * g⁻¹]`.
The lemmas `Action.quotientIsoOfEqMapConj_hom_mk`,
`Action.quotientIsoOfEqMapConj_inv_mk` and `Action.quotientIsoOfEqMapConj_hom_one`
give the representative formulas and the identity-coset image `[g]`.
This image is the coset of `g`, not a unique representative.
Both maps use `MulActionHom.quotientEquivFixedPoints`; Mathlib's `Action.mkIso`
supplies the categorical isomorphism.
Existence of equivariant maps in both directions alone is not the isomorphism
criterion. See the [coset-action API](../GroupTheory/GroupAction/Quotient.lean)
and [nonnormal permutation examples](../GroupTheoryTest/Topology/Algebra/Group/Quotient.lean).

**Maps between nested coset spaces.** For subgroups `H ≤ K` of any group `G`,
[`MulActionHom.quotientMapOfLE`](../GroupTheory/GroupAction/QuotientMap.lean)
bundles the canonical map `(G ⧸ H) →[G] (G ⧸ K)` for the left actions.
It is surjective, sends each representative to the same representative,
preserves identity inclusions and composition, and commutes with `toQuotient`.
No normality or finiteness assumption is required. When both coset spaces
are finite, the underlying function agrees with Mathlib's finite
`G`-set morphism. The existing [permutation examples](../GroupTheoryTest/Topology/Algebra/Group/Quotient.lean)
exhibit distinct source classes that merge, while a third class stays distinct.

**Restricted coset actions.** For any group `G : Type u` and subgroups `H, K`,
[`MulAction.orbitQuotientQuotientEquivDoubleCoset`](../GroupTheory/GroupAction/DoubleCoset.lean)
identifies the orbits of the canonical restricted `H`-action on `G ⧸ K` with
`H`–`K` double cosets. It sends `orbit(gK)` to `H g K`, with the inverse formula
on the same representative. The stabilizer at `gK`, as a subgroup of `H`, is
`(K.map (MulAut.conj g).toMonoidHom).comap H.subtype`.
Mathlib's `MulAction.orbitEquivQuotientStabilizer` identifies each orbit with
`H ⧸ MulAction.stabilizer H (QuotientGroup.mk (s := K) g)`; the characteristic
smul lemmas in [the coset-action API](../GroupTheory/GroupAction/Quotient.lean)
express equivariance without restricting the independent group and carrier universes.
`MulAction.quotientEquivSigmaDoubleCoset` reindexes Mathlib's primed orbit partition
by double cosets and commutes with the stock sigma action, which fixes the index.
Its fibers are whole orbits: no representative or basepoint section is selected.
Neither subgroup needs to be normal; no finiteness, topology or extra nonemptiness
hypothesis is used. The [three-point permutation model](../GroupTheoryTest/GroupAction/RestrictedCoset.lean)
uses a nonnormal point stabilizer, an identity coset fixed by it, and a second orbit
with two distinct cosets.

**Right transversals and subgroup towers.**
[`GroupTheory.Transversal`](../GroupTheory/Transversal.lean) provides subgroup factors,
representative permutations, changes of representatives, and inner-times-outer
product transversals for arbitrary nested subgroups, without finiteness assumptions.
It generalizes the pure Continuous Group Cohomology formalization
and reuses Mathlib’s complement and subgroup-image API.

**Product-coset orbits and double cosets.** For any group `G : Type u` and
arbitrary subgroups `H, K`,
[`MulAction.orbitQuotientProdQuotientEquivDoubleCoset`](../GroupTheory/GroupAction/DoubleCoset.lean)
identifies the orbits of the canonical diagonal left action of a single `G` on
`(G ⧸ H) × (G ⧸ K)` with `DoubleCoset.Quotient (H : Set G) (K : Set G)`.
The forward map sends `orbit(xH, yK)` to `H (x⁻¹ * y) K`; its inverse sends
`H g K` to `orbit(H, gK)`. These are classes, not unique representatives.
No finiteness, normality or topological assumption is required. Both representative
formulas are simp lemmas. The criterion
`MulAction.orbitRel_prod_quotient_mk_eq_mk_iff` says two pairs represented by
`(x, y)` and `(x', y')` have the same orbit exactly when
`∃ h ∈ H, ∃ k ∈ K, x'⁻¹ * y' = h * (x⁻¹ * y) * k`.
The [three-point permutation examples](../GroupTheoryTest/Topology/Algebra/Group/Quotient.lean)
use `H = K = ⟨(01)⟩` in `S₃`, with orbit sizes three and six and double-coset
sizes two and four. They use both directions of the equivalence and include
an arbitrary-group `H = ⊤` boundary with one orbit class and one double-coset class.

**Invariant equivalence relations.** For a group `G` acting pretransitively on `X`
and a chosen point `a : X`,
[`MulAction.stabilizerInvariantSetoidOrderIso`](../GroupTheory/GroupAction/InvariantSetoid.lean)
identifies subgroups containing `MulAction.stabilizer G a` with left-`G`-invariant
`Setoid`s on `X`, ordered by relation refinement. The group and carrier universes
are independent. For the stock coset action on `G ⧸ H`, the relation at `K ≥ H`
is exactly `Setoid.ker (MulActionHom.quotientMapOfLE hHK)`; on representatives it
is `g⁻¹ * h ∈ K`. The inverse recovers the subgroup from the identity class.
No finiteness, normality or topological assumption is required. The
[nonnormal three-point model](../GroupTheoryTest/GroupAction/InvariantSetoid.lean)
separates this kernel from the orbit relation of the restricted left `K`-action.

**Left exactness of fixed vectors.** For a monoid `G` and modules over any semiring
`R`, [`RepresentationInvariants`](../GroupTheory/RepresentationInvariants.lean) provides
the fixed submodule and the restriction `f.fixedSubmoduleMap` of an intertwining map.
The modules need only be additive commutative monoids, and all carrier universes are
independent. `fixedSubmoduleMap_injective` preserves ambient injectivity. For an
injective `f`, `range_fixedSubmoduleMap` identifies the restricted range with
`(LinearMap.range f.toLinearMap).comap σ.fixedSubmodule.subtype`, where `σ` is the
target representation. Hence `fixedSubmoduleMap_bijective` restricts an ambient
bijection to a bijection of fixed submodules. If `f` is injective and
`Function.Exact f g`, then `fixedSubmoduleMap_exact` proves
`Function.Exact f.fixedSubmoduleMap g.fixedSubmoduleMap` on the original module and
representation data. No finiteness, topology, group structure on `G` or additive
inverses are required. The identity, composition, inclusion and unique-factorization
APIs are compatible with the usual submodule maps. When `R` is a commutative ring,
`G` is a group and the module is an additive commutative group, the fixed submodule
equals Mathlib's existing invariant submodule.
The module explains a nontrivial split sequence for the coordinate-swap action on `ℕ²`
and why the sign action on `ℤ`, reduced modulo two, does not preserve surjectivity.

- **[Functoriality of fixed submodules](../GroupTheory/RepresentationFixedFunctoriality.lean).**
  An equivariant semilinear map over an arbitrary semiring homomorphism carries fixed
  vectors to fixed vectors. The source fixed submodule lies in the comap of the target
  fixed submodule, with equality when the given map is injective. Both original scalar
  and module structures are retained; no scalar-surjectivity assumption is needed.
  Precomposing a representation with a monoid homomorphism enlarges its fixed submodule,
  with equality for a surjective homomorphism and, in particular, a multiplicative equivalence.

**Products of fixed submodules.** For representations `ρ` on `A` and `τ` on `B`
of the same monoid `G` over any semiring `R`,
`Representation.fixedSubmodule_prod` proves the literal submodule equality

```lean
(ρ.prod τ).fixedSubmodule = ρ.fixedSubmodule.prod τ.fixedSubmodule
```

Here `A` and `B` are their given additive commutative monoid modules; their
universes, and those of `R` and `G`, are independent. The ambient product module
is induced from these original factors, not an independently supplied module
structure. There are no group, finiteness, additive-inverse or commutative-scalar
assumptions. `mem_fixedSubmodule_prod` is the coordinatewise membership criterion.

The generic [linear-algebra supplement](../GroupTheory/LinearAlgebra/Prod.lean)
`Submodule.prodEquiv P Q : (P.prod Q) ≃ₗ[R] P × Q` splits and joins coordinates.
It has no acting-monoid parameter. In the
[representation API](../GroupTheory/RepresentationInvariants.lean),
`fixedSubmoduleProdEquiv ρ τ` composes `LinearEquiv.ofEq` along the displayed equality
with this generic equivalence. Its forward coordinate and inverse ambient-pair
simp lemmas, restricted-projection characterization and inclusion identity
identify the map on the original modules. `fixedSubmoduleProdEquiv_naturality`
commutes with any supplied pair of intertwiners into two independently
universe-polymorphic target modules. The product intertwiner in that identity is
assembled from Mathlib's existing `fst`, `snd`, `comp` and common-domain `prod`;
there is no replacement product-intertwiner construction.

For example, let the infinite non-group monoid `Multiplicative ℕ` act on `ℕ²`
by powers of the swap and on `ℕ³` by powers of the cyclic rotation. Fixedness at
exponent one forces respectively `(a, a)` and `(b, b, b)` and implies fixedness
at every exponent. Both fixed submodules are proper and nonzero. The equivalence
splits the product-fixed vector `((a, a), (b, b, b))` into two independent
parameters over a semiring without additive inverses. Zero modules and trivial
actions are also allowed.

Under the stronger commutative-ring, group and additive-group hypotheses,
`Representation.invariants_prod` gives
`(ρ.prod τ).invariants = ρ.invariants.prod τ.invariants` on the same data.
Rewriting the three occurrences of `fixedSubmodule` in `fixedSubmoduleProdEquiv`
using `fixedSubmodule_eq_invariants` gives the corresponding linear equivalence
without a second pairing definition. These results reuse Mathlib's product,
submodule and intertwining APIs and this library's existing fixed-vector
restrictions; they do not assert coverage of a book passage.

**Arbitrary indexed products of fixed submodules.** For `I : Type uI`, an original
family `M : I → Type uM` of additive commutative monoids with their given `R`-module
structures, and `ρ i : Representation R G (M i)`, the
[indexed-product API](../GroupTheory/RepresentationPi.lean) constructs
`Representation.pi ρ` using `LinearMap.piMap (fun i => ρ i g)` at `g`. It proves

```lean
(Representation.pi ρ).fixedSubmodule =
  Submodule.pi Set.univ (fun i => (ρ i).fixedSubmodule)
```

Only `[Semiring R]` and `[Monoid G]` are required. The scalar, monoid, index and fiber
universes are independent, and the product has its original dependent-function module
structure. No finite or nonempty index, scalar commutativity, nonzero condition,
additive inverses or invertible actions are assumed. The named criterion
`mem_fixedSubmodule_pi` exchanges the two universal quantifiers in fixedness; it is
not a global simplification rule.

`isIntertwiningMap_pi_iff` characterizes compatibility of an arbitrary linear map
from an independently universe-polymorphic representation by compatibility of its
composites with the stock `LinearMap.proj`. The theorem
`existsUnique_isIntertwiningMap_pi` uses `LinearMap.pi`, `proj_pi` and `pi_proj_comp`
to assemble supplied intertwining coordinates uniquely, without another product engine.

The generic [linear enrichment](../GroupTheory/LinearAlgebra/Pi.lean)
`Submodule.piEquiv p : (Submodule.pi Set.univ p) ≃ₗ[R] (∀ i, p i)` adds linear fields
to Mathlib's `Equiv.subtypeEquivRight` followed by `Equiv.subtypePiEquivPi`.
`fixedSubmodulePiEquiv ρ` composes equality transport with this enrichment. Its forward
and inverse coordinate formulas and inclusion identity retain the original ambient
coordinates. `fixedSubmodulePiEquiv_naturality` uses the supplied original family of
intertwiners into fibers in an independent target universe. Its product map bundles
`LinearMap.piMap` with derived compatibility via the existing pointwise intertwiner
constructor. In the separate commutative-ring/group/additive-group context,
`invariants_pi` follows by the same-data `fixedSubmodule_eq_invariants` bridge, without
a second invariants-equivalence definition. The independently heterogeneous binary API
above is unchanged.

For index type `ℕ`, let the free monoid on one generator act by swap on every `ℕ²`
fiber. The fixed fibers are proper nonzero diagonals. The all-`(1, 1)` sequence has
infinite support and is fixed, while a sequence with `(1, 0)` at one coordinate is not.
Coordinatewise doubling is a nonidentity intertwiner. The alternative generator action
`(a, b) ↦ (a, 0)` is noninvertible and has a proper nonzero fixed horizontal axis.
For an empty index type, both sides have the unique empty function and the fixed
submodule is the whole product. These examples explain the full-product and weak
algebraic hypotheses; they assert no external-source coverage.

- **[Direct sums of fixed submodules](../GroupTheory/RepresentationDirectSum.lean).** For arbitrary
  families of monoid representations over a semiring on additive commutative monoids,
  the fixed submodule of the algebraic direct sum is canonically linearly equivalent
  to the direct sum of the fixed submodules, preserving every ambient coefficient.
  Arbitrary linear maps from these fixed fibers extend uniquely to the fixed submodule
  of the direct sum, without ambient extensions or an action on the target.
- **[Norms and fixed-vector surjections](../GroupTheory/RepresentationNorm.lean).** For finite-group
  representations over a semiring on additive commutative monoids, a surjective
  intertwining map is surjective on fixed submodules if every fixed target vector
  is a value of the target norm. It suffices that multiplication by the group order
  is surjective on the target fixed submodule, or bijective on the ambient target.
  No divisibility or cancellation in the source is required. The
  [norm naturality API](../GroupTheory/RepresentationNormNaturality.lean) allows the
  two coefficient carriers to lie in independent universes.

**Action automorphisms and centralizers.** For `(G : Type u) [Group G]`,
`(C : Type v) [Category.{w} C]` and `A : Action C G`,
`Action.autEquivCentralizer A` identifies `CategoryTheory.Aut A` with
`Subgroup.centralizer (Set.range A.ρAut)` in `Aut A.V`. Its forward value is
exactly `(Action.forget C G).mapIso α`; its inverse has underlying isomorphism
the supplied centralizer element, equipped with equivariance.
The three universes are independent.
`Action.autEquivPermCentralizer G X` specializes this to
`Aut (Action.ofMulAction G X) ≃* centralizer (range (MulAction.toPermHom G X))`
for an arbitrary `G`-set `X : Type v`, with the centralizer taken in
`Equiv.Perm X`, using stock `Aut.mulEquivPerm`
(`CategoryTheory.Aut.mulEquivPerm`).
The characteristic lemmas identify all four forward/inverse hom/inv coordinates,
the bundled forgetful homomorphisms, and equality by forward evaluation.
Multiplication is ordinary composition `α (β x)` on both sides.
Neither result assumes finiteness, transitivity, faithfulness, a point, nonemptiness
or topology.

For a pretransitive `G`-action and `x : X`,
`MulAction.isPretransitive_centralizer_iff_stabilizer_normal` characterizes
pretransitivity of this canonical image centralizer by normality of the point
stabilizer. The general helper
`MulAction.stabilizer_normal_of_pretransitive_commuting` only needs a commuting
pretransitive scalar operation `SMul H X`, with no monoid structure on `H` or
pretransitivity of `G`. These are general group-action facts, not freeness criteria.
The [clients](../GroupTheoryTest/ActionCentralizer.lean) use independent swaps
`(01)` and `(12)` of a trivial three-point action, whose products send `0` to
`1` and `2` in the two orders, and the unique automorphism of the empty action.
See the [API](../GroupTheory/GroupAction/Centralizer.lean) and the
[normal-stabilizer clients](../GroupTheoryTest/GroupAction/CentralizerTransitivity.lean).

**Automorphisms of transitive actions.** For a group `G` acting transitively
on `X` and a chosen point `x`, `MulAction.normalizerQuotientEquivAut`
identifies `N_G(G_x) / G_x` with the canonical
`CategoryTheory.Aut (Action.ofMulAction G X)`. The group and set universes
are independent; there is no finiteness, normality, faithfulness or freeness
assumption. The denominator is the stabilizer as a subgroup of its normalizer.
`Action.normalizerToAut` constructs inverse right translation on `G / H` for
any subgroup `H`, with kernel `H` inside `N_G(H)` and same-object agreement
with Mathlib's finite-normal `Action.FintypeCat.toEndHom` after `Aut.toEnd`
and `FintypeCat.incl.mapAction`/`mapEnd`.
Automorphisms multiply by ordinary function composition, so `[n]` sends
`g • x` to `(g * n⁻¹) • x`. May's displayed `g * n` formula reverses multiplication
under this convention; the abstract isomorphism remains valid with inverse
parameter. See the [action API](../GroupTheory/GroupAction/Automorphism.lean)
and its [noncommutative and nonnormal clients](../GroupTheoryTest/GroupAction/Automorphism.lean).

**Finite free bases and finite-index subgroups.** The
[free-group rank module](../GroupTheory/FreeGroup/Rank.lean) proves that every free
basis of a finitely generated group has a finite indexing type of cardinality
`Group.rank G`. For every finite-index subgroup `H` of a finitely generated free
group, it proves `Group.rank H + H.index = Group.rank G * H.index + 1`, including
ambient rank zero and without normality or a separate finite-generation
hypothesis on `H`. Mathlib supplies subgroup freeness and finite generation.
The [parity-kernel client](../GroupTheoryTest/FreeGroup/Rank.lean) constructs an
index-two subgroup of `FreeGroup (Fin 2)`, computes its rank as three and uses
the existing basis-reindexing API to give a basis indexed by `Fin 3`.

### Index-two subgroups and explicit generators

For an arbitrary group, index-two subgroups correspond to nontrivial homomorphisms
into `Multiplicative (ZMod 2)`. The API includes kernel uniqueness, characteristic
values, and pullback along surjective homomorphisms. Normality follows from index
two and is not an additional hypothesis.

For a free group basis `β` indexed by `Fin 2`, write `a = β 0` and `b = β 1`.
The three nontrivial generator-value patterns have the following kernel generators:

| Values on `a,b` | Explicit generators |
| --- | --- |
| `10` | `a²`, `b`, `a * b * a⁻¹` |
| `01` | `b²`, `a`, `b * a * b⁻¹` |
| `11` | `a²`, `b * a⁻¹`, `a * b` |

The three kernels are distinct and exhaust the index-two subgroups. The word
spanning formulas themselves apply to any two-generated group with an index-two
subgroup; they assert generation, not freeness of the displayed triples.

See the overview for [index-two subgroups and explicit generators](../README.md#headline-results).

## Coefficient sums and pushouts

- **[Coefficient-sum relations](../GroupTheory/Finsupp/CoefficientSum.lean).**
  Over any semiring `R`, for an additive commutative group `M` with an `R`-module
  structure and any specified `i₀ : ι`, the kernel of the coefficient sum on
  `ι →₀ M` is the `R`-span of `single i m - single i₀ m`. An `R`-linear map into
  an additive commutative monoid with an `R`-module structure factors uniquely
  through this sum exactly when its singleton components agree, equivalently when
  it vanishes on the kernel. The factor is composition with `single i₀`. The index type
  may be infinite; the target need not be cancellative or an additive group.

- **[Group pushouts over a trivial vertex](../GroupTheory/Category/Grp/Pushout.lean).**
  For a group homomorphism `f : A →* B` and any trivial group `T`, the canonical
  quotient `B / normalClosure (range f)` with its quotient leg from `B` and
  trivial leg from `T` is the pushout. In every group pushout of this span,
  the leg from `B` is surjective with kernel exactly `normalClosure (range f)`.
  The unbundled universal property allows independent source, vertex and target
  universes and monoid targets; the categorical square uses `GrpCat`'s ambient
  universe. No commutativity, injectivity or exactness hypothesis is required.

## Topological refinements

**Finite-neighborhood joint continuity.** Let `S`, `X` and `Y` be topological
spaces in independent universes, and let `f : S × X → Y`. The pointwise criterion
`ContinuousAt.of_finite_mem_nhds_right` gives continuity at `(s, x)` assuming:

- `V` is a finite neighborhood of `x`;
- for every `y ∈ V`, the row `t ↦ f (t, y)` is continuous at `s`;
- the single column `y ↦ f (s, y)` is continuous at `x`.

Only the selected rows need to be continuous at that point; this statement does
not require global continuity of every row or every column. The neighborhood
need not itself be open.

For global continuity, `Continuous.of_finite_nhds_right` assumes that every point
of `X` has some finite neighborhood, and that all rows and all columns are
continuous. `Continuous.of_finite_right` supplies the same conclusion under
`[Finite X]` and those two separate-continuity hypotheses. The finite space has
its given topology: discreteness, T0 and a chosen finite enumeration are not
additional requirements.

For topological spaces `M` and `X` in independent universes, the same criteria
apply to a primitive scalar operation `[SMul M X]`.
`ContinuousSMul.of_finite_nhds_right` constructs `ContinuousSMul M X` from
`[ContinuousConstSMul M X]`, continuity of each orbit map `m ↦ m • x`, and a
finite neighborhood at every point of `X`. Thus both fixed-scalar maps and orbit
maps are required to be continuous. `ContinuousSMul.of_finite_right` replaces
the neighborhood hypothesis with `[Finite X]`. Neither constructor assumes
monoid or group laws, and no finiteness condition is imposed on `M`. These
criteria are distinct from the orbit/open-stabilizer criteria for group actions
on discrete spaces below. See
[the finite-neighborhood continuity API](../GroupTheory/Topology/SeparateContinuity.lean).

**Fixed-action continuity.**

- `Topology.IsCoinducing.continuousConstSMul` transports continuity of fixed
  scalar actions from `X` to `Y` along an equivariant coinducing map
  `f : X →[M] Y`, assuming `ContinuousConstSMul M X`, with topologies on
  `X` and `Y` and primitive actions of `M` on both. Scalar, source and target
  universes are independent; no scalar topology, action laws or surjectivity
  is required. `Topology.IsCoinducing.continuousConstVAdd` gives the
  corresponding transport from `X` to `Y` for fixed vector additions,
  assuming `ContinuousConstVAdd M X`. See
  [the transport API](../GroupTheory/Topology/Algebra/ConstMulAction.lean).
- `QuotientGroup.continuousConstSMul` supplies continuous fixed left actions on
  the canonical coinduced left-coset quotient `G ⧸ H` for every subgroup `H`,
  assuming only `Group G`, `TopologicalSpace G` and `ContinuousConstSMul G G`.
  No normality, right continuity, joint multiplication, continuous inversion,
  separation, compactness or index assumption is required. The additive instance
  is `QuotientAddGroup.continuousConstVAdd`. See
  [the coset quotient API](../GroupTheory/Topology/Algebra/Group/Quotient.lean).

**Continuous actions on discrete spaces.** For a group with a topology whose fixed
left translations are continuous, acting on a discrete space,
[`MulAction.continuous_smul_const_iff_stabilizer_isOpen`](../GroupTheory/Topology/Algebra/MulAction.lean)
characterizes continuity of each orbit map by openness of its stabilizer.
`MulAction.continuousSMul_iff_stabilizer_isOpen` characterizes joint continuity by
openness of all stabilizers. Additive versions are included. Joint continuity of
multiplication, continuity of inversion, separation and normality are not required.

- **[Actions of preirreducible groups](../GroupTheory/Topology/Algebra/MulAction/Irreducible.lean).**
  For any group with a preirreducible topology and continuous inversion, an action
  on an arbitrary topological space is jointly continuous exactly when each orbit
  point is inseparable from the point acted on. No separation assumption on the
  target or continuity of multiplication in the actor is required. For a T0 target,
  this makes the action pointwise trivial. The additive result requires continuous
  negation. These results use the given action and the ordinary product topology.

**Continuous equivariant maps from cosets.**
[`ContinuousMulActionHom`](../GroupTheory/Topology/Algebra/MulActionHom.lean) bundles
continuous maps compatible with arbitrary scalar operations along any function
`φ : M → N`. It carries the topology induced from compact-open continuous maps,
not the pointwise function topology. For a group `G`, arbitrary subgroup `H` and
a jointly continuous action on `X`,
[`ContinuousMulActionHom.quotientHomeomorphFixedPoints`](../GroupTheory/Topology/Algebra/Group/Quotient.lean)
expresses the coset-map universal property as a homeomorphism onto the canonical
`H`-fixed-point subspace. It assumes continuity of right translations of `G`,
with no continuous inversion, left-translation continuity, normality, closedness,
local compactness or separation assumption. Its forward map evaluates at `[1]`;
its inverse sends `[g]` to `g • x` and forgets to the algebraic equivalence above.
The [circle model](../GroupTheoryTest/Topology/Algebra/ContinuousCosetMap.lean) constructs
two distinct continuous maps using the parameters `1` and `-1`, directly from the
algebraic equivalence and quotient continuity, without using the homeomorphism.

**Dense maps on units.** For monoids `M` and `N`,
[`DenseRange.units_map`](../GroupTheory/Topology/Algebra/Group/Units.lean) shows that
a dense homomorphism `f : M →* N` which reflects units induces a dense map on unit
groups if the canonical coercion `Nˣ → N` is an open embedding. Only `N` needs a
topology; no continuity assumption on `f` is imposed. The
[examples](../GroupTheoryTest/Topology/Algebra/Group/Units.lean) verify the hypotheses
for the rational inclusion into the reals and use the integer quotient modulo five
to demonstrate why unit reflection cannot be omitted.

**Open, closed and clopen subgroups and left-coset quotients.**
For an arbitrary subgroup `H`, the following results require only `Group G`, a
supplied `TopologicalSpace G` and continuity of fixed left translations
(`ContinuousConstSMul G G`), using the canonical left-coset quotient `G ⧸ H`
with its coinduced topology:

- `Subgroup.isOpen_iff_discreteTopology_quotient`: `H` is open iff the quotient
  is discrete.
- `Subgroup.isClosed_iff_t1Space_quotient`: `H` is closed iff the quotient is T1.
- `Subgroup.isClopen_iff_isOpen`: `H` is clopen iff it is open, without an
  index assumption.
- `Subgroup.isOpen_iff_isClosed` and `Subgroup.isClopen_iff_isClosed`: with
  `H.FiniteIndex`, openness, closedness and clopenness are equivalent.

None of these characterizations requires compactness. The separate
`Subgroup.finiteIndex_of_isOpen` adds `CompactSpace G` to deduce finite index
from openness. None assumes normality, right translations, joint multiplication,
continuous inversion or ambient separation. See
[the subgroup and quotient API](../GroupTheory/Topology/Algebra/Group/Quotient.lean)
and [the clients](../GroupTheoryTest/Topology/Algebra/Group/Quotient.lean). The clients
supply open and closed singleton fibers, finite coset types and same-object
agreement with Mathlib's stronger separately continuous API. Every observer
`G ⧸ H → Y`, for any space `Y`, is continuous when `H` is closed and of finite
index; no compactness or explicit openness premise is needed. Their concrete
model is cofinite additive integers, tagged multiplicatively, times discrete
permutations of three points, with subgroup whole first factor times the cyclic
group generated by `(01)`. Supporting proof terms describe an open, proper,
nonnormal subgroup of index three in an infinite compact non-T2 group with
nonjoint multiplication, independently of the subgroup and quotient results.
This first example also has continuous right translations and inversion: it does
not distinguish left
from both-sided constant continuity.

The same client module supplies a second example with the permutation topology
induced by its canonical left-coset projection to an **explicitly discrete**
auxiliary target. The construction does not read the quotient's dependent
coinduced topology as its input.
Supporting terms give all canonical left translations continuous but right
translation by `(12)`, inversion and joint multiplication discontinuous; the
finite permutation space is not T0. The product with the same cofinite integer
factor is infinite and compact, has the same clopen, proper, nonnormal index-three
subgroup and fails right/separate continuity, inversion and T0/T1/T2. Independent
closedness and algebraic finite-index witnesses let the closed/T1 and
finite-index open/clopen APIs apply to both strict examples without a both-sided
premise.

- `AddSubgroup.isClopen_iff_isOpen` and `AddSubgroup.isOpen_iff_isClosed` give their
  noncommutative additive counterparts under continuity of fixed left additions.
- The criteria compose with the identity-neighborhood and interior APIs: a closed
  finite-index subgroup is a neighborhood of the identity, or of zero additively.

- **[Locally closed subgroups](../GroupTheory/Topology/Algebra/Group/LocallyClosed.lean).**
  In a group with separately continuous multiplication and continuous inversion,
  a subgroup is closed exactly when it is a neighborhood of the identity within
  its closure, equivalently locally closed at the identity, at any specified
  member, or globally locally closed. The additive API assumes separately
  continuous addition and continuous negation. No joint continuity, separation,
  normality or commutativity is required.

**Total boundedness from finite-index subgroup bases.** For `G : Type u`
with `[Group G] [UniformSpace G] [IsLeftUniformGroup G]`, take any index type
`ι : Type v`, predicate `p : ι → Prop` and family `H : ι → Subgroup G`.
The universes `u` and `v` are independent. Given
`B : (nhds (1 : G)).HasBasis p (fun i => (H i : Set G))`,
`Filter.HasBasis.totallyBounded_univ_iff_subgroup_finiteIndex` states

```lean
TotallyBounded (Set.univ : Set G) ↔ ∀ i, p i → (H i).FiniteIndex
```

The additive form,
`Filter.HasBasis.totallyBounded_univ_iff_addSubgroup_finiteIndex`, uses
`[AddGroup A] [UniformSpace A] [IsLeftUniformAddGroup A]`, a basis at `0`
and additive subgroups, with the same independent index universe and predicate.
Neither form assumes normality, separation, countability, a nonempty index type,
completeness or compactness. See the
[total-boundedness criterion](../GroupTheory/Topology/Algebra/Group/TotalBounded.lean)
and its [applications](../GroupTheoryTest/Topology/FiniteIndex.lean): in the 3-adic
integers, closed norm balls of radius `(1 / 3) ^ n` identify with powers of `(3)`
and give the neighborhood basis, while reduction to finite `ZMod (3 ^ n)` gives
finite index without using compactness. Both the additive criterion and the
multiplicative criterion on `Multiplicative ℤ_[3]` are applied. In the infinite
discrete group `ℤ`, the zero subgroup is a neighborhood basis but has infinite
index; applying the additive criterion shows that `ℤ` is not totally bounded.

**Compact open subgroup neighborhoods.** Every identity neighborhood in a
locally compact totally disconnected topological group contains a compact open
subgroup; neighborhoods need not be open, and no ambient compactness or separate
Hausdorff hypothesis is imposed. `OpenSubgroup.nhds_one_hasBasis_compact` expresses
the neighborhood basis. For any compact open set, `OpenSubgroup.leftStabilizer`
constructs its open left-translation stabilizer, even if the set misses the identity.
When the set contains the identity, that subgroup is compact and contained in the set.
The construction requires neither local compactness nor total disconnectedness.
See [the subgroup API](../GroupTheory/Topology/CompactOpenSubgroup.lean)
and [the boundary clients](../GroupTheoryTest/Topology/CompactOpenSubgroup.lean).

**Open kernels and finite images.** For a continuous homomorphism from a
nonarchimedean group, a target identity neighborhood containing no nontrivial
subgroup forces an open kernel, without source compactness, commutativity or a
separation assumption on the target. An open kernel makes any group homomorphism
locally constant, even without continuity or a topology on the target.
Compactness of the source then gives finite image and a finite, discrete
quotient by the kernel; Mathlib's `QuotientGroup.kerLift` gives the unique
factorization, injective onto the image but not necessarily surjective onto
the target. The centered half-circle supplies the target neighborhood for
circle-valued characters, including those on compact locally compact totally
disconnected groups via the compact-open subgroup basis. See
[the general API](../GroupTheory/Topology/OpenKernel.lean),
[the circle specialization](../GroupTheory/Topology/CircleCharacter.lean) and
[a nonconstant two-element character](../GroupTheoryTest/Topology/OpenKernel.lean).

**Rational-circle character subgroups.** A character of an abelian group has
finite image precisely when it has finite order as a whole character. For
topological abelian groups, characters with open kernels form a subgroup;
compactness makes every such character finite-order, without a Hausdorff
assumption. The converse holds for compact Hausdorff groups containing a dense
finitely generated subgroup, using openness of finite-index subgroups. Both
subgroups admit precomposition, with continuity required only for the
open-kernel restriction. See
[the character subgroup API](../GroupTheory/Topology/CharacterSubgroups.lean)
and [the finite and 2-adic examples](../GroupTheoryTest/Topology/CharacterSubgroups.lean).

**Rational-circle and continuous characters.** The rational additive circle embeds
in the unit circle, and every finite-order circle point has a rational preimage.
For a compact nonarchimedean commutative additive group, open-kernel
rational-circle characters identify additively with its continuous
circle-valued characters.
If the group is additionally Hausdorff and has a dense finitely generated
additive subgroup, its finite-order characters supply that domain. These
comparisons neither cover all abstract rational-circle characters nor give a
topological equivalence. See [the inclusion](../GroupTheory/Topology/RationalCircle.lean),
[both comparison maps](../GroupTheory/Topology/RationalCircleCharacter.lean) and
[the finite and 2-adic clients](../GroupTheoryTest/Topology/RationalCircleCharacter.lean).

### Circle equivalences and codomain transport

- **Circle equivalences and codomain transport.** `AddCircle.continuousAddEquivCircle`
  identifies every nonzero-period additive circle with `Additive Circle`, using the
  exponential `x ↦ exp (2 * π / T * x)`. Codomain transport gives homeomorphisms of
  continuous homomorphism spaces for monoids with arbitrary topologies, and continuous
  multiplicative equivalences for commutative codomains with continuous multiplication.
  The period-one specialization transports continuous additive characters pointwise.

- **[Type-tag transport](../GroupTheory/Topology/TypeTags.lean).** Continuous monoid
  homomorphisms `Multiplicative A →ₜ* B` and continuous additive homomorphisms
  `A →ₜ+ Additive B` are identified by a compact-open homeomorphism, for any additive
  monoid `A` and monoid `B` with arbitrary topologies. For a commutative `B` with continuous
  multiplication this is also an additive equivalence on the pointwise hom spaces.

## Finite-index openness and automatic continuity

**Finite index from dense finite generation.** In a compact Hausdorff
commutative topological group with an abstractly finitely generated dense
subgroup, every positive-power range has finite index and is open. Every
abstract finite-index subgroup is therefore open, without assuming that it is
closed. Additive versions use positive natural-number scalar maps. The dense
integer subgroup of the 2-adic integers witnesses doubling with finite-index
open range and a proper finite-index reduction kernel; the zero scalar map
has infinite-index range. See [the subgroup results](../GroupTheory/Topology/FiniteIndex.lean)
and [the 2-adic examples](../GroupTheoryTest/Topology/FiniteIndex.lean).

  More generally, closedness of that range suffices without compactness or ambient
  separation. Every abstract finite-index subgroup in the compact Hausdorff case is
  open, without assuming it closed.
  An [abstract homomorphism](../GroupTheory/Topology/OpenKernel.lean) from such a compact
  group with finite range is locally constant for any target with multiplication and
  identity (`MulOneClass`; additively `AddZeroClass`). No target topology is needed;
  local constancy gives continuity for any subsequently given target topology.
  Separately, a homomorphism into any monoid has open kernel and is locally constant
  if one fixed positive exponent annihilates its whole image, with no target topology
  or continuity assumed. The additive counterparts use the range of `x ↦ n • x` and,
  for the fixed-positive-scalar condition, additive monoid targets.

- **[Finite-index openness and automatic continuity](../GroupTheory/Topology/AutomaticContinuity.lean).**
  For a group with a topology and continuous fixed left translations, the following are
  equivalent: every finite-index subgroup is open; every abstract homomorphism to a finite
  discrete group is continuous; and every action on an arbitrary discrete space with finite
  individual orbits is jointly continuous. The source, finite-target and action-carrier
  universes are independent. Each converse to subgroup openness holds even for an arbitrary
  source topology, without continuity of translations or group operations. Subgroups need
  not be normal. The additive counterparts apply to possibly noncommutative additive groups
  and require no additive structure on action carriers.

  Every abstract homomorphism from a compact Hausdorff commutative topological group with a specified
  dense abstractly finitely generated subgroup into a compact nonarchimedean group is
  continuous. The target need not be commutative or Hausdorff, and the image may be
  infinite. The additive homomorphism counterpart has the same scope; this result does
  not assert local constancy. Every abstract action of the same source on an arbitrary
  discrete space with finite individual orbits is jointly continuous, without requiring
  a finite total action image. Its additive action counterpart also uses an arbitrary
  carrier, with no additive structure required on it.

- **[Finite-index openness under quotients and sections](../GroupTheory/Topology/FiniteIndex/Descent.lean).**
  For groups with arbitrary given topologies, openness of every finite-index subgroup
  descends along homomorphisms that reflect open preimages of all subsets. In particular,
  this applies to a homomorphism with a continuous right-inverse function (not necessarily
  a homomorphism), a quotient-map homomorphism, a surjective open homomorphism, and the
  canonical quotient by any normal subgroup. No topological-group or separation
  hypothesis is needed. Multiplicative homeomorphisms preserve the condition in both
  directions, and the same results hold additively. A
  [nonlinear section of the integer projection](../GroupTheoryTest/Topology/FiniteIndex/Descent.lean)
  illustrates the function-level section theorem.

The property that every finite-index subgroup is open descends to finite-index subgroups
with their induced topology, and from arbitrary dependent products to each factor, without
continuity assumptions on group operations. This property also pulls back along a continuous
injective group homomorphism with finite-index range, without requiring a topological
embedding; see [`Injective`](../GroupTheory/Topology/FiniteIndex/Injective.lean).
With continuous fixed left translations, the property ascends from any open subgroup and is
preserved by binary and finite dependent products. Under the same assumption, for any given
finite-index subgroup the ambient property is equivalent to that subgroup being open and all
of its finite-index subgroups
being open in the induced topology.

The subgroup identity-neighborhood and identity-interior criteria also require only
continuous fixed left translations. All these results have additive versions without a
commutativity assumption. See
[`AutomaticContinuity`](../GroupTheory/Topology/AutomaticContinuity.lean) and
[`FiniteIndex`](../GroupTheory/Topology/FiniteIndex.lean).

## Further topological constructions

**Open quotients of compact spaces.** If `f : X → Y` is an open quotient map,
`X` is compact, Hausdorff and totally disconnected, and `Y` is Hausdorff,
`Topology.IsOpenQuotientMap.totallyDisconnectedSpace` gives total
disconnectedness of `Y`. This is a general result about topological spaces,
independent of group structure. See [the theorem](../GroupTheory/Topology/OpenQuotient.lean)
and [a non-injective finite projection](../GroupTheoryTest/Topology/OpenQuotient.lean).

**Discrete-valued maps on compact spaces and groups.** For any compact space
`X` and discrete space `Y`, `ContinuousMap.discreteTopology_of_compactSpace`
gives discreteness of the existing compact-open topology on `C(X, Y)`.
For any compact topological group `G`, every `f : C(G, Y)` descends through
an open normal subgroup: `ContinuousMap.exists_openNormalSubgroup_factor`
gives `N : OpenNormalSubgroup G` and `fbar : C(G ⧸ N.toSubgroup, Y)` with
`∀ g, fbar (QuotientGroup.mk g) = f g`. Mathlib's open-subgroup quotient APIs
make this quotient finite and discrete. Neither theorem requires Hausdorffness
or nonemptiness of the spaces; factorization requires neither total
disconnectedness nor commutativity of `G`, and no algebraic structure on `Y`
or homomorphism condition on `f`. Discreteness is a theorem, not a new global
instance. See [the map-space theorem](../GroupTheory/Topology/ContinuousMap/CompactDiscrete.lean),
[the group factorization](../GroupTheory/Topology/Algebra/CompactGroup/DiscreteFactor.lean),
[isolated maps and observers](../GroupTheoryTest/Topology/ContinuousMap/CompactDiscrete.lean)
and [right-invariance and separation clients](../GroupTheoryTest/Topology/Algebra/CompactGroup/DiscreteFactor.lean).

**Finite-coordinate factorization on compact group powers.** For an arbitrary
index type `I`, compact topological group `G` and discrete space `Y`, every
`f : C(I → G, Y)` factors through finitely many quotient coordinates.
`ContinuousMap.exists_finset_openNormalSubgroup_pi_factor` gives
`s : Finset I`, one `N : OpenNormalSubgroup G` and
`fbar : C((s → G ⧸ N.toSubgroup), Y)` with the canonical triangle
`∀ x : I → G, fbar (fun i : s => QuotientGroup.mk (x i)) = f x`.
The topologies are the canonical product and group-quotient topologies.
It is the **selected finite stage** `s → G ⧸ N.toSubgroup`, not the full
quotient power over `I`, that is finite and discrete. The types `I`, `G` and
`Y` have independent universes, and neither `I` nor `Y` needs to be finite.
The selected set may be empty. No additional nonemptiness, Hausdorffness,
commutativity, total disconnectedness or profinite hypothesis is required;
`Y` needs no group structure and `f` need not be a homomorphism.

The supporting cylinder API is more general: for arbitrary `I` and a family
`A : I → Type*` with only `[∀ i, Group (A i)]` and
`[∀ i, TopologicalSpace (A i)]`, any
`M : OpenNormalSubgroup (∀ i, A i)` contains a finite cylinder.
`OpenNormalSubgroup.exists_finset_pi_subset M` gives `s : Finset I` and
`N : ∀ i : s, OpenNormalSubgroup (A i)` such that
`∀ x : (∀ i, A i), (∀ i : s, x i ∈ N i) → x ∈ M`.
For a constant family and `M : OpenNormalSubgroup (I → G)`,
`OpenNormalSubgroup.exists_finset_uniform_pi_subset M`
gives one `N : OpenNormalSubgroup G` with
`∀ x : I → G, (∀ i : s, x i ∈ N) → x ∈ M`.
Coordinates outside `s` are unrestricted. These two containment theorems
require neither continuity of group operations, compactness, separation nor
a finite index type. The factorization combines the existing unary theorem
with this finite-cylinder containment and continuous quotient descent.
See [the cylinder API](../GroupTheory/Topology/Algebra/OpenSubgroup/Pi.lean),
[the power factorization](../GroupTheory/Topology/Algebra/CompactGroup/PiDiscreteFactor.lean)
and [two-coordinate, infinite-index and empty-index clients](../GroupTheoryTest/Topology/Algebra/CompactGroup/PiDiscreteFactor.lean).

**Finite-coordinate homomorphism factorization.** For an arbitrary dependent
family of groups `G i` with topologies and a discrete group `H`, every
`f : (∀ i, G i) →ₜ* H` factors as a continuous group homomorphism through
quotients of finitely many coordinates by open normal subgroups.
`ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor` gives
`s : Finset I`, `N : ∀ i : s, OpenNormalSubgroup (G i)` and
`fbar : (∀ i : s, G i ⧸ (N i).toSubgroup) →ₜ* H`, with the bundled triangle
`fbar.comp (ContinuousMonoidHom.piQuotient s (fun i => (N i).toSubgroup)) = f`.
Each selected quotient and their product have their canonical discrete topology.
Neither continuity of the source operations nor compactness, separation,
commutativity or finiteness of the index or target is assumed. The selected
stage may be infinite, and the descended homomorphism need not be injective.
If all factors are compact,
`ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor_finite` makes
each selected quotient and their product finite. Compactness is needed only
for this refinement.

The canonical `ContinuousMonoidHom.piQuotient` projection needs normality,
not openness, of the selected subgroup family. Its application, kernel and
surjectivity lemmas describe its coordinates. Under the explicit quotient-map
hypothesis, `piQuotient_existsUnique_factor` gives unique continuous descent
into any monoid equipped with a topology exactly when the projection kernel
lies in the observer's kernel. See
[the homomorphism API](../GroupTheory/Topology/Algebra/Group/PiDiscreteFactor.lean)
and [essential coordinates, noninjective factors and nonfinite stages](../GroupTheoryTest/Topology/Algebra/Group/PiDiscreteFactor.lean).

**Locally compact identity components.** In a locally compact topological group,
the identity component is the intersection of **all** open subgroups, even
without a Hausdorff assumption; membership and point-separation lemmas make
this characterization usable. For a continuous open surjective group homomorphism
with locally compact source, the closure of its identity-component image is
the identity component of the target, without target separation or local
compactness assumptions. Openness and closure are essential; the printed
open-*normal* intersection is false in general. The image argument uses the
locally compact open-quotient theorem for totally disconnected groups, proved
by restricting to a compact open subgroup. See [the component theorems](../GroupTheory/Topology/ConnectedComponentOpenSubgroup.lean),
[their boundary clients](../GroupTheoryTest/Topology/ConnectedComponentOpenSubgroup.lean)
and [the open-quotient lemma](../GroupTheory/Topology/OpenQuotient.lean).

**Identity-component quotients.** For any topological group, the ordinary
quotient by Mathlib's `Subgroup.connectedComponentOfOne` is Hausdorff and totally
disconnected, without a separation or local-compactness hypothesis on the
original group. `QuotientGroup.connectedComponentQuotientMk` is the canonical
continuous projection. `QuotientGroup.connectedComponentQuotientLift` factors
continuous homomorphisms into totally disconnected groups, with application,
composition, uniqueness and hom-equivalence APIs. The target group's
operations need not be continuous. See
[the quotient API](../GroupTheory/Topology/ConnectedComponentQuotient.lean)
and [boundary examples](../GroupTheoryTest/Topology/ConnectedComponentQuotient.lean).

**Continuous compatible sections.** For any category `J`, functor
`F : J ⥤ MonCat`, and topologies on its monoid stages, the existing Mathlib
compatible-sections subtype has continuous coordinate projections
`MonCat.sectionsπContinuousMonoidHom F j`. For any monoid `H` with an arbitrary
topology, `MonCat.sectionsLift` constructs a continuous monoid homomorphism
from a family of continuous homomorphisms `H →ₜ* F.obj j` compatible with
**every** arrow.
`MonCat.sectionsLift_unique` and `MonCat.sectionsHomEquiv` give its uniqueness
and the equivalence with compatible families. `MonCat.sections_topology`
identifies the sections topology as the initial topology: the infimum of the
topologies induced by all coordinate projections.
`GrpCat.sectionsπContinuousMonoidHom` extends
Mathlib's algebraic projection for group-valued diagrams. No continuity of
multiplication on `H` or the stages, or of the transition maps, is assumed;
filteredness, inhabitance, compactness, separation and surjectivity are likewise
unnecessary. This is a continuous-*monoid*-homomorphism API, not a TopCat limit
or topological-group structure assertion. See [the definitions and theorems](../GroupTheory/Topology/Sections.lean)
and [boundary examples](../GroupTheoryTest/Topology/Sections.lean).

## Grothendieck extensions

**Additive and biadditive Grothendieck extensions.** For an additive commutative
monoid `A` and an additive commutative group `G`,
`Algebra.GrothendieckAddGroup.liftAddEquiv` packages Mathlib's universal-property
equivalence as `(A →+ G) ≃+ (Algebra.GrothendieckAddGroup A →+ G)`. Its
underlying equivalence is exactly Mathlib's `lift`, with inverse restriction
along the canonical map `of`. For another additive commutative monoid `B`,
`Algebra.GrothendieckAddGroup.lift₂` extends any curried biadditive map
`A →+ B →+ G` to both canonical completions, with generator formulas,
extensionality and uniqueness. The three universes are independent. No
cancellation or nontriviality hypothesis is required; the API reuses Mathlib's
completion and introduces no replacement carrier. See the
[Grothendieck lift API](../GroupTheory/MonoidLocalization/GrothendieckGroup.lean)
and its [integer-valued clients](../GroupTheoryTest/GrothendieckGroup.lean).

**Ring structures and multiplicative Grothendieck lifts.** For any semiring `A`,
`Algebra.GrothendieckAddGroup A` has a canonical `Ring` instance; for a
commutative semiring it has a canonical `CommRing` instance with the same
underlying ring. Both retain the existing additive group, including its
natural and integer scalar operations. The canonical `ofRingHom` retains the
entire additive generator `of`. The bundled multiplication `mulAddHom` already
exists for a non-unital, non-associative semiring, with generator computation,
extensionality and uniqueness; associativity, units and commutativity use the
corresponding source laws separately. For any ring `S`, `liftRingHom` extends
`A →+* S` to a ring homomorphism from the completion, with its entire underlying
additive homomorphism equal to the existing additive `lift`. Generator evaluation,
extensionality and uniqueness characterize the extension. The equivalence
`liftRingEquiv` has this canonical lift as its forward function and restriction
along `ofRingHom` as its inverse. The source and target universes are independent;
no commutativity of the target, cancellation or nontriviality is required. See the
[ring API](../GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean) and the
[signed-natural and one-element clients](../GroupTheoryTest/GrothendieckGroup.lean).

### Completion products and cofinal denominators

Completion commutes canonically with arbitrary dependent products of additive
commutative monoids, including infinite and empty index types. The equivalence
preserves all tuple units, has induced evaluations as its coordinates and is
natural in families of additive homomorphisms. The completed product map is
bijective exactly when every completed coordinate map is bijective; no cancellation
or nontriviality is assumed.

For a family `ι : I → B` in an additive commutative monoid with
`∀ b, ∃ i c, b + c = ι i`, every element of the completion is `of b - of (ι i)`.
If an additive subgroup contains all `of (ι i)`, the quotient has representatives
from `B`, without cancellation or injectivity assumptions. Applied to a cofinal
additive homomorphism, this gives monoid representatives modulo the group range
of the induced completion map.

**[Nilpotence reflection on additive units](../GroupTheory/MonoidLocalization/GrothendieckGroup/Nilpotent.lean).**
For any semiring `A` and `a : A` with `IsAddUnit a`, the image
`Algebra.GrothendieckAddGroup.ofRingHom A a` is nilpotent if and only if `a` is
nilpotent. If the image has vanishing `n`th power, then `a ^ (n + 1) = 0`,
including `n = 0`. The supporting
[absorption API](../GroupTheory/Algebra/IsAddUnit.lean) proves that an additive unit
annihilates any element `b` satisfying `b + c = c`; it already works in a
nonunital, nonassociative semiring. These results require neither additive
cancellation nor commutative multiplication.

For polynomial-unit arguments over a commutative semiring, this supplies the
scalar step from nilpotence of a coefficient's image in the completion to
nilpotence of the coefficient itself, once its additive invertibility is known.
The polynomial coefficient criterion and its converse are separate results, not
asserted by this scalar theorem.

## Abelian arithmetic

**Finite cyclic norm exactness.**
[`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range`](../GroupTheory/CyclicNorm.lean)
identifies `ker (∑ i ∈ Finset.range m, sigma ^ i)` with `range (1 - sigma)`
for an endomorphism `sigma` of any additive commutative group `A`. It requires
`m : ℕ` with `0 < m` and `sigma ^ m = 1` (not necessarily *exact* order `m`),
injectivity of multiplication by that **same** `m`, and an elementwise fixed
lift: if `sigma a - a ∈ m • A`, some `sigma`-fixed `z` satisfies
`a - z ∈ m • A`. This is useful when fixed classes modulo `m • A` have
fixed representatives even though multiplication by `m` is not surjective.
It does not assume divisibility or a global fixed-lift section, and does not
assert an unconditional Tate/cohomology theorem or source coverage. See the
[cyclic norm guide](../GroupTheory/CyclicNorm/README.md) and its
[client examples and counterexamples](../GroupTheoryTest/CyclicNorm.lean).

**Surjective natural scalars on FG abelian groups.** For `[AddCommGroup A]`,
`[AddGroup.FG A]` and `n : ℕ` with `2 ≤ n`, surjectivity of the
map `fun x : A => n • x` forces `Finite A` and
`Nat.Coprime n (Nat.card A)`. A *single* integer scalar is a two-sided
inverse for `n • ·` on every element; the finite-and-coprime condition
characterizes both surjectivity and bijectivity of that map. The four APIs in
[`GroupTheory.FGScalarSurjectivity`](../GroupTheory/FGScalarSurjectivity.lean) are
`AddCommGroup.exists_zsmul_inverse_of_nsmul_surjective`,
`AddCommGroup.finite_coprime_of_nsmul_surjective`,
`AddCommGroup.nsmul_surjective_iff_finite_coprime` and
`AddCommGroup.nsmul_bijective_iff_finite_coprime`. These statements do not
apply to arbitrary surjective endomorphisms and do not formalize K-theory.
See the [FG scalar guide](../GroupTheory/FGScalarSurjectivity/README.md) and its
[client examples](../GroupTheoryTest/FGScalarSurjectivity.lean).

**Kernels of induced quotient maps.** For normal subgroups `N ≤ G` and `M ≤ H`
and a group equivalence `f : G ≃* H` with `f(N) ≤ M`,
`QuotientGroup.kerMapEquivQuotientOfEquiv` identifies the kernel of the induced
`G / N → H / M` with `M / f(N)`, using the subgroup of `M` defined by the image.
The groups may be noncommutative and lie in independent universes; image normality
is derived from the ambient equivalence. A kernel class `[g]` maps to `[f g]`,
and the inverse sends `[m]` to `[f.symm m]`. The additive equivalence and both
representative formulas are generated in `QuotientAddGroup`.
For a second such quotient map, ambient homomorphisms `a : G →* G'` and
`b : H →* H'` preserving the respective normal subgroups and satisfying
`f' ∘ a = b ∘ f` induce a commuting square of these equivalences.
`QuotientGroup.kerMapEquivQuotientOfEquiv_naturality` states this compatibility;
its additive counterpart is generated in `QuotientAddGroup`. See the
[quotient-kernel API](../GroupTheory/QuotientGroup/Kernel.lean) and the
[independent rational-plane diagonal model](../GroupTheoryTest/QuotientKernel.lean).

**Torsion in additive quotients.** For any additive commutative group `V`,
additive subgroup `L` and `n : ℕ`, bijectivity of multiplication by `n` on `V`
gives `QuotientAddGroup.nsmulTorsionEquivQuotient : (V / L)[n] ≃+ L / nL`.
Here the domain is the multiplication kernel and `nL` is the multiplication range on `L`.
It uses the ordinary kernel and range-quotient carriers.
The forward and inverse representative simp lemmas describe `[x] ↦ [n • x]`,
for a class represented by `x` with `n • x ∈ L`, and unique ambient `n`-division.
The hypothesis is needed at this scalar only: there are no topology, lattice,
finite-generation, finite-rank or divisibility-at-other-scalars premises. At `n = 0`
it forces `V` to be trivial; at `n = 1` both sides are trivial.
This is the scalar specialization of the quotient-kernel comparison, with an
explicit equality identifying the two constructions after the canonical transports.
See
[the construction and its characteristic laws](../GroupTheory/QuotientTorsion.lean)
and [the rational half- and quarter-classes and unit-scalar examples](../GroupTheoryTest/QuotientTorsion.lean).

The scalar-transition statement
`QuotientAddGroup.nsmulTorsionEquivQuotient_naturality` says that, for `n = m * d`,
multiplication by `d` on quotient torsion corresponds to reduction `L / nL → L / mL`, as an equality
of additive homomorphisms built from the usual quotient and kernel-restriction
maps. Bijectivity at `n` implies the required bijectivity at `m`; there is no
positivity assumption. The quarter-to-half rational example computes the
nonzero classes and their equivalence values from representatives, then applies
this identity to their compatibility.
This is a specialization of the quotient-kernel naturality square.

**Scalar indices on FG abelian groups.**
The [scalar-index formula](../GroupTheory/IndexNSmul.lean) gives the all-natural-scalar
identity `index(n • A) = n ^ Module.finrank ℤ A * Nat.card (ker(n • ·))` under
`[AddCommGroup A] [AddGroup.FG A]`. In the module's notation this is
`(nsmulAddMonoidHom (α := A) n).range.index =
n ^ Module.finrank ℤ A * Nat.card ((nsmulAddMonoidHom (α := A) n).ker)`
for every `n : ℕ`. The injective specialization requires only
injectivity at the specified scalar, not freeness or a nonzero scalar. The free
comparison collapses the kernel-weighted expression to Mathlib's existing
`n ^ Module.finrank ℤ A` for `[Module.Free ℤ A] [Module.Finite ℤ A]`, also at zero.
Index and `Nat.card` are zero for infinite quotients and kernels;
no all-scalar finiteness conclusion is asserted.
Mathlib already supplies quotient finiteness at nonzero scalars.
The [mixed examples](../GroupTheoryTest/IndexNSmul.lean) distinguish integer module
finrank from minimum-generator rank and allow nonzero finite torsion.

**Finite torsion in additive quotients.** For `{V : Type u} [AddCommGroup V]`,
`L : AddSubgroup V` with `[AddGroup.FG L]`, and any `n : ℕ`, assume only
`Function.Bijective (nsmulAddMonoidHom (α := V) n)`. The
[cardinality extension](../GroupTheory/QuotientTorsion/Cardinality.lean) gives:

- `QuotientAddGroup.finite_ker_nsmul_quotient`:
  `Finite (nsmulAddMonoidHom (α := V ⧸ L) n).ker`.
- `QuotientAddGroup.natCard_ker_nsmul_quotient`:
  `Nat.card (nsmulAddMonoidHom (α := V ⧸ L) n).ker = n ^ Module.finrank ℤ L`.

The finite-kernel conclusion is separate because natural cardinality alone does
not assert finiteness. Integer module finrank measures torsion-free rank, so
finite torsion in `L` is allowed. No freeness, ambient or quotient finite
generation, global torsion-freeness, bijectivity at other scalars, or positivity
premise is required. At zero the premise forces the ambient group trivial,
and the equation is `1 = 0 ^ 0`.

The [private models](../GroupTheoryTest/QuotientTorsion.lean) reuse the nonzero
rational half-class to obtain a rank-one finitely generated subgroup,
ambient doubling bijectivity, and a finite kernel of cardinality two. The direct
count uses the original equivalence and Mathlib's free-index theorem; both general
theorems are also instantiated on the same group. The zero-scalar trivial group and
doubling on `ZMod 3` check the degenerate and nonzero finite-torsion cases independently.
For a complex full lattice, separately supplying integer rank `2 * g` gives
the finite-level count `n ^ (2 * g)`; the free case already admits the stock
free-index route. No uniformization, lattice-rank calculation, tensor comparison,
inverse limit, Tate-module theorem or scheme-point correspondence follows here.

## Closed Noetherian subsemigroups

Import `GroupTheory.Topology.Algebra.Group.Subsemigroup` for inverse closure of a
closed subsemigroup whose induced topology is Noetherian. Only continuity of
fixed left translations in the ambient group is required; the ambient space need
not be Noetherian, and the subsemigroup may be empty. The additive counterpart
gives closure under negation. For a submonoid, every element is a unit in the
original submonoid.

## Archimedean multiplicative boundedness

Import `GroupTheory.Algebra.Order.Subsemigroup`.

The target is a commutative monoid `Γ` equipped with a linear order and a chosen `0`.
The instances are `CommMonoid Γ`, `Zero Γ`, `LinearOrder Γ`, `ZeroLEOneClass Γ`,
`PosMulStrictMono Γ` and `MulArchimedean Γ`: in particular, `0 ≤ 1`, multiplication
by positive elements is strictly monotone, and the target is multiplicatively Archimedean.

For a selected carrier `s : S` with `SetLike S Γ` and `MulMemClass S Γ`,
[`MulMemClass.bddAbove_iff_le_one_of_mulArchimedean`](../GroupTheory/Algebra/Order/Subsemigroup.lean)
says that `s` is bounded above exactly when every member is at most `1`.
Multiplication closure suffices: no membership of `1` or nonemptiness is required.
For the empty set, the memberwise condition is vacuous and `1` is an upper bound,
not an asserted member or maximum. The carrier type `S` and target `Γ` may occupy
independent universes.

For a multiplicative map `f : F`,
[`MulHomClass.bddAbove_range_iff_le_one_of_mulArchimedean`](../GroupTheory/Algebra/Order/Subsemigroup.lean)
says that its raw function range is bounded above exactly when `f x ≤ 1` for every `x`.
The source `M` needs only `Mul M`; the map interface is `FunLike F M Γ` and
`MulHomClass F M Γ`. The source, target and map type may occupy independent universes.
No identity, associativity or power operation on the source is assumed.

These statements concern order boundedness of the selected set or raw function range,
not a generated submonoid, subgroup, topological closure or topological total boundedness.
They use the declared commutative target interface, not a weakening of the different
hypotheses in the module's inverse-target criteria.
