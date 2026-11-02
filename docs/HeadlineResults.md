# Headline results

[Back to the library overview](../README.md#headline-results) ·
[Detailed result guide](Results.md) · [Usage guide](Usage.md)

This is the complete headline catalogue accompanying the
[family overview](../README.md#headline-results). Each entry links to its modules
or detailed statements. The [result guide](Results.md) develops the APIs,
examples and further results; [References and credits](../CREDITS.md) records
mathematical sources and prior formalizations.

## Catalogue navigation

- [Pointwise products and scalar actions](#pointwise-products-and-scalar-actions)
- [Zero-sum pairs and multiplicative images](#zero-sum-pairs-and-multiplicative-images)
- [Power restrictions and order](#power-restrictions-and-order)
- [Group actions and presentations](#group-actions-and-presentations)
- [Fixed vectors and averaging](#fixed-vectors-and-averaging)
- [Free groups, arithmetic and Grothendieck completions](#free-groups-arithmetic-and-grothendieck-completions)
- [Topology and abstract homomorphisms](#topology-and-abstract-homomorphisms)
- [Further algebraic and character results](#further-algebraic-and-character-results)


## Pointwise products and scalar actions

For arbitrary `ι : Type u` and `β : ι → Type v`, with independent universes and
`[∀ i, MulZeroClass (β i)]`, `DFinsupp.pointwiseMul` selects coefficientwise
multiplication on the existing dependent finitely supported functions. It is not
registered as an instance. Its application formula, singleton products and support
inclusions are in [`DFinsupp.Pointwise`](../GroupTheory/DFinsupp/Pointwise.lean).
The computable support statements use decidable equality of indices and decisions
for nonzero coefficients; the multiplication itself needs neither.

For constant fibres, `Finsupp.toDFinsupp_mul` preserves the original pointwise
product at `MulZeroClass` alone. The inverse comparison uses exactly the decision
arguments of `DFinsupp.toFinsupp`; the plain equivalence has the same forward map
as `Finsupp.toDFinsupp`. Existing arithmetic and additive/linear conversion APIs
remain unchanged; see [`Finsupp.Pointwise`](../GroupTheory/Finsupp/Pointwise.lean).
For independent coefficient and scalar types `C` and `B`, the scalar comparison
`Finsupp.toDFinsupp_pointwise_smul` requires only `Zero C` and
`SMulZeroClass B C`. Scalars are full functions `ι → B`, acting through evaluation
at each index and the existing `DFinsupp` scalar action. The semiring/module
specialization uses the additive conversion equivalence with this action, not a
uniform action of the function semiring on every fibre; see
[`Finsupp.PointwiseScalar`](../GroupTheory/Finsupp/PointwiseScalar.lean).

## Zero-sum pairs and multiplicative images

- **Zero-sum pairs and unit images.** In a nonunital, nonassociative semiring,
  `a + b = 0` implies `a * a = b * b`. A function-like multiplication-preserving
  map to a monoid sends such a pair to values that are units simultaneously;
  preservation of addition, zero or one and target commutativity are not required
  (`mul_self_eq_mul_self_of_add_eq_zero`,
  `MulHomClass.isUnit_apply_iff_of_add_eq_zero`;
  [`GroupTheory.Algebra.IsAddUnit`](../GroupTheory/Algebra/IsAddUnit.lean)).
  The source, target and function-family universes are independent; see the
  [usage guide](Usage.md#zero-sum-pairs-and-multiplicative-images).

## Power restrictions and order

- **Subgroup membership through finite powers.** In any group, a power at the gcd of a
  finite family of natural exponents belongs to a subgroup-like object if and only if
  every selected power does. A family with gcd one detects membership of the element.
  For `s : Finset ι` and `e : ι → ℕ`, the exact generated-subgroup formula is
  `Subgroup.closure ((fun i => a ^ (e i)) '' (s : Set ι)) =
  Subgroup.zpowers (a ^ (s.gcd e))`. In an additive group the formula is
  `AddSubgroup.closure ((fun i => (e i) • a) '' (s : Set ι)) =
  AddSubgroup.zmultiples ((s.gcd e) • a)`.
  Only `Group` or `AddGroup` is required, respectively; the carrier, subgroup-like
  object type and index universes are independent. No commutativity, normality,
  finite or nonempty index type, or positivity assumption is needed. Empty families
  and zero exponents are included; empty or all-zero families generate the bottom
  subgroup. See the [subgroup-power API](../GroupTheory/Algebra/Group/Subgroup/Power.lean)
  and [usage guide](Usage.md#subgroup-membership-through-finite-powers).

- **Intersections of cyclic power subgroups.** For any group, element `a` and natural
  exponents `m n`, `Subgroup.zpowers_pow_inf a m n` gives
  `Subgroup.zpowers (a ^ m) ⊓ Subgroup.zpowers (a ^ n) =
  Subgroup.zpowers (a ^ (Nat.lcm m n))`.
  In an additive group, `AddSubgroup.zmultiples_nsmul_inf` gives the corresponding
  intersection of the integer-multiple subgroups of `m • a` and `n • a`.
  Zero exponents are included; no commutativity or order assumption is needed.
  See the [subgroup-power API](../GroupTheory/Algebra/Group/Subgroup/Power.lean)
  and [usage guide](Usage.md#subgroup-membership-through-finite-powers).

  For `s : Finset ι` and `e : ι → ℕ`, `Subgroup.zpowers_inf_finsetInf_pow` identifies
  the intersection of `Subgroup.zpowers a` with
  `s.inf (fun i => Subgroup.zpowers (a ^ (e i)))` as
  `Subgroup.zpowers (a ^ (s.lcm e))`. If `s.Nonempty`,
  `Subgroup.finsetInf_zpowers_pow` removes the initial `Subgroup.zpowers a` factor.
  For an empty family the finite infimum is top, so this initial cyclic subgroup is
  essential. The additive companions are `AddSubgroup.zmultiples_inf_finsetInf_nsmul`
  and `AddSubgroup.finsetInf_zmultiples_nsmul`, using natural multiples in an additive
  group. These finite-family formulas require only `Group` or `AddGroup`, with independent
  carrier and index universes, and allow zero and repeated coefficients.

- **Finite power kernels.** In any monoid, let `a` be left-regular: left multiplication
  by `a` is injective. For arbitrary `b`, equality of their powers at the gcd of a finite
  family of natural exponents is equivalent to equality at every selected exponent.
  A family with gcd one gives `a = b`. The additive statements require only an additive
  monoid and injective left addition by `a`. No regularity of `b`, global cancellation,
  commutativity or group assumption is needed. Empty families and zero exponents are
  included; see [`GroupTheory/MonoidHom/PositivePower.lean`](../GroupTheory/MonoidHom/PositivePower.lean).
- **Right-regular power kernels.** In any monoid, if right multiplication by `a` is
  injective, equality of powers of `a` and arbitrary `b` at every exponent in a finite
  family is equivalent to equality at their gcd. A family with gcd one gives `a = b`;
  in particular, two coprime exponents suffice. Empty families and zero exponents are
  included. Additive versions require only an additive monoid and injective right
  addition by `a`.

  For both the left- and right-regular routes, the finite-family criterion is
  `s.gcd e = 1` for `s : Finset ι` and `e : ι → ℕ`, in independent index and carrier universes;
  it does not require a coprime pair among the selected exponents. For the empty family
  the gcd is zero, so the equivalence is vacuous and does not determine `a = b`.
  The binary equivalences include `(m, n) = (0, 0)`.
  The [usage guide](Usage.md#power-kernels-and-restriction) gives the theorem names
  and distinguishes these monoid statements from homomorphism restriction below.

- **Restriction through powers.** Let `f : M →* N`, where `M` has the stock `MulOne`
  structure and `N` is a monoid. If every `x : N` has some positive power in `Set.range f`,
  precomposition by `f` is injective on homomorphisms into any monoid with unique positive
  roots (`IsMulTorsionFree`); equality can therefore be checked after restriction. The
  additive statements use positive multiples and torsion-free additive targets.
  Their source needs only `AddZero`, with a distinguished zero but no associativity
  or identity laws, just as `MulOne` supplies no such laws on the multiplicative source.

- **Left-regular equality detection through finite power images.** Let `f : A →* M`,
  with only `MulOne A`, and let `M` and `N` be monoids. For every `x : M`, suppose
  there are `s : Finset ι` and `e : ι → ℕ` with `s.gcd e = 1` and
  `x ^ (e i) ∈ Set.range f` for every `i ∈ s`. For fixed `g h : M →* N`, if every
  `g x` is left-regular, then `g.comp f = h.comp f ↔ g = h`. The four carrier and
  index universes are independent; both `s` and `e` may depend on `x`. No regularity
  of `h`, global target cancellation, commutativity, group, surjectivity, finite or
  nonempty index type, decidable equality or positivity assumption is needed.
  The additive form uses `AddZero A`, additive monoids and natural multiples with
  gcd one. Zero and repeated exponents and coefficients are allowed; singleton
  exponent one is valid, while empty or all-zero families cannot have gcd one.
  The finite-natural-set interface remains the `ι = ℕ`, `e = id` specialization:
  `s : Finset ℕ`, `s.gcd id = 1` and `x ^ n ∈ Set.range f` for every `n ∈ s`.
  Coprime pairs and consecutive-power images specialize it; for left-cancellative
  targets the latter make precomposition injective.

- **Right-regular equality detection through finite power images.** Let `f : A →* M`,
  with only `MulOne A`, and let `M` and `N` be monoids. For each `x : M`, suppose
  there are `s : Finset ι` and `e : ι → ℕ` with `s.gcd e = 1` and
  `x ^ (e i) ∈ Set.range f` for every `i ∈ s`. For fixed `g h : M →* N`,
  right-regularity of every `g x` gives `g.comp f = h.comp f ↔ g = h`, with no
  regularity assumption on `h`. All four carrier and index universes are independent;
  both `s` and `e` may depend on `x`. No global cancellation, commutativity, group,
  surjectivity, finite or nonempty index type, decidable equality or positivity is needed.
  The additive peer uses `AddZero A`, additive monoids and natural multiples.
  Zero and repeated exponents and singleton exponent one are valid; empty or all-zero
  families cannot have gcd one. The two regularity orientations have the same indexed
  image input shape; neither is a power-equality kernel for two elements or global
  precomposition injectivity into an arbitrary monoid.
  See the [image-detection API](../GroupTheory/MonoidHom/PositivePower.lean)
  and [input shapes](Usage.md#power-kernels-and-restriction).

- **Restriction through consecutive powers.** If for every `x : N` both `x ^ n` and
  `x ^ (n + 1)` lie in `Set.range f` for some natural `n`, precomposition is injective on
  homomorphisms into any left-cancellative monoid. The exponent may be zero; no unique-root,
  commutativity, order or group hypothesis on the target is needed.

- **Pointwise comparison from positive powers.** Under the positive-power range condition,
  homomorphisms `g h : N →* Γ` to a linearly ordered commutative monoid with zero satisfy
  `g (f a) ≤ h (f a)` for all `a : M` if and only if `g x ≤ h x` for all `x : N`.
  Neither associativity nor identity laws on `M` are used, and `N` need not be commutative
  or ordered. The positive exponent need not be uniform. These restriction results are in
  [`GroupTheory/MonoidHom/PositivePower.lean`](../GroupTheory/MonoidHom/PositivePower.lean).

- **Archimedean multiplicative boundedness** ([module](../GroupTheory/Algebra/Order/Subsemigroup.lean);
  [statements and API](Results.md#archimedean-multiplicative-boundedness)).
  For a commutative monoid equipped with a linear order and a chosen `0` with `0 ≤ 1`,
  assume multiplicative Archimedeanness and strictly monotone multiplication by positive
  elements. A multiplication-closed selected set is bounded above iff every member is
  at most `1`; the same criterion holds for the raw range of a multiplicative map from
  a type with only multiplication. Selected sets may be empty and need not contain `1`.

## Group actions and presentations

- **[Coset actions and conjugacy](../GroupTheory/GroupAction/Quotient.lean).**
  For arbitrary subgroups `H, K` of a group `G`, equivariant maps `G/H → G/K`
  exist exactly when `H ≤ gKg⁻¹` for some `g`; the coset actions are isomorphic
  exactly when `H, K` are conjugate. Maps both ways alone do not suffice.

- **[Coefficient-sum relations](../GroupTheory/Finsupp/CoefficientSum.lean).**
  Over a semiring `R`, for an additive commutative group `M` with an `R`-module
  structure and a chosen `i₀ : ι`, the coefficient-sum kernel on `ι →₀ M` is
  the `R`-span of `single i m - single i₀ m`. Linear maps into additive
  commutative monoid modules factor uniquely through the sum exactly when their
  singleton components agree; neither finite indices nor cancellative targets
  are required.

- **[Group diagrams by arrow relations](../GroupTheory/Category/Grp/Colimits.lean).**
  For any group-valued diagram, the free product of its object groups modulo the
  normal closure of all arrow-identification relators has the diagram's universal
  property into every monoid in an independent universe. No smallness, finiteness
  or commutativity is assumed. Its generator maps satisfy every arrow, generate
  the quotient, and determine every outgoing homomorphism. Explicitly lifting
  each object to the carrier universe `max u v` gives a colimit cocone and the
  leg-preserving comparison with any other colimit in that universe; this does not
  assert that universe lift preserves arbitrary large group colimits. A
  [nonabelian example](../GroupTheoryTest/Category/Grp/Colimits.lean) combines an
  identity arrow with an isolated component and detects noncommuting generators.

- **[Compatible maps of group diagrams](../GroupTheory/Category/Grp/ColimitMap.lean).**
  For two diagrams over the same arbitrary indexing category, a family of group
  homomorphisms commuting with every diagram arrow induces a homomorphism between
  their canonical colimits. Source and target object groups may have independent
  universes. Restrictions to the object groups characterize the induced map, and
  the construction respects identity families and composition. If every component
  homomorphism is surjective, the induced map is surjective and its kernel is the
  normal closure of the images of all component kernels under the original source
  generator maps, by
  [`map_surjective` and `ker_map`](../GroupTheory/Category/Grp/ColimitMapKernel.lean).
  No nonemptiness, connectedness, filteredness or finiteness of the indexing
  category is required; the empty diagram is included.

- **[Pushouts over a trivial group](../GroupTheory/Category/Grp/Pushout.lean).**
  For a group homomorphism `f : A →* B` and a trivial group `T`, the pushout is
  `B / normalClosure (range f)`. In every such group pushout the `B`-leg is
  surjective with exactly that kernel, without injectivity or commutativity
  assumptions. The guide distinguishes the unbundled and `GrpCat` universes.

## Fixed vectors and averaging

- **[Fixed vectors over semirings](../GroupTheory/RepresentationInvariants.lean).**
  For monoid representations on additive commutative monoid modules over a
  semiring, intertwiners `f, g` with injective `f` and `Function.Exact f g` give
  exactness on fixed submodules, not arbitrary surjectivity. Fixed submodules also commute with
  [arbitrary products](../GroupTheory/RepresentationPi.lean), including empty ones,
  and [algebraic direct sums](../GroupTheory/RepresentationDirectSum.lean).

- **[Noetherian monoid cohomology](../GroupTheory/Cohomology/Noetherian.lean).**
  Let `R` be any ring, `G` any monoid and `A : Rep R G` a linear representation,
  with independent ring, monoid and coefficient universes. The
  [inhomogeneous complex](../GroupTheory/Cohomology/Basic.lean)
  `Rep.inhomogeneousCochains A` has degree `n` term `(Fin n → G) → A`, with
  pointwise module structure and alternating differential using `A.ρ`.
  Its cohomology is `Rep.cohomology A n`. The canonical `R`-linear equivalence
  `Rep.cohomologyZeroEquiv A` identifies degree zero with `A.ρ.fixedSubmodule`
  in the original coefficient module. Under only `IsNoetherian R A`,
  `Rep.isNoetherian_cohomology_zero` makes degree zero Noetherian for arbitrary `G`.
  If also `Finite G`, `Rep.isNoetherian_cohomology` makes every natural degree
  Noetherian: cochains are finite products of `A`, cycles embed in cochains,
  and cohomology is a quotient of cycles. Neither commutativity nor Noetherianity
  of `R`, finiteness of the underlying `A`, nor a trivial action is required;
  no separate finite-generation hypothesis is imposed.
  The Mathlib comparison requires a commutative ring and a group, with `R`, `G`
  and the coefficient carrier all in one universe. It identifies the complexes
  and cohomology; in degree zero it agrees, after that transport, with
  `groupCohomology.H0Iso` on values in `A`. The invariant-submodule equivalence
  alone allows independent universes. See the
  [construction and comparison laws](Results.md#monoid-cochains-and-noetherian-cohomology)
  and [usage](Usage.md#monoid-cochains-and-noetherian-cohomology).

- **[Finite-group intertwining lifts](../GroupTheory/RepresentationLifting.lean).** If the
  order of a finite group is a unit in a possibly noncommutative semiring, any ordinary
  linear lift of one intertwining map through another intertwining map can be replaced
  by an intertwining lift. The modules need only be additive commutative monoids; the map
  being lifted through need not be surjective, and the given linear lift need not
  intertwine. Averaging uses the
  [additive conjugation representation](../GroupTheory/RepresentationLinHomAdd.lean).

- **[Finite-group crossed-map averaging](../GroupTheory/CocycleAveraging.lean).**
  For a finite group `G` acting by additive automorphisms on an additive commutative
  group `A`, bijective multiplication by `Nat.card G` makes every crossed map
  principal: `z g = g • v - v`. The explicit witness is the negative inverse-order
  multiple of its sum. Its formula commutes with additive maps between groups with
  bijective multiplication by the same order; transporting cocycles additionally
  needs equivariance. See the [averaging API](../GroupTheory/CocycleAveraging/README.md).
  For a module over any semiring, a unit-valued order suffices, with the
  negative inverse-unit scalar sum as witness. The additive group action need
  not be scalar-linear, and the scalar-form vector formula remains natural
  under arbitrary additive maps.

## Free groups, arithmetic and Grothendieck completions

- **[Kernels of free-group relabelings](../GroupTheory/FreeGroup/Map.lean).**
  For any function `σ : I → J`, `FreeGroup.ker_map` identifies the kernel of
  `FreeGroup.map σ` with the normal closure of all `of i * (of k)⁻¹` for which
  `σ i = σ k`. The label types lie in independent universes and may be empty;
  no injectivity, surjectivity or finiteness is assumed. The same module gives
  injectivity and surjectivity criteria for the induced homomorphism.

- **[Finite-index free-group ranks](../GroupTheory/FreeGroup/Rank.lean).**
  For finite-index `H` in a finitely generated free group,
  `rank H + [G:H] = rank G * [G:H] + 1`, including ambient rank zero.
  Mathlib supplies subgroup freeness and finite generation. The
  [index-two guide](Results.md#index-two-subgroups-and-explicit-generators)
  gives all three explicit generating triples in rank two, not triple freeness.

- **[Grothendieck extensions](../GroupTheory/MonoidLocalization/GrothendieckGroup.lean).**
  Biadditive maps from two additive commutative monoids into an additive
  commutative group extend uniquely to both completions. A semiring's additive
  completion has a [canonical ring structure](../GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean)
  and universal ring lifts, without cancellation. For an additive unit in any
  semiring, [nilpotence is reflected](../GroupTheory/MonoidLocalization/GrothendieckGroup/Nilpotent.lean)
  by the canonical map to that ring; the scalar step is not a polynomial criterion.

- **[Torsion in additive quotients](../GroupTheory/QuotientTorsion.lean).**
  For an additive commutative group `V`, any additive subgroup `L`, and any
  natural `n` whose multiplication map is bijective on `V`, `(V/L)[n] ≃+ L/nL`
  by `[x] ↦ [n • x]`. If `L` is finitely generated, the kernel is
  [finite of cardinality](../GroupTheory/QuotientTorsion/Cardinality.lean)
  `n ^ Module.finrank ℤ L`; freeness and ambient finite generation are not needed.

## Topology and abstract homomorphisms

- **[Closed self-embeddings and irreducible components](../GroupTheory/Topology/ClosedEmbedding.lean).**
  For any topological space `X`, a closed self-embedding `f : X → X` is surjective
  if `X` has finitely many irreducible components and strict inclusion of nonempty
  irreducible closed subsets is well-founded:
  `[WellFoundedLT (TopologicalSpace.IrreducibleCloseds X)]`.
  The theorem is `Topology.IsClosedEmbedding.surjective_of_finite_irreducibleComponents`.
  No Noetherianity, separation or group structure is assumed, and the empty space is
  included. These are irreducible components, not connected or path components;
  see the [argument and exact interface](Results.md#closed-self-embeddings-and-irreducible-components).

- **[Inverses in preirreducible subsemigroup closures](../GroupTheory/Topology/Algebra/Group/Subsemigroup/Closure.lean).**
  Let `S` be a subsemigroup of a group with a given topology and continuous fixed
  left translations (`ContinuousConstSMul G G` for the canonical regular left action).
  Suppose `S` is preirreducible, right multiplication by each actual `s ∈ S` is
  continuous on `closure (S : Set G)`, and
  `[WellFoundedLT (TopologicalSpace.IrreducibleCloseds G)]` holds for the ambient group
  in its original topology. Then `Subsemigroup.inv_mem_closure_of_isPreirreducible`
  sends membership of **any** `x` in the closure to membership of `x⁻¹` there.
  This descending chain condition uses strict inclusion (`LT`, not `GT`).
  No ambient Noetherianity, global right continuity, joint multiplication,
  continuous inversion, T1, compactness or commutativity is required. Empty `S` is
  allowed (then no `x` satisfies the membership premise). See the
  [closure argument](Results.md#closed-noetherian-subsemigroups) and
  [input shapes](Usage.md#inverses-in-a-subsemigroups-closure).

- **[Inverses in a Noetherian subsemigroup closure](../GroupTheory/Topology/Algebra/Group/Subsemigroup/Closure.lean).**
  Let `S` be a subsemigroup of a group with a given topology and continuous fixed
  left translations (`ContinuousConstSMul G G` for the canonical regular left action).
  If right multiplication by each `s ∈ S` is continuous on `closure (S : Set G)`
  and the actual closure subtype has Noetherian induced topology, then
  `Subsemigroup.inv_mem_closure_of_noetherianSpace` sends membership of `x` in that
  closure to membership of `x⁻¹`. Neither ambient Noetherianity, global right-translation
  continuity, joint multiplication, continuous inversion, separation, compactness nor
  commutativity is assumed. This is a membership theorem on the original closure,
  not a bundled subgroup construction. See the
  [exact input shapes](Usage.md#inverses-in-a-subsemigroups-closure) and
  [closure argument](Results.md#closed-noetherian-subsemigroups).

- **Locally constructible subgroups.** A locally constructible subgroup is closed under separately continuous
  multiplication and continuous inversion, without separation or ambient
  Noetherian hypotheses; the additive analogue holds as well. See
  [`GroupTheory.Topology.Algebra.Group.LocallyClosed`](../GroupTheory/Topology/Algebra/Group/LocallyClosed.lean).

- **[Cofinite groups and actions](../GroupTheory/Topology/Algebra/Group/Cofinite.lean).**
  Inversion and fixed translations are continuous on every cofinite group;
  joint multiplication is continuous exactly when the group is finite. An action
  of a cofinite group on any cofinite space is jointly continuous exactly when
  the actor is finite or the action is pointwise trivial. These use the ordinary
  product topology, not the cofinite topology on the whole set of pairs.

- **[Ultrafilter-limit homomorphisms](../GroupTheory/Topology/Ultrafilter.lean).**
  For a compact Hausdorff monoid with continuous multiplication, limits along
  any fixed ultrafilter give a surjective abstract homomorphism from its power.
  If the ultrafilter contains all cofinite sets, all fibers are dense; for a
  nontrivial target it is not continuous at the constant identity family.
  The guide includes finite-group targets and the original `ℕ → ZMod 3` example.

- **[Finite-index openness and automatic continuity](../GroupTheory/Topology/AutomaticContinuity.lean).**
  Every abstract finite-index subgroup of a compact Hausdorff commutative
  topological group with a dense algebraically finitely generated subgroup is
  open. Every abstract homomorphism from such a source into a compact
  nonarchimedean group is continuous; the target need not be Hausdorff or
  commutative, and the image may be infinite. This does not assert local constancy.

- **[Finite-coordinate homomorphism factorization](../GroupTheory/Topology/Algebra/Group/PiDiscreteFactor.lean).**
  A continuous homomorphism from any dependent product of groups with given
  topologies into a discrete group factors continuously through quotients of
  finitely many coordinates by open normal subgroups. No continuity of source
  operations is required. The selected stage is finite if all factors are compact,
  but need not be finite otherwise.

- **[Finite-index identity components](../GroupTheory/Topology/Algebra/Group/Subgroup.lean).**
  For a group with a topology and continuous fixed left translations, the identity
  component is an open subgroup of finite index when there are finitely many
  connected components. No local connectedness, separation, continuous inversion
  or normality assumption is needed. The additive version applies to the zero
  component.

- **[Compact open subgroups](../GroupTheory/Topology/CompactOpenSubgroup.lean) and
  [identity-component quotients](../GroupTheory/Topology/ConnectedComponentQuotient.lean).**
  Every locally compact totally disconnected topological group has a compact
  open subgroup basis, without a separate Hausdorff premise. Every topological
  group's ordinary quotient by its identity component is Hausdorff and totally
  disconnected, without separation or local compactness of the original group.

- **[Finite T0 pretransitive action spaces are discrete](Results.md#finite-t0-pretransitive-action-spaces).**
  If a group `G` acts pretransitively on a finite T0 topological space `X`,
  and `x ↦ g • x` is continuous for every fixed `g`, the given topology on
  `X` is discrete. No topology or finiteness of `G`, or nonemptiness of `X`,
  is required. See
  [`MulAction.discreteTopology_of_finite_of_isPretransitive`](../GroupTheory/Topology/GroupAction/Orbit.lean).

- **Finite-neighborhood joint continuity.** For `f : S × X → Y` between
  topological spaces, fix `(s, x)` and a finite neighborhood `V` of `x`.
  If `t ↦ f (t, y)` is continuous at `s` for every `y ∈ V` and
  `y ↦ f (s, y)` is continuous at `x`, then `f` is continuous at `(s, x)`.
  With all rows and columns continuous, finite neighborhoods at every point of
  `X` give global continuity; this includes finite `X` with its given topology.
  The scalar-operation corollaries require continuous fixed-scalar maps and
  continuous orbit maps, not action laws. See
  [the criteria and hypotheses](Results.md#topological-refinements) and
  [the continuity API](../GroupTheory/Topology/SeparateContinuity.lean).

The guide also covers [finite-index descent and property transport](Results.md#finite-index-openness-and-automatic-continuity),
[circle characters and other topology results](Results.md#topological-refinements),
[conditional cyclic norms and scalar indices](Results.md#abelian-arithmetic),
and the material hypotheses, formulas and examples behind these headlines.

## Further algebraic and character results

- **Orthogonal sums and finite-product homomorphisms.**
  [`Ring.Hom.FiniteSum`](../GroupTheory/Ring/Hom/FiniteSum.lean) supplies
  `NonUnitalRingHom.sum s f h` for a finite support `s`: the source and target
  are nonunital nonassociative semirings, and distinct component images must
  annihilate one another in both orders. Its additive map and application are
  the stock finite additive sum; empty and singleton supports have the expected
  zero and component formulas. No finite index type is required.

  For `[Fintype ι]`, `[∀ i, NonAssocSemiring (R i)]`, `[Semiring S]` and
  nonunital maps `φ : ∀ i, R i →ₙ+* S`, `Pi.liftRingHom φ horth hone` is a
  unit-preserving homomorphism `(∀ i, R i) →+* S` when
  `horth : ∀ i j, i ≠ j → φ i 1 * φ j 1 = 0` and `hone : ∑ i, φ i 1 = 1`.
  Source associativity is not required; target associativity is. Index, fibre
  and target universes are independent. The factory has no external
  `DecidableEq`, nonempty-index, nontriviality, commutativity or global-centrality
  premise. For an empty index, cover-one forces `0 = 1` in the target.
  `liftRingHom_apply` evaluates the lift as `∑ i, φ i (x i)`.
  With `[DecidableEq ι]`, `liftRingHom_single`, `liftRingHom_unique` and
  `liftRingHom_eq_iff` express extension along `Pi.single` and determination by
  those coordinate restrictions. They do not assert injectivity of the lift
  or a coordinate-recovery criterion. The construction reuses Mathlib's finite
  additive sums and Hom/Pi interfaces; its module records the upstream credits.

- **Contravariant transport of the whole compact-open dual.** For monoids `A`,
  `B` equipped with topologies, `PontryaginDual.mapEquiv` sends `e : A ≃ₜ* B`
  to `PontryaginDual B ≃ₜ* PontryaginDual A` by precomposition. Its inverse is
  precomposition with `e.symm`; identity and composition laws retain this reversed
  direction. No locally compact pair, Hausdorff or continuous-operation premise
  is required. The carrier is the original whole continuous-character space,
  not a replacement by abstract characters. See
  [`PontryaginDual`](../GroupTheory/Topology/PontryaginDual.lean).

- **Injectivity for discrete abelian groups.** For `[CommGroup G]` with a
  topology and `[DiscreteTopology G]`,
  `PontryaginDual.eval_injective_of_discrete G` proves injectivity of the
  original canonical continuous evaluation into the compact-open bidual.
  There is no finiteness, finite-generation, countability or nontriviality
  premise. The proof uses Mathlib's character-module separation and this
  library's rational-circle embedding `AddCircle.rationalToCircle`;
  discreteness makes the detecting character continuous. This is an
  injectivity theorem, not surjectivity, a topological embedding, or full
  Pontryagin reflexivity. Import
  [`PontryaginDual.Discrete`](../GroupTheory/Topology/PontryaginDual/Discrete.lean)
  explicitly.

- **Real characters and canonical biduality.** Every continuous circle-valued
  character of the additive real line has a unique period-one Fourier frequency.
  `PontryaginDual.realEquiv` identifies the original real topology with the
  compact-open topology on the entire real character space. The forward map of
  `PontryaginDual.realEvalEquiv` is canonical bidual evaluation, not a separately
  chosen algebraic identification. See
  [`PontryaginDual.Real`](../GroupTheory/Topology/PontryaginDual/Real.lean).

- **Canonical Pontryagin bidual evaluation.** For a monoid `A` equipped with a
  topology and `[LocallyCompactPair A Circle]`, `PontryaginDual.eval A` is the
  continuous homomorphism `a ↦ (χ ↦ χ a)` into the existing compact-open bidual.
  It is natural under arbitrary continuous monoid homomorphisms. If the dual
  also forms a locally compact pair with `Circle`, evaluation on the dual is
  a section of the dual of evaluation. No group, commutativity, continuity of
  the monoid operations or Hausdorff hypothesis on `A` is required. These
  general monoid results alone do not assert injectivity, surjectivity or full Pontryagin reflexivity
  of the original evaluation. See
  [`GroupTheory.Topology.PontryaginDual`](../GroupTheory/Topology/PontryaginDual.lean).

- **Equality of powers in reduced rings.** In any reduced ring, two elements whose
  powers agree at two coprime natural exponents are equal. More generally,
  `x ^ Nat.gcd m n = y ^ Nat.gcd m n` if and only if both `x ^ m = y ^ m` and
  `x ^ n = y ^ n`. These criteria require neither commutativity nor regularity,
  and include zero exponents and the zero ring. Use
  `IsReduced.eq_of_pow_eq_pow_of_coprime` and `IsReduced.pow_gcd_eq_pow_gcd_iff`
  from [`GroupTheory.Ring.Power`](../GroupTheory/Ring/Power.lean).

- **Positive-power annihilators.** In any reduced monoid with zero, for every
  nonzero natural exponent `m`, `a ^ m * b = 0 ↔ a * b = 0` and
  `a * b ^ m = 0 ↔ a * b = 0`. No commutativity, cancellation, absence of zero
  divisors or nontriviality is assumed. The exponent condition is essential:
  a zeroth power is one. Use `pow_mul_eq_zero_iff` and `mul_pow_eq_zero_iff` from
  [`GroupTheory.Algebra.GroupWithZero.Reduced`](../GroupTheory/Algebra/GroupWithZero/Reduced.lean).
  The annihilator API reuses Mathlib's
  square-zero criterion, upward power propagation and opposite-monoid transport;
  a factor equal to one recovers the existing `pow_eq_zero_iff`.
  For two lists aligned so that each entry of one is a positive power of the
  corresponding entry of the other, their ordered products are zero simultaneously
  (`List.Forall₂.prod_eq_zero_iff_of_pow`, in
  [`GroupTheory.Algebra.GroupWithZero.Reduced.List`](../GroupTheory/Algebra/GroupWithZero/Reduced/List.lean)).
  Exponents may vary per occurrence, including repeated bases; empty lists are allowed.
  This preserves the product-zero condition, not product values.

- **Nilpotency classes.** In any monoid with zero, `nilpotencyClass_pow` gives
  `nilpotencyClass (a ^ n) = (nilpotencyClass a + n - 1) / n` for every natural
  exponent. At exponent zero this uses total natural-number division, not a
  ceiling at zero. `nilpotencyClass_map` preserves the class under unital monoid
  maps that preserve and reflect zero; injectivity is not required.
  Diagonal semiconjugacy
  `SemiconjBy a x a` and nilpotence of `x` give
  `nilpotencyClass a ≤ nilpotencyClass x + 1`
  (`SemiconjBy.nilpotencyClass_le_add_one`;
  [`GroupTheory.Algebra.GroupWithZero.Nilpotent`](../GroupTheory/Algebra/GroupWithZero/Nilpotent.lean)).
  In any semiring, a finite pairwise orthogonal family satisfies
  `nilpotencyClass (∑ i ∈ s, f i) ≤
  max (nilpotencyClass (0 : R)) (s.sup (fun i => nilpotencyClass (f i)))`
  (`Finset.nilpotencyClass_sum_le_of_pairwise_mul_eq_zero`;
  [`GroupTheory.Ring.Nilpotent.Finset`](../GroupTheory/Ring/Nilpotent/Finset.lean)).
  The class of zero accounts for empty support. Neither bound requires
  commutativity or nontriviality; the upper bound has no nilpotence hypothesis
  and uses Mathlib's convention that nonnilpotent elements have class zero.

- **Commuting divisors and products.** In a monoid, `a ∣ c` and `Commute a c`
  imply `a ^ n ∣ c ^ n` for every natural exponent `n`, including zero
  (`Commute.pow_dvd_pow_of_dvd`;
  [`GroupTheory.Algebra.Divisibility.Basic`](../GroupTheory/Algebra/Divisibility/Basic.lean)).
  In a monoid with zero, if `a` is also nilpotent, then
  `nilpotencyClass c ≤ nilpotencyClass a`
  (`Commute.nilpotencyClass_le_of_dvd`). Thus a nilpotent `a` commuting with
  `b` gives `nilpotencyClass (a * b) ≤ nilpotencyClass a`
  (`Commute.nilpotencyClass_mul_le_left`;
  [`GroupTheory.Algebra.GroupWithZero.Nilpotent`](../GroupTheory/Algebra/GroupWithZero/Nilpotent.lean)).
  If a nilpotent element `a` occurs in a list `l` and commutes with every entry,
  then `nilpotencyClass l.prod ≤ nilpotencyClass a`
  (`List.nilpotencyClass_prod_le_of_mem`;
  [`GroupTheory.Algebra.BigOperators.GroupWithZero.List`](../GroupTheory/Algebra/BigOperators/GroupWithZero/List.lean)).
  No other factor or list entry need be nilpotent, and other list entries
  need not commute with one another. Trivial monoids with zero are allowed.
  The bounds require nilpotence of `a`: the total class is zero for
  nonnilpotent elements, so a class inequality alone does not imply nilpotence.

- **Vanishing powers of finite commuting sums.** In any semiring, let `s : Finset ι`,
  `f : ι → R` and `n : ι → ℕ`. If `f i ^ n i = 0` for every `i ∈ s`, and
  `f i` commutes with `f j` for distinct `i, j ∈ s`, then
  `(∑ i ∈ s, f i) ^ (1 + ∑ i ∈ s, (n i - 1)) = 0`
  (`Finset.sum_pow_eq_zero_of_pairwise_commute`;
  [`GroupTheory.Ring.Nilpotent.Finset`](../GroupTheory/Ring/Nilpotent/Finset.lean)).
  Subtraction is natural-number subtraction. The individual exponents need not be
  equal or positive; no commutativity or nontriviality of the semiring is assumed.
  Empty support gives exponent one, while a supported zero exponent forces the zero
  semiring. The index type need not be finite or nonempty.

- **Equality from finite power-sampling sets.** Let `S : Set M`, where `M` and `N`
  are monoids. Suppose every `x : M` admits `s : Finset ι` and `e : ι → ℕ` with
  `s.gcd e = 1` and `x ^ (e i) ∈ S` for every `i ∈ s`. For any common carrier
  `F` with `FunLike F M N` and `MulHomClass F M N`, fixed `g h : F` satisfy
  `Set.EqOn g h S ↔ g = h` whenever every `g x` is left-regular. The source,
  target, map-carrier and index universes are independent. Both `s` and `e` may
  depend on `x`; zero and repeated exponents are allowed. No unit-preserving
  map class, regularity of `h`, global cancellation, commutativity, algebraic
  structure on `S`, or finiteness or nonemptiness of the index type is required.
  The additive form uses `AddHomClass`, additive monoids and natural multiples.
  Use `MulHomClass.eqOn_iff_eq_of_finite_powers_mem_of_isLeftRegular` and
  `AddHomClass.eqOn_iff_eq_of_finite_multiples_mem_of_isAddLeftRegular` from
  [`GroupTheory/MonoidHom/PositivePower.lean`](../GroupTheory/MonoidHom/PositivePower.lean).
- **[Fixed vectors of transitive permutation representations](../GroupTheory/RepresentationOfMulAction.lean).**
  If a group acts pretransitively on a finite nonempty set `X`, its permutation
  representation over any semiring `R` has fixed submodule linearly equivalent
  to `R`. The image of `r` has coefficient `r` at every point, and the inverse
  evaluates at any point. The acting group need not be finite, and the
  coefficient semiring may be noncommutative or zero. No invertible group
  order is required. The construction uses
  Mathlib's permutation representations and this library's fixed submodules.
  Finite coefficient support forces the carrier to be finite whenever a fixed
  vector is nonzero; on an infinite carrier the fixed submodule is bottom.

- **[Normalized finite-group norms](../GroupTheory/RepresentationAveragingProjector.lean).**
  If the order of a finite group is a unit in a possibly noncommutative semiring,
  the normalized norm is an idempotent self-intertwiner whose range is exactly
  the existing fixed submodule. Modules need only be additive commutative monoids;
  the construction uses `Finite`, and its sum formula works with any finite
  enumeration and any unit representing the group order. It commutes with
  intertwiners and is the unique equivariant retraction onto the fixed vectors.
  Under Mathlib's commutative-ring, additive-commutative-group, `Fintype` and
  invertible-order hypotheses, its underlying linear map
  [agrees with Mathlib's `Representation.averageMap`](../GroupTheory/RepresentationAveragingProjectorComparison.lean).

- **Power congruences modulo radical ideals.** For a commutative ring and a
  radical ideal `I`, membership of both `x ^ m - y ^ m` and `x ^ n - y ^ n` in `I`
  is equivalent to membership of `x ^ Nat.gcd m n - y ^ Nat.gcd m n` in `I`.
  Natural exponents may be zero and the ring need not be nontrivial. See
  `Ideal.IsRadical.pow_gcd_sub_pow_gcd_mem_iff` in
  [`Ring.Ideal.Power`](../GroupTheory/Ring/Ideal/Power.lean).

- **Integrals and orthogonality of characters.** For a monoid `K` with its original
  topology and measurable space, measurable opens and `[MeasurableMul K]`,
  a nontrivial continuous circle-valued character has complex Bochner integral zero
  against any left-invariant measure. Distinct characters have zero off-diagonal
  integral `∫ x, χ x * conj (ψ x) ∂μ`.
  No group, compactness, finiteness or normalization of the measure is assumed;
  for a nonintegrable function the Bochner integral is zero by definition.
  See `PontryaginDual.integral_eq_zero_of_ne_one` and `integral_mul_conj_eq_zero`
  in [`PontryaginDual.Integral`](../GroupTheory/Topology/PontryaginDual/Integral.lean).
