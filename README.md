# Group Theory

A Lean library for group actions, fixed vectors and monoid cohomology,
topological groups and abstract automatic continuity, Grothendieck completions,
and abelian arithmetic.
The library depends directly on [Mathlib](https://github.com/leanprover-community/mathlib4)
and [Homological Algebra](https://github.com/FormalFrontier/homological-algebra). Homological Algebra supplies the
finite-homology interface used by the finite group-cohomology results. The [result guide](docs/Results.md) gives detailed
statements, examples and API qualifications, and identifies constructions and
prior results reused from Mathlib.

## Headline results

- **Finite-coordinate factorization.** A homomorphism from an arbitrary product of
  groups, continuous at the identity, into a group with no small subgroups kills
  every element equal to the identity on a suitable finite set of coordinates.
  Globally continuous homomorphisms factor continuously through that finite product,
  uniquely for the chosen finite set. No continuity of group operations is required.
  See [`FiniteCoordinates`](GroupTheory/Topology/Algebra/ContinuousMonoidHom/FiniteCoordinates.lean).

- **Real seminormed spaces and no small subgroups.** A real seminormed space's
  additive group has no small subgroups if and only if its seminorm topology is
  Hausdorff. In particular, every real normed space has no small subgroups, without
  completeness or finite-dimensionality hypotheses. See
  [`NormedSpace.lean`](GroupTheory/Topology/Algebra/Group/NoSmallSubgroups/NormedSpace.lean).

- **No small subgroups and compact-source hom spaces.**
  `NoSmallSubgroups G` means that some identity neighborhood contains no
  nontrivial subgroup. Its neighborhood and positive-powers APIs include an
  open inversion-symmetric identity neighborhood when inversion is continuous.
  For a compact monoid `M` with a topology and a commutative topological group
  `G` with no small subgroups,
  `ContinuousMonoidHom.discreteTopology_of_noSmallSubgroups` proves
  `DiscreteTopology (M →ₜ* G)` for the compact-open topology.
  `Circle.noSmallSubgroups` gives the canonical instance using Mathlib's arc
  `Circle.centeredArc (Real.pi / 2)` and its existing powers criterion. See
  [`Group.NoSmallSubgroups`](GroupTheory/Topology/Algebra/Group/NoSmallSubgroups.lean),
  [`ContinuousMonoidHom.NoSmallSubgroups`](GroupTheory/Topology/Algebra/ContinuousMonoidHom/NoSmallSubgroups.lean)
  and [`Group.NoSmallSubgroups.Circle`](GroupTheory/Topology/Algebra/Group/NoSmallSubgroups/Circle.lean).

- **Pointwise products of dependent finitely supported functions.**
  `DFinsupp.pointwiseMul` gives a non-instance `Mul (Π₀ i, β i)` whenever
  each fibre is a `MulZeroClass`; evaluation multiplies the two coefficients.
  Singles at distinct indices have zero product, and product support is contained
  in the intersection of the supports. No associativity, unit or finite index is
  required. `Finsupp.toDFinsupp_mul` recovers the ordinary pointwise product
  without decidability assumptions. Independently,
  `Finsupp.toDFinsupp_pointwise_smul` compares function-valued scalar actions
  using only a zero-preserving coefficient action. These data are selected
  explicitly, without changing the graded multiplication on `DirectSum`.
  See [`DFinsupp.Pointwise`](GroupTheory/DFinsupp/Pointwise.lean),
  [`Finsupp.Pointwise`](GroupTheory/Finsupp/Pointwise.lean) and
  [`Finsupp.PointwiseScalar`](GroupTheory/Finsupp/PointwiseScalar.lean).

- **Surjectivity of bidual evaluation for discrete groups.** For every discrete
  group `A`, not necessarily commutative,
  `PontryaginDual.eval_surjective_of_discrete A` makes the canonical map
  `PontryaginDual.eval A : A →ₜ* PontryaginDual (PontryaginDual A)` surjective.
  This does not assert injectivity or reflexivity for noncommutative groups. See
  [`PontryaginDual.Discrete.Surjective`](GroupTheory/Topology/PontryaginDual/Discrete/Surjective.lean).

- **Canonical biduality for discrete abelian groups.** For every `A : Type u`
  with `[CommGroup A] [TopologicalSpace A] [DiscreteTopology A]`,
  `PontryaginDual.evalEquivOfDiscrete A` is a continuous multiplicative
  equivalence `A ≃ₜ* PontryaginDual (PontryaginDual A)` with the original
  compact-open topologies. Its forward map is exactly `PontryaginDual.evalHom A`.
  The inverse obeys both inverse laws and is characterized by
  `χ ((PontryaginDual.evalEquivOfDiscrete A).symm Φ) = Φ χ`.
  Both directions are natural for continuous homomorphisms between discrete
  abelian groups in independent universes. No finiteness or countability
  assumption is needed, and the trivial group is included. See
  [`PontryaginDual.Discrete.Equivalence`](GroupTheory/Topology/PontryaginDual/Discrete/Equivalence.lean).

For a finite index type `I` and a commutative topological group `E`,
[`ContinuousMonoidHom.intPiEvalEquiv I E`](GroupTheory/Topology/Algebra/ContinuousMonoidHom/Int/Pi.lean)
identifies the compact-open space `Multiplicative (I → ℤ) →ₜ* E` with `I → E`
by evaluation on the standard integer generators. Its inverse sends `c` to
`ofAdd n ↦ ∏ i, c i ^ n i` and retains the existing finite coproduct of
integer-power homomorphisms. The source has its original product and type-tag
topologies. The empty index is included; no nonemptiness, source local
compactness, separation or discrete-target assumption is needed.

- **Characters of binary products.** Restriction gives
  `PontryaginDual.prodEquiv A B : PontryaginDual (A × B) ≃ₜ*
  (PontryaginDual A × PontryaginDual B)`; the inverse sends `(χ, ψ)` to
  `(a, b) ↦ χ a * ψ b`. The source monoids have their original, arbitrary
  topologies, with no operation-continuity, local-compactness or separation
  assumption. The equivalence uses the entire compact-open character spaces
  and is natural under products of continuous monoid homomorphisms. More
  generally, the compact-open coproduct equivalence for continuous
  homomorphisms has a commutative topological-group target; its algebraic
  restriction universal property needs only a commutative-monoid target with
  continuous multiplication. See
  [`ContinuousMonoidHom`](GroupTheory/Topology/Algebra/ContinuousMonoidHom.lean)
  and [`PontryaginDual.Prod`](GroupTheory/Topology/PontryaginDual/Prod.lean).
  This binary result asserts neither infinite-product duality nor bidual reflexivity.

- **Canonical biduality of binary products and the real plane.**
  `PontryaginDual.evalHom A : A →* PontryaginDual (PontryaginDual A)` bundles
  fixed evaluation for any monoid with a topology. Given factor equivalences
  `eA : A ≃ₜ* PontryaginDual (PontryaginDual A)` and `eB` with the pointwise
  laws `eA a χ = χ a` and `eB b ψ = ψ b`, `PontryaginDual.prodEvalEquiv`
  has evaluation as its forward map and an explicit inverse using the two
  supplied inverses and the product-dual comparison. No additional local
  compactness, group, separation or operation-continuity hypotheses are needed.
  `ContinuousMulEquiv.prodMultiplicative` lifts Mathlib's algebraic
  tag-of-product equivalence under addition and topologies alone.
  `PontryaginDual.realPlaneEvalEquiv` applies the product construction to the
  two real factors and this tag equivalence, on `Multiplicative (ℝ × ℝ)` with
  its original topology. The binary construction allows one-point factors;
  no positive-dimension or nontriviality assumption is imposed.
  See [`PontryaginDual.Prod`](GroupTheory/Topology/PontryaginDual/Prod.lean),
  [`TypeTags`](GroupTheory/Topology/TypeTags.lean) and
  [`PontryaginDual.Real`](GroupTheory/Topology/PontryaginDual/Real.lean).
  This is not an assertion of infinite-product or
  general locally compact abelian biduality.

- **Finite dependent products and finite real function spaces.** For a finite index
  `I` and monoids `A i` with topologies, `PontryaginDual.piEquiv A` identifies
  `PontryaginDual (∀ i, A i)` with `∀ i, PontryaginDual (A i)`, using their entire
  compact-open duals. Restriction uses the identity-supported coordinate
  inclusions; the inverse has value `∏ i, χ i (a i)`. The more general
  `ContinuousMonoidHom.piEquiv A E` has a commutative topological group target
  `E`; the source factors need no continuous operations, commutativity, local
  compactness or separation. Supplied canonical factor bidual equivalences and
  their evaluation laws give `PontryaginDual.piEvalEquiv A e h`, with forward
  map exactly evaluation and inverse given by the supplied coordinate inverses.
  `ContinuousMulEquiv.piMultiplicative A` lifts Mathlib's algebraic tag
  equivalence for any index under addition and topologies alone.
  `PontryaginDual.realPiEvalEquiv I` then gives canonical biduality on the original
  `Multiplicative (I → ℝ)` for every finite `I`, including the empty index and
  hence dimension zero. This real-case consequence is auxiliary to the duality
  setting of Neukirch–Schmidt–Wingberg. No infinite-product or general locally
  compact abelian duality theorem is asserted. See
  [`ContinuousMonoidHom.Pi`](GroupTheory/Topology/Algebra/ContinuousMonoidHom/Pi.lean),
  [`PontryaginDual.Pi`](GroupTheory/Topology/PontryaginDual/Pi.lean) and
  [`PontryaginDual.Real`](GroupTheory/Topology/PontryaginDual/Real.lean).
  The finite algebraic universal property reuses Mathlib's work of Joachim
  Breitner and Yakov Pechersky; the coordinate and tag equivalences reuse the
  Mathlib formalizations credited in those modules.

- **Integer characters by generator evaluation.** For any topological group
  `E`, `ContinuousMonoidHom.intEvalHomeomorph E` identifies the compact-open
  space `Multiplicative ℤ →ₜ* E` with `E`, by evaluation at
  `Multiplicative.ofAdd (1 : ℤ)`. The inverse sends `e` to the continuous
  homomorphism with underlying map `zpowersHom E e`, taking `n` to
  `e ^ n.toAdd`. For commutative `E`, `ContinuousMonoidHom.intEvalEquiv E`
  is a continuous multiplicative equivalence with the same homeomorphism.
  No local compactness or Hausdorff hypothesis is needed. Specializing to
  `Circle` identifies the whole `PontryaginDual (Multiplicative ℤ)` with
  `Circle`. The characteristic laws and target naturality are in
  [`ContinuousMonoidHom.Int`](GroupTheory/Topology/Algebra/ContinuousMonoidHom/Int.lean),
  which reuses Mathlib's integer universal property and compact-open continuity
  results, with the formalization credits listed in its references.

**[Complete headline catalogue: statements, hypotheses and module links](docs/HeadlineResults.md).**
The families below give an overview; the catalogue retains the full statements
and qualifications. For API details and examples, see the
[result guide](docs/Results.md); for imports and applications, see the
[usage guide](docs/Usage.md).

### Zero-sum pairs and multiplicative images

In a nonunital, nonassociative semiring, `a + b = 0` implies `a * a = b * b`.
A multiplication-preserving function into any monoid sends `a` and `b` to
units simultaneously, without preserving addition, zero or one or requiring
commutativity of the target. See the
[zero-sum API](GroupTheory/Algebra/IsAddUnit.lean).

### Reduced powers and nilpotence

- Cyclic products in a monoid with zero satisfy
  `nilpotencyClass (a * b) ≤ nilpotencyClass (b * a) + 1`, and symmetrically; see
  [nilpotency classes](GroupTheory/Algebra/GroupWithZero/Nilpotent.lean).

In a reduced ring, not necessarily commutative, equality at two coprime natural
powers determines an element; equality at two exponents is equivalent to equality
at their gcd. In a reduced monoid with zero, positive powers preserve left and
right annihilators. Aligned lists of positive powers preserve product-zero, not
product values. See the [complete statements](docs/HeadlineResults.md#further-algebraic-and-character-results)
and the [reduced-ring power API](GroupTheory/Ring/Power.lean).
Over a commutative ring, equality of two powers modulo a radical ideal is
equivalent to equality at their gcd, including zero exponents; see the
[radical-ideal API](GroupTheory/Ring/Ideal/Power.lean).

In any monoid with zero, `nilpotencyClass_pow` gives
`nilpotencyClass (a ^ n) = (nilpotencyClass a + n - 1) / n` for every natural
exponent, using total natural-number division at zero. Unital monoid maps preserving and
reflecting zero preserve the class; injectivity is not required. See
[`Algebra.GroupWithZero.Nilpotent`](GroupTheory/Algebra/GroupWithZero/Nilpotent.lean).
Separately, `SemiconjBy a x a` and nilpotence of `x` bound the
nilpotency class of `a` by that of `x` plus one. Finite pairwise orthogonal sums
over any semiring are nilpotent exactly when every supported summand is nilpotent,
with an explicit class bound. For finite pairwise commuting families with
`f i ^ n i = 0`, the sum vanishes to the power `1 + ∑ i ∈ s, (n i - 1)`.
No commutativity or nontriviality of the semiring, positivity of the individual
exponents, or finite index type is assumed. The
[catalogue](docs/HeadlineResults.md#further-algebraic-and-character-results) records
empty-support cases and the class-zero convention for nonnilpotent elements;
these results use [`Ring.Nilpotent.Finset`](GroupTheory/Ring/Nilpotent/Finset.lean).

For a semiring algebra over a commutative semiring, a finite sum of pairwise
commuting submodules has total nilpotency class at most one plus the sum of the
predecessors of the summands' total classes. A finite span satisfies the corresponding
generator-class bound when the generators' principal submodules pairwise commute;
the generators themselves need not commute. Neither bound assumes summand or
generator nilpotence, and both include empty support and trivial carriers. See the
[finite-submodule bounds](GroupTheory/Ring/Nilpotent/Submodule.lean).

Over a commutative semiring `R`, the finitely generated ideal criterion
`Ideal.FG.isNilpotent_iff_le_nilradical` characterizes nilpotence by containment
in the nilradical. The finite-span bound specializes to
`nilpotencyClass (Ideal.span (↑s : Set R)) ≤ 1 + ∑ x ∈ s, (nilpotencyClass x - 1)`.
Nonnilpotent ideals have total class zero, so this upper bound alone is not a
nilpotence criterion. See the [finite-ideal API](GroupTheory/Ring/Nilpotent/Ideal.lean).

For commuting elements `a, c` in any monoid, `a ∣ c` implies
`a ^ n ∣ c ^ n` for every natural `n`, including zero. In a monoid with zero,
if `a` is nilpotent, the commuting multiple has nilpotency class at most that of
`a`. In particular this bounds a product `a * b` when `a` commutes with `b`,
and a list product when the nilpotent `a` occurs in the list and commutes with
every entry. Other entries need not be nilpotent or commute with one another.
These bounds retain the nilpotence premise: the total class is zero for
nonnilpotent elements, so a class inequality alone is not a nilpotence criterion.
See the [commuting-divisor API](GroupTheory/Algebra/Divisibility/Basic.lean),
[list-product API](GroupTheory/Algebra/BigOperators/GroupWithZero/List.lean) and
[full statements](docs/HeadlineResults.md#further-algebraic-and-character-results).

### Finite sums and product homomorphisms

For submodules of a semiring equipped with a module structure over another
semiring, `Submodule.sum_eq_sup` identifies finite sums with finite suprema,
complementing the zero/bottom and addition/supremum identities.
No scalar-tower, commutativity, or algebra hypothesis is required. See
[`Algebra.Algebra.Operations`](GroupTheory/Algebra/Algebra/Operations.lean).

Finite families of nonunital ring homomorphisms whose distinct images annihilate
each other in both orders have a sum homomorphism, even for nonunital,
nonassociative source and target semirings. For a finite dependent product of
unital nonassociative semirings, `Pi.liftRingHom` instead builds a **unital**
homomorphism into an associative semiring from nonunital component maps: their
unit images must be pairwise orthogonal and sum to one. No commutativity, global
centrality or nontriviality is assumed. The empty-index case is included; its
cover-one premise forces the target to satisfy `0 = 1`. See
[`Ring.Hom.FiniteSum`](GroupTheory/Ring/Hom/FiniteSum.lean) and the
[catalogue](docs/HeadlineResults.md#further-algebraic-and-character-results) for
application, zero-off extension and uniqueness laws, with their hypotheses.

### Power restrictions and order

In any group, membership of every power in a finite family in a subgroup-like
object is equivalent to membership of the gcd power; gcd one detects the element.
The subgroup generated by the selected powers is the cyclic subgroup generated
by that gcd power. Additive groups have the corresponding natural-multiple
formulas. No commutativity or normality is needed; empty and all-zero families
generate the trivial subgroup. See the
[subgroup-power API](GroupTheory/Algebra/Group/Subgroup/Power.lean).

For any group element `a` and natural exponents `m n`, the intersection of
`Subgroup.zpowers (a ^ m)` and `Subgroup.zpowers (a ^ n)` is
`Subgroup.zpowers (a ^ (Nat.lcm m n))`. The additive version uses the
integer-multiple subgroups of `m • a` and `n • a`. Zero exponents are included;
no commutativity or order assumption is needed. See the same
[subgroup-power API](GroupTheory/Algebra/Group/Subgroup/Power.lean).

For a finite family of natural exponents, intersecting the cyclic power subgroups
with `Subgroup.zpowers a` gives the subgroup generated by the lcm power.
Nonempty families need no initial cyclic factor; for an empty family the plain
intersection is top. Additive groups have the corresponding natural-multiple
formula. See the [catalogue](docs/HeadlineResults.md#power-restrictions-and-order).

In a monoid, let `a` have injective left multiplication (left regularity).
Equality of its powers and those of arbitrary `b` at a finite family of natural
exponents is equivalent to equality at their gcd;
a family with gcd one determines `a = b`. The same finite-family criterion
holds separately when `a` has injective right multiplication (right regularity).
No regularity of `b` or global cancellation is needed; additive versions hold in
additive monoids. Empty families and zero exponents are included. See the
[power-kernel API](GroupTheory/MonoidHom/PositivePower.lean).

Let `f : M →* N`, where `N` is a monoid and `M` has only multiplication and a
chosen one (`MulOne`). If the range of `f` contains a positive power of every
element of `N`, it detects equality of homomorphisms from `N` into any monoid
with unique positive roots.

For finite image detection, let `f : A →* M`, with only `MulOne A` and monoids
`M, N`. Suppose each `x : M` admits `s : Finset ι` and `e : ι → ℕ` with
`s.gcd e = 1` and `x ^ (e i) ∈ Set.range f` for every `i ∈ s`. For fixed
`g h : M →* N`, left-regularity of every `g x` gives
`g.comp f = h.comp f ↔ g = h`; a separate criterion uses right-regularity
instead. In both, `h` is arbitrary, the four universes are independent, and
`s, e` may depend on `x`. Additive peers use `AddZero A`, additive monoids
and natural multiples.
No global cancellation, commutativity, group structure, surjectivity, positivity,
finite or nonempty index type, or decidable equality is assumed. Zero and
repeated exponents are allowed; empty or all-zero families cannot have gcd one.
The natural-set left interface is the `ι = ℕ`, `e = id` specialization;
coprime and consecutive-power adapters remain available. Consecutive-power
images give precomposition injectivity into left-cancellative targets.
The [catalogue](docs/HeadlineResults.md#power-restrictions-and-order) distinguishes
these fixed-pair image criteria from elementwise power kernels and injectivity
on all homomorphisms into an arbitrary monoid.

More generally, a set of a monoid that contains, for each element, a finite
family of its powers with gcd-one exponents detects equality of fixed
multiplication-preserving maps into a monoid whenever the first map has
left-regular values. Unit preservation and regularity of the second map are not
required. The [set criterion and additive form](docs/HeadlineResults.md#further-algebraic-and-character-results)
allow independent universes, element-dependent families and zero or repeated exponents.

For a multiplicatively Archimedean commutative monoid with a linear order,
chosen `0`, `0 ≤ 1` and strictly monotone multiplication by positive elements,
a multiplication-closed set is bounded above exactly when all its members are
at most `1`, even for empty sets. See the
[power and order catalogue](docs/HeadlineResults.md#power-restrictions-and-order)
for additive restriction, pointwise comparison and multiplicative-map versions.

### Group actions and presentations

For arbitrary subgroups `H, K` of a group `G`, equivariant maps `G/H → G/K`
exist exactly when `H ≤ gKg⁻¹` for some `g`; the coset actions are isomorphic
exactly when the subgroups are conjugate, not merely when maps exist both ways.
Group-valued diagrams have presentations by free products modulo the normal
closure of arrow relations. For a group homomorphism `f : A →* B`, a pushout
along `A → T` with `T` trivial is `B / normalClosure (range f)`.
Objectwise-surjective compatible homomorphisms between two diagrams over the same
arbitrary indexing category induce a surjection of colimits; its kernel is the
normal closure of the component kernels' images. The object groups may have
independent universes.
The [actions and presentations catalogue](docs/HeadlineResults.md#group-actions-and-presentations)
also gives coefficient-sum relations over semirings and the precise universal
properties, including their universe qualifications.

### Fixed vectors and averaging

For monoid representations on additive commutative monoid modules over a
semiring, intertwiners `f, g` with injective `f` and `Function.Exact f g` remain
exact on fixed submodules. Fixed vectors commute with arbitrary products and
algebraic direct sums, but do not in general preserve surjectivity.

**[Noetherian monoid cohomology](GroupTheory/Cohomology/Noetherian.lean).**
For `A : Rep R G` over any ring `R` and monoid `G`,
[inhomogeneous cochains](GroupTheory/Cohomology/Basic.lean) have degree `n`
term `(Fin n → G) → A` and differential using the given linear action.
Degree zero is canonically `R`-linearly equivalent to `A.ρ.fixedSubmodule`.
If `IsNoetherian R A`, degree-zero cohomology is Noetherian for arbitrary `G`;
if also `Finite G`, cohomology is Noetherian in every natural degree.
Neither commutativity nor Noetherianity of `R`, finiteness of the underlying
`A`, nor a trivial action is required. The [catalogue](docs/HeadlineResults.md#fixed-vectors-and-averaging)
gives the independent universes and the narrower Mathlib group-cohomology comparison.

For a finite group whose order is a unit in a possibly noncommutative semiring,
a given linear lift between intertwining maps can be replaced by an
intertwining lift; no surjectivity of the map lifted through is required.
Separately, for a finite group acting by additive automorphisms on an additive
commutative group, bijective multiplication by the group order makes every
crossed map principal. The [fixed-vector and averaging catalogue](docs/HeadlineResults.md#fixed-vectors-and-averaging)
keeps the representation and additive-action hypotheses distinct and gives the
explicit averaging formula and its naturality.

A pretransitive group action on a finite nonempty set has permutation-fixed
submodule linearly equivalent to the coefficient semiring; the acting group need
not be finite and no invertible order is needed. A nonzero fixed vector forces
the acted-on carrier to be finite; on an infinite pretransitive carrier the fixed
submodule is bottom, still over any coefficient semiring. Separately, for a finite group
whose order is a unit in a possibly noncommutative semiring, the normalized norm
is a natural idempotent self-intertwiner with range the fixed submodule, on
additive commutative monoid modules. Its narrower commutative-ring comparison
with Mathlib's `averageMap` is in the
[catalogue](docs/HeadlineResults.md#further-algebraic-and-character-results).

### Free groups, arithmetic and Grothendieck completions

For any generator relabeling `σ : I → J`, the kernel of `FreeGroup.map σ` is
the **normal closure** of all `of i * (of k)⁻¹` with `σ i = σ k`. The label
types may be empty and lie in independent universes; no injectivity, surjectivity
or finiteness is needed. The induced homomorphism is injective or surjective
exactly when `σ` is. See the [free-group map API](GroupTheory/FreeGroup/Map.lean).

For a finite-index subgroup `H` of a finitely generated free group `G`,
`rank H + [G:H] = rank G * [G:H] + 1`, including ambient rank zero.
Mathlib supplies subgroup freeness and finite generation. Biadditive maps from
two additive commutative monoids to an additive commutative group extend uniquely
to both Grothendieck completions; a semiring's additive completion has a canonical
ring structure and universal ring lifts, without cancellation.

For an additive commutative group `V`, subgroup `L` and natural `n`, bijective
multiplication by `n` on `V` gives `(V/L)[n] ≃+ L/nL`. If `L` is finitely generated,
this torsion subgroup is finite of cardinality `n ^ Module.finrank ℤ L`, without
freeness of `L` or ambient finite generation. The
[free-group, arithmetic and completion catalogue](docs/HeadlineResults.md#free-groups-arithmetic-and-grothendieck-completions)
also links the explicit index-two generators and nilpotence reflection on additive units.

### Topology and abstract homomorphisms

For a subsemigroup `S` of a group with continuous fixed left translations,
its topological closure is stable under inverses if that closure's induced
topology is Noetherian and each right translation by a member of `S` is
continuous on the closure. No ambient Noetherianity or continuous inversion is
assumed. See
[`Subsemigroup.inv_mem_closure_of_noetherianSpace`](GroupTheory/Topology/Algebra/Group/Subsemigroup/Closure.lean)
and the [precise inputs](docs/Usage.md#inverses-in-a-subsemigroups-closure).
Alternatively, with the same local right continuity, inverse stability follows
if `S` is preirreducible and strict inclusion of nonempty irreducible closed
subsets of the ambient group is well-founded (`WellFoundedLT`). This applies to
every element of the closure, not just members of `S`.

More generally, a closed self-embedding of any topological space is surjective
if the space has finitely many irreducible components and well-founded strict
inclusion of nonempty irreducible closed subsets. No Noetherianity or separation is assumed;
see the [closed-embedding theorem](GroupTheory/Topology/ClosedEmbedding.lean).

In a compact Hausdorff commutative topological group with a dense algebraically
finitely generated subgroup, every abstract finite-index subgroup is open.
Every abstract homomorphism from such a source to a compact nonarchimedean group
is continuous, even with an infinite image; this does not assert local constancy.
The [topology catalogue](docs/HeadlineResults.md#topology-and-abstract-homomorphisms)
also covers ultrafilter-limit counterexamples to continuity, cofinite groups and
actions, locally constructible subgroups, identity components, compact open
subgroups and finite-coordinate factorizations.

Two continuity interfaces are separate: a pretransitive group action by continuous
fixed-element maps on a finite T0 space makes its given topology discrete, with
no topology or finiteness needed on the group. By contrast, for topological spaces
`M, X` where every point of `X` has a finite neighborhood, a primitive scalar
operation `M × X → X` is jointly continuous if **both** fixed-scalar maps and orbit
maps are continuous; no action laws or separation are required.
The catalogue includes the local finite-neighborhood criterion for arbitrary maps.

### Pontryagin characters and bidual evaluation

- **Saturation of uniformly spanning character sets.** Let `K` be a compact
  monoid with measurable opens and measurable fixed translations, and let `μ`
  be a finite nonzero left-invariant measure. If the complex span of the scalar
  characters from a set `S` is uniformly dense in `C(K, ℂ)`, then `S` is the
  entire Pontryagin dual. In particular, every point-separating subgroup of
  characters is the whole dual. The measure need not be a probability measure;
  no group, Hausdorffness or countability assumption on `K` is required. See
  [`PontryaginDual.Saturation`](GroupTheory/Topology/PontryaginDual/Saturation.lean).

- **Uniform density of scalar characters.** Let `K` be a compact monoid with a
  topology, and let `S` be a subgroup of its continuous `Circle`-valued
  characters that separates points of `K`. The complex linear span of
  `x ↦ (χ x : ℂ)`, for `χ ∈ S`, is dense in `C(K, ℂ)` for the uniform topology.
  No measure, continuity of the monoid operations, or separation or countability
  typeclass on `K` is required. This uses Mathlib's scalar Stone–Weierstrass theorem;
  see [`GroupTheory.Topology.PontryaginDual.StoneWeierstrass`](GroupTheory/Topology/PontryaginDual/StoneWeierstrass.lean).

- **Real characters and canonical biduality.** Every continuous circle-valued
  character of the additive real line has a unique period-one Fourier frequency.
  `PontryaginDual.realEquiv` identifies the original real topology with the
  compact-open topology on the entire real character space. The forward map of
  `PontryaginDual.realEvalEquiv` is canonical bidual evaluation, not a separately
  chosen algebraic identification. See
  [`PontryaginDual.Real`](GroupTheory/Topology/PontryaginDual/Real.lean).

- **Transport of the whole Pontryagin dual.** A continuous multiplicative
  equivalence `A ≃ₜ* B` induces `PontryaginDual B ≃ₜ* PontryaginDual A` by
  precomposition, with the original compact-open topologies. Only monoids with
  topologies are needed: no local compactness, Hausdorffness or continuity of
  their operations is assumed. See `PontryaginDual.mapEquiv` in
  [`PontryaginDual`](GroupTheory/Topology/PontryaginDual.lean).

- **Canonical Pontryagin bidual evaluation.** For a monoid `A` equipped with a
  topology and `[LocallyCompactPair A Circle]`, `PontryaginDual.eval A` is the
  continuous homomorphism `a ↦ (χ ↦ χ a)` into the existing compact-open bidual.
  It is natural under arbitrary continuous monoid homomorphisms. If the dual
  also forms a locally compact pair with `Circle`, evaluation on the dual is
  a section of the dual of evaluation. No group, commutativity, continuity of
  the monoid operations or Hausdorff hypothesis on `A` is required. These
  general monoid results alone do not assert injectivity, surjectivity or full Pontryagin reflexivity
  of the original evaluation. See
  [`GroupTheory.Topology.PontryaginDual`](GroupTheory/Topology/PontryaginDual.lean).

- **Bidual evaluation separates discrete abelian groups.** For a commutative
  group with its discrete topology, `PontryaginDual.eval_injective_of_discrete`
  proves that the canonical continuous bidual evaluation is injective. No
  finiteness, finite generation or countability is required. The injectivity
  theorem is available in
  [`PontryaginDual.Discrete`](GroupTheory/Topology/PontryaginDual/Discrete.lean).
  For full canonical continuous reflexivity, including the inverse, use
  `PontryaginDual.evalEquivOfDiscrete` in
  [`PontryaginDual.Discrete.Equivalence`](GroupTheory/Topology/PontryaginDual/Discrete/Equivalence.lean).

- **Integrals and orthogonality of characters.** For a monoid `K` with its original
  topology and measurable space, measurable opens and `[MeasurableMul K]`,
  a nontrivial continuous circle-valued character has complex Bochner integral zero
  against any left-invariant measure. Distinct characters have zero off-diagonal
  integral `∫ x, χ x * conj (ψ x) ∂μ`.
  No group, compactness, finiteness or normalization of the measure is assumed;
  for a nonintegrable function the Bochner integral is zero by definition.
  See `PontryaginDual.integral_eq_zero_of_ne_one` and `integral_mul_conj_eq_zero`
  in [`PontryaginDual.Integral`](GroupTheory/Topology/PontryaginDual/Integral.lean).

## Using the library

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "groupTheory"
git = "https://github.com/FormalFrontier/group-theory.git"
rev = "main"
```

GitHub `main` contains reviewed releases, not development commits. Lake resolves
that ref when you add or update the dependency; your `lake-manifest.json` keeps
that resolution until another update. Use the release's matching Lean toolchain
and mathlib revision; Lake resolves only one revision of each package in a build.
For a fixed reproducible version, replace `main` with the full commit of a
published release. Dependencies from another Formal Frontier library
use the GitHub URL and full published release commit, not moving
`main`, development commits or PR heads.

Import the aggregate module with:

```lean
import GroupTheory
```

## Use and verification

Detailed imports, applications, client boundaries and compatibility notes are in
the [usage guide](docs/Usage.md). Use the module imports documented with each
interface; the aggregate module does not re-export every theory module.
`GroupTheoryTest` is for repository verification, not downstream imports.

### Building and checking the repository

The checkout's [`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml)
and [`lake-manifest.json`](lake-manifest.json) record the Lean version and exact
resolved dependency revisions. Mathlib and the public GitHub release of Homological
Algebra are pinned to full commits, with a common Mathlib revision. Use the
checked-in manifest and toolchain together for a reproducible build rather than
updating either dependency independently. Run from this repository:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build GroupTheory GroupTheoryTest
```

Both roots include the finite-coordinate homomorphism and left-coset modules
and their supporting clients for whole-interface checking. Verification of the
public results and private clients requires both the build and the complete
standard-axiom audit described below.

The matching precompiled mathlib cache **must succeed before the build**.
The test-only compact/discrete and left-coset observer modules keep their helper
declarations private and may emit `linter.privateModule` warnings. The command above retains
those warnings; adding `--wfail` treats them as errors.
`LEAN_NUM_THREADS` is runtime tuning, not a child-process or memory cap;
`LAKE_JOBS` is unsupported by this pinned Lake. Build both roots when
verifying the maintained producer and clients. The configured CI also checks
complete transitive axioms, including private declarations, against only
`propext`, `Classical.choice` and `Quot.sound`; building alone does not
establish that audit. No benchmark, memory guarantee or source-coverage
claim is implied by this guidance.

## Contents

| Mathematics | Modules |
| --- | --- |
| Finite orthogonal sums of nonunital ring homomorphisms and unital maps from finite products | [`Ring.Hom.FiniteSum`](GroupTheory/Ring/Hom/FiniteSum.lean) |
| Finite sums of submodules as finite suprema over semirings | [`Algebra.Algebra.Operations`](GroupTheory/Algebra/Algebra/Operations.lean) |
| Powers of commuting divisors | [`Algebra.Divisibility.Basic`](GroupTheory/Algebra/Divisibility/Basic.lean) |
| Nilpotency-class bound from a chosen commuting list entry | [`Algebra.BigOperators.GroupWithZero.List`](GroupTheory/Algebra/BigOperators/GroupWithZero/List.lean) |
| Nilpotency classes of powers and zero-reflecting maps; bounds from commuting divisors and products, semiconjugacy and orthogonal sums; vanishing powers of finite commuting sums | [`Algebra.GroupWithZero.Nilpotent`](GroupTheory/Algebra/GroupWithZero/Nilpotent.lean), [`Ring.Nilpotent.Finset`](GroupTheory/Ring/Nilpotent/Finset.lean) |
| Total nilpotency-class bounds for finite commuting submodule sums and finite spans; finitely generated ideal criterion and specialization | [`Ring.Nilpotent.Submodule`](GroupTheory/Ring/Nilpotent/Submodule.lean), [`Ring.Nilpotent.Ideal`](GroupTheory/Ring/Nilpotent/Ideal.lean) |
| Equality of multiplicative or additive maps from finite gcd-one power-sampling sets | [`MonoidHom.PositivePower`](GroupTheory/MonoidHom/PositivePower.lean) |
| Fixed vectors of transitive permutation representations on finite or infinite carriers | [`RepresentationOfMulAction`](GroupTheory/RepresentationOfMulAction.lean) |
| Normalized norms, natural idempotent self-intertwiners and comparison with Mathlib's averaging map | [`RepresentationAveragingProjector`](GroupTheory/RepresentationAveragingProjector.lean), [`RepresentationAveragingProjectorComparison`](GroupTheory/RepresentationAveragingProjectorComparison.lean) |
| Real Fourier self-duality and canonical biduality | [`PontryaginDual.Real`](GroupTheory/Topology/PontryaginDual/Real.lean) |
| Whole compact-open dual transport; canonical bidual evaluation, naturality and triangular retraction | [`PontryaginDual`](GroupTheory/Topology/PontryaginDual.lean) |
| Uniform density of scalar characters from point-separating subgroups | [`PontryaginDual.StoneWeierstrass`](GroupTheory/Topology/PontryaginDual/StoneWeierstrass.lean) |
| Injectivity of canonical bidual evaluation for discrete abelian groups | [`PontryaginDual.Discrete`](GroupTheory/Topology/PontryaginDual/Discrete.lean) |
| Canonical continuous bidual equivalence, inverse character law and forward/inverse naturality for discrete abelian groups | [`PontryaginDual.Discrete.Equivalence`](GroupTheory/Topology/PontryaginDual/Discrete/Equivalence.lean) |
| Integrals and off-diagonal orthogonality of Pontryagin characters | [`PontryaginDual.Integral`](GroupTheory/Topology/PontryaginDual/Integral.lean) |
| Finite kernels and fibers with weak homomorphism targets | [`MonoidHom.Finite`](GroupTheory/MonoidHom/Finite.lean) |
| Subgroup membership and generated cyclic subgroups through finite powers; finite cyclic-power intersections | [`Algebra.Group.Subgroup.Power`](GroupTheory/Algebra/Group/Subgroup/Power.lean) |
| Regular-element power kernels and homomorphism restriction through powers | [`MonoidHom.PositivePower`](GroupTheory/MonoidHom/PositivePower.lean) |
| Coinduced cofinite topologies and finite-versus-infinite fibers | [`Topology.Cofinite`](GroupTheory/Topology/Cofinite.lean), [paired integer projections](GroupTheoryTest/Topology/Cofinite.lean) |
| Cofinite group operations and actions, coset quotients and homomorphisms | [`Group.Cofinite`](GroupTheory/Topology/Algebra/Group/Cofinite.lean) |
| Coefficient-sum kernels and factorization over semirings | [`Finsupp.CoefficientSum`](GroupTheory/Finsupp/CoefficientSum.lean), [noncancellative-target client](GroupTheoryTest/Finsupp/CoefficientSum.lean) |
| Group pushouts and normal-closure quotients | [`Category.Grp.Pushout`](GroupTheory/Category/Grp/Pushout.lean) |
| Group-diagram free-product presentations | [`Category.Grp.Colimits`](GroupTheory/Category/Grp/Colimits.lean) |
| Compatible maps of group colimits and their kernels | [`Category.Grp.ColimitMap`](GroupTheory/Category/Grp/ColimitMap.lean), [`ColimitMapKernel`](GroupTheory/Category/Grp/ColimitMapKernel.lean) |
| Dense unit maps for unit-reflecting monoid homomorphisms | [`Topology.Algebra.Group.Units`](GroupTheory/Topology/Algebra/Group/Units.lean), [rational and integer-quotient examples](GroupTheoryTest/Topology/Algebra/Group/Units.lean) |
| Products of submodules and their coordinate splitting | [`LinearAlgebra.Prod`](GroupTheory/LinearAlgebra/Prod.lean), [`LinearAlgebra.Pi`](GroupTheory/LinearAlgebra/Pi.lean) |
| Fixed vectors, products, direct sums and left exactness over semirings | [`RepresentationInvariants`](GroupTheory/RepresentationInvariants.lean), [`RepresentationPi`](GroupTheory/RepresentationPi.lean), [`RepresentationDirectSum`](GroupTheory/RepresentationDirectSum.lean) |
| Inhomogeneous monoid cochains over rings, fixed vectors in degree zero and Noetherian cohomology | [`Cohomology.Basic`](GroupTheory/Cohomology/Basic.lean), [`Cohomology.Noetherian`](GroupTheory/Cohomology/Noetherian.lean) |
| Fixed-submodule transport across coefficient and acting-monoid maps | [`RepresentationFixedFunctoriality`](GroupTheory/RepresentationFixedFunctoriality.lean) |
| Given linear lifts of finite-group intertwining maps | [`RepresentationLifting`](GroupTheory/RepresentationLifting.lean), [`RepresentationLinHomAdd`](GroupTheory/RepresentationLinHomAdd.lean) |
| Finite-group norms and surjections on fixed submodules | [`RepresentationNorm`](GroupTheory/RepresentationNorm.lean), [`RepresentationNormNaturality`](GroupTheory/RepresentationNormNaturality.lean) |
| Additive universal property, biadditive Grothendieck extensions, arbitrary products, cofinal denominator forms and quotient representatives | [`MonoidLocalization.GrothendieckGroup`](GroupTheory/MonoidLocalization/GrothendieckGroup.lean) |
| Ring structures, canonical generators and multiplicative universal properties for additive Grothendieck groups of semirings | [`MonoidLocalization.GrothendieckGroup.Ring`](GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean) |
| Additive-unit absorption and nilpotence reflection in Grothendieck rings | [`Algebra.IsAddUnit`](GroupTheory/Algebra/IsAddUnit.lean), [`MonoidLocalization.GrothendieckGroup.Nilpotent`](GroupTheory/MonoidLocalization/GrothendieckGroup/Nilpotent.lean) |
| Equivariant maps from cosets and subgroup-fixed points | [`GroupAction.Quotient`](GroupTheory/GroupAction/Quotient.lean), [permutation-action and boundary examples](GroupTheoryTest/CosetActionHom.lean) |
| Canonical coset-action isomorphisms and subgroup conjugacy | [`GroupAction.Quotient`](GroupTheory/GroupAction/Quotient.lean), [nonnormal examples](GroupTheoryTest/Topology/Algebra/Group/Quotient.lean) |
| Product-coset orbits and double cosets | [`GroupAction.DoubleCoset`](GroupTheory/GroupAction/DoubleCoset.lean), [permutation and boundary examples](GroupTheoryTest/Topology/Algebra/Group/Quotient.lean) |
| Equivariant maps between nested coset spaces | [`GroupAction.QuotientMap`](GroupTheory/GroupAction/QuotientMap.lean) |
| Invariant equivalence relations and overgroups of point stabilizers | [`GroupAction.InvariantSetoid`](GroupTheory/GroupAction/InvariantSetoid.lean), [nonnormal model](GroupTheoryTest/GroupAction/InvariantSetoid.lean) |
| Action automorphisms, centralizers and normal stabilizers | [`Centralizer`](GroupTheory/GroupAction/Centralizer.lean) |
| Transitive-action automorphisms and normalizer quotients | [`Automorphism`](GroupTheory/GroupAction/Automorphism.lean) |
| Free-group relabeling kernels, injectivity and surjectivity | [`FreeGroup.Map`](GroupTheory/FreeGroup/Map.lean) |
| Finite free bases and finite-index free-group ranks | [`FreeGroup.Rank`](GroupTheory/FreeGroup/Rank.lean) |
| Index-two subgroups, characters and explicit generators | [`Subgroup.IndexTwo`](GroupTheory/Subgroup/IndexTwo.lean), [`FreeGroup.IndexTwo`](GroupTheory/FreeGroup/IndexTwo.lean) |
| Orbit inseparability for actions of preirreducible groups | [`MulAction.Irreducible`](GroupTheory/Topology/Algebra/MulAction/Irreducible.lean) |
| Locally closed subgroups under separate continuity | [`Group.LocallyClosed`](GroupTheory/Topology/Algebra/Group/LocallyClosed.lean), [additive intersection client](GroupTheoryTest/Topology/Algebra/Group/LocallyClosed.lean) |
| Inverses in Noetherian subsemigroup closures | [`Subsemigroup.inv_mem_closure_of_noetherianSpace`](GroupTheory/Topology/Algebra/Group/Subsemigroup/Closure.lean) |
| Inverses in preirreducible closures under ambient irreducible-closed DCC | [`Subsemigroup.inv_mem_closure_of_isPreirreducible`](GroupTheory/Topology/Algebra/Group/Subsemigroup/Closure.lean) |
| Closed self-embeddings with finitely many irreducible components | [`Topology.IsClosedEmbedding.surjective_of_finite_irreducibleComponents`](GroupTheory/Topology/ClosedEmbedding.lean) |
| Fixed-action continuity and subgroup quotients | [`ConstMulAction`](GroupTheory/Topology/Algebra/ConstMulAction.lean), [`Quotient`](GroupTheory/Topology/Algebra/Group/Quotient.lean) |
| Compact open subgroups, open kernels and circle characters | [`CompactOpenSubgroup`](GroupTheory/Topology/CompactOpenSubgroup.lean), [`OpenKernel`](GroupTheory/Topology/OpenKernel.lean), [`CircleCharacter`](GroupTheory/Topology/CircleCharacter.lean) |
| Character subgroups and rational-circle comparison | [`CharacterSubgroups`](GroupTheory/Topology/CharacterSubgroups.lean), [`RationalCircle`](GroupTheory/Topology/RationalCircle.lean), [`RationalCircleCharacter`](GroupTheory/Topology/RationalCircleCharacter.lean) |
| Finite index from dense finite generation | [`FiniteIndex`](GroupTheory/Topology/FiniteIndex.lean) |
| Total boundedness and finite-index subgroup bases | [`TotalBounded`](GroupTheory/Topology/Algebra/Group/TotalBounded.lean) |
| Discrete-valued maps and compact-group factorization | [`CompactDiscrete`](GroupTheory/Topology/ContinuousMap/CompactDiscrete.lean), [`DiscreteFactor`](GroupTheory/Topology/Algebra/CompactGroup/DiscreteFactor.lean) |
| Finite cylinders and coordinate factorizations | [`OpenSubgroup.Pi`](GroupTheory/Topology/Algebra/OpenSubgroup/Pi.lean), [`PiDiscreteFactor`](GroupTheory/Topology/Algebra/CompactGroup/PiDiscreteFactor.lean), [`Group.PiDiscreteFactor`](GroupTheory/Topology/Algebra/Group/PiDiscreteFactor.lean) |
| Identity components and quotients | [`ConnectedComponentOpenSubgroup`](GroupTheory/Topology/ConnectedComponentOpenSubgroup.lean), [`ConnectedComponentQuotient`](GroupTheory/Topology/ConnectedComponentQuotient.lean) |
| Open quotients and compatible sections | [`OpenQuotient`](GroupTheory/Topology/OpenQuotient.lean), [`Sections`](GroupTheory/Topology/Sections.lean) |
| Kernels of quotient maps and scalar torsion | [`QuotientGroup.Kernel`](GroupTheory/QuotientGroup/Kernel.lean), [`QuotientTorsion`](GroupTheory/QuotientTorsion.lean), [`QuotientTorsion.Cardinality`](GroupTheory/QuotientTorsion/Cardinality.lean) |
| Cyclic norms and scalar maps | [`CyclicNorm`](GroupTheory/CyclicNorm.lean), [`FGScalarSurjectivity`](GroupTheory/FGScalarSurjectivity.lean), [`IndexNSmul`](GroupTheory/IndexNSmul.lean) |

## References

See [References and credits](CREDITS.md) for the mathematical sources,
prior formalizations and detailed attribution.

The finite-power subgroup formulas use Mathlib's
`Int.closure_eq_zmultiples_finsetGcd`; the power-kernel and image-detection APIs
also use its finite-gcd, regularity and opposite-structure interfaces.

The zero-sum self-product identity generalizes the argument in
[Valuation Integers](https://github.com/FormalFrontier/valuation-integers);
the unit-image comparison uses Mathlib's `isUnit_mul_self_iff`.

K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87,
Springer, 1982, gives the classical finite-group cohomology vanishing theorem
underlying the [crossed-map averaging results](GroupTheory/CocycleAveraging.lean).

The inverse-closure idea using minimal left translates is due to Flint; see the
[subsemigroup module](GroupTheory/Topology/Algebra/Group/Subsemigroup.lean).

## Credits and license

The cofinite quotient results use Mathlib's coset, quotient-topology, finite-set and
cofinite-topology APIs, together with the dense-fiber formalization in
[`Topology.DenseFibers`](GroupTheory/Topology/DenseFibers.lean).

The cohomology constructions follow Mathlib's group-cohomology formalization by
Amelia Livingston; the square-zero argument follows the alternating-face-map
formalization by Joël Riou, Adam Topaz and Johan Commelin.

The finite commuting-sum power bound reuses Mathlib's binary quantitative nilpotence
bound from Oliver Nash's nilpotent theory.

The free-group relabeling results build on Mathlib's free-group construction
and map API, formalized by Kenny Lau.

Commuting-divisor power divisibility generalizes Mathlib's commutative-monoid
power-divisibility lemma; the nilpotency and list-product bounds use this generic
result and Mathlib's nilpotency-class and list-factorization interfaces.

The finite homomorphism constructions reuse Mathlib's additive finite sums and
Hom/Pi APIs; this library supplies the orthogonal nonunital sum, finite-product
unital lift and their application and uniqueness lemmas. Upstream contributors
are credited in the [module references](GroupTheory/Ring/Hom/FiniteSum.lean).

The finite-integer coordinate equivalence assembles this library's existing
integer, finite-product and type-tag formalizations. Its domain and coordinate
transports follow Mathlib's algebraic congruences and Pi homeomorphism by
Johannes Hölzl, Callum Sutton, Yury Kudryashov, Patrick Massot,
Sébastien Gouëzel, Zhouhang Zhou and Reid Barton, together with the
compact-open hom-space formalization by Thomas Browning and Nailin Guan.
The underlying product and integer universal properties are Joachim Breitner's
noncommutative Pi coproduct and Mario Carneiro's integer-power homomorphism.

Authors: Formal Frontier Agents. The Lean proofs and clients were developed by
Formal Frontier AI agents. Licensed under [Apache-2.0](LICENSE).
