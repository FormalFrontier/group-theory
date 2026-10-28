# Results

[Back to the overview](../README.md).

The following results are available in this library.

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

See the overview for [index-two subgroups and explicit generators](../README.md#index-two-subgroups-and-explicit-generators).

## Topological refinements

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

**Finite index from dense finite generation.** In a compact Hausdorff
commutative topological group with an abstractly finitely generated dense
subgroup, every positive-power range has finite index and is open. Every
abstract finite-index subgroup is therefore open, without assuming that it is
closed. Additive versions use positive natural-number scalar maps. The dense
integer subgroup of the 2-adic integers witnesses doubling with finite-index
open range and a proper finite-index reduction kernel; the zero scalar map
has infinite-index range. See [the subgroup results](../GroupTheory/Topology/FiniteIndex.lean)
and [the 2-adic examples](../GroupTheoryTest/Topology/FiniteIndex.lean).

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
