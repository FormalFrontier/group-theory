# Group Theory

A Lean library for group actions and fixed vectors, topological groups and
abstract automatic continuity, Grothendieck completions, and abelian arithmetic.
The library depends directly on [Mathlib](https://github.com/leanprover-community/mathlib4)
and [Homological Algebra](https://github.com/FormalFrontier/homological-algebra). Homological Algebra supplies the
finite-homology interface used by the finite group-cohomology results. The [result guide](docs/Results.md) gives detailed
statements, examples and API qualifications, and identifies constructions and
prior results reused from Mathlib.

## Headline results

- **Restriction through powers.** Let `f : M →* N`, where `M` has the stock `MulOne`
  structure and `N` is a monoid. If every `x : N` has some positive power in `Set.range f`,
  precomposition by `f` is injective on homomorphisms into any monoid with unique positive
  roots (`IsMulTorsionFree`); equality can therefore be checked after restriction. The
  additive statements use positive multiples and torsion-free additive targets.
- **Restriction through consecutive powers.** If for every `x : N` both `x ^ n` and
  `x ^ (n + 1)` lie in `Set.range f` for some natural `n`, precomposition is injective on
  homomorphisms into any left-cancellative monoid. The exponent may be zero; no unique-root,
  commutativity, order or group hypothesis on the target is needed.
- **Pointwise comparison from positive powers.** Under the positive-power range condition,
  homomorphisms `g h : N →* Γ` to a linearly ordered commutative monoid with zero satisfy
  `g (f a) ≤ h (f a)` for all `a : M` if and only if `g x ≤ h x` for all `x : N`.
  Neither associativity nor identity laws on `M` are used, and `N` need not be commutative
  or ordered. The positive exponent need not be uniform. These restriction results are in
  [`GroupTheory/MonoidHom/PositivePower.lean`](GroupTheory/MonoidHom/PositivePower.lean).

- **Locally constructible subgroups.** A locally constructible subgroup is closed under separately continuous
  multiplication and continuous inversion, without separation or ambient
  Noetherian hypotheses; the additive analogue holds as well. See
  [`GroupTheory.Topology.Algebra.Group.LocallyClosed`](GroupTheory/Topology/Algebra/Group/LocallyClosed.lean).

- **[Cofinite groups and actions](GroupTheory/Topology/Algebra/Group/Cofinite.lean).**
  Inversion and fixed translations are continuous on every cofinite group;
  joint multiplication is continuous exactly when the group is finite. An action
  of a cofinite group on any cofinite space is jointly continuous exactly when
  the actor is finite or the action is pointwise trivial. These use the ordinary
  product topology, not the cofinite topology on the whole set of pairs.

- **[Coset actions and conjugacy](GroupTheory/GroupAction/Quotient.lean).**
  For arbitrary subgroups `H, K` of a group `G`, equivariant maps `G/H → G/K`
  exist exactly when `H ≤ gKg⁻¹` for some `g`; the coset actions are isomorphic
  exactly when `H, K` are conjugate. Maps both ways alone do not suffice.

- **[Coefficient-sum relations](GroupTheory/Finsupp/CoefficientSum.lean).**
  Over a semiring `R`, for an additive commutative group `M` with an `R`-module
  structure and a chosen `i₀ : ι`, the coefficient-sum kernel on `ι →₀ M` is
  the `R`-span of `single i m - single i₀ m`. Linear maps into additive
  commutative monoid modules factor uniquely through the sum exactly when their
  singleton components agree; neither finite indices nor cancellative targets
  are required.

- **[Group diagrams by arrow relations](GroupTheory/Category/Grp/Colimits.lean).**
  For any group-valued diagram, the free product of its object groups modulo the
  normal closure of all arrow-identification relators has the diagram's universal
  property into every monoid in an independent universe. No smallness, finiteness
  or commutativity is assumed. Its generator maps satisfy every arrow, generate
  the quotient, and determine every outgoing homomorphism. Explicitly lifting
  each object to the carrier universe `max u v` gives a colimit cocone and the
  leg-preserving comparison with any other colimit in that universe; this does not
  assert that universe lift preserves arbitrary large group colimits. A
  [nonabelian example](GroupTheoryTest/Category/Grp/Colimits.lean) combines an
  identity arrow with an isolated component and detects noncommuting generators.

- **[Pushouts over a trivial group](GroupTheory/Category/Grp/Pushout.lean).**
  For a group homomorphism `f : A →* B` and a trivial group `T`, the pushout is
  `B / normalClosure (range f)`. In every such group pushout the `B`-leg is
  surjective with exactly that kernel, without injectivity or commutativity
  assumptions. The guide distinguishes the unbundled and `GrpCat` universes.

- **[Fixed vectors over semirings](GroupTheory/RepresentationInvariants.lean).**
  For monoid representations on additive commutative monoid modules over a
  semiring, intertwiners `f, g` with injective `f` and `Function.Exact f g` give
  exactness on fixed submodules, not arbitrary surjectivity. Fixed submodules also commute with
  [arbitrary products](GroupTheory/RepresentationPi.lean), including empty ones,
  and [algebraic direct sums](GroupTheory/RepresentationDirectSum.lean).

- **[Finite-group intertwining lifts](GroupTheory/RepresentationLifting.lean).** If the
  order of a finite group is a unit in a possibly noncommutative semiring, any ordinary
  linear lift of one intertwining map through another intertwining map can be replaced
  by an intertwining lift. The modules need only be additive commutative monoids; the map
  being lifted through need not be surjective, and the given linear lift need not
  intertwine. Averaging uses the
  [additive conjugation representation](GroupTheory/RepresentationLinHomAdd.lean).
- **[Finite-group crossed-map averaging](GroupTheory/CocycleAveraging.lean).**
  For a finite group `G` acting by additive automorphisms on an additive commutative
  group `A`, bijective multiplication by `Nat.card G` makes every crossed map
  principal: `z g = g • v - v`. The explicit witness is the negative inverse-order
  multiple of its sum. Its formula commutes with additive maps between groups with
  bijective multiplication by the same order; transporting cocycles additionally
  needs equivariance. See the [averaging API](GroupTheory/CocycleAveraging/README.md).
  For a module over any semiring, a unit-valued order suffices, with the
  negative inverse-unit scalar sum as witness. The additive group action need
  not be scalar-linear, and the scalar-form vector formula remains natural
  under arbitrary additive maps.
- **[Finite-index free-group ranks](GroupTheory/FreeGroup/Rank.lean).**
  For finite-index `H` in a finitely generated free group,
  `rank H + [G:H] = rank G * [G:H] + 1`, including ambient rank zero.
  Mathlib supplies subgroup freeness and finite generation. The
  [index-two guide](docs/Results.md#index-two-subgroups-and-explicit-generators)
  gives all three explicit generating triples in rank two, not triple freeness.

- **[Ultrafilter-limit homomorphisms](GroupTheory/Topology/Ultrafilter.lean).**
  For a compact Hausdorff monoid with continuous multiplication, limits along
  any fixed ultrafilter give a surjective abstract homomorphism from its power.
  If the ultrafilter contains all cofinite sets, all fibers are dense; for a
  nontrivial target it is not continuous at the constant identity family.
  The guide includes finite-group targets and the original `ℕ → ZMod 3` example.

- **[Finite-index openness and automatic continuity](GroupTheory/Topology/AutomaticContinuity.lean).**
  Every abstract finite-index subgroup of a compact Hausdorff commutative
  topological group with a dense algebraically finitely generated subgroup is
  open. Every abstract homomorphism from such a source into a compact
  nonarchimedean group is continuous; the target need not be Hausdorff or
  commutative, and the image may be infinite. This does not assert local constancy.

- **[Finite-coordinate homomorphism factorization](GroupTheory/Topology/Algebra/Group/PiDiscreteFactor.lean).**
  A continuous homomorphism from any dependent product of groups with given
  topologies into a discrete group factors continuously through quotients of
  finitely many coordinates by open normal subgroups. No continuity of source
  operations is required. The selected stage is finite if all factors are compact,
  but need not be finite otherwise.

- **[Finite-index identity components](GroupTheory/Topology/Algebra/Group/Subgroup.lean).**
  For a group with a topology and continuous fixed left translations, the identity
  component is an open subgroup of finite index when there are finitely many
  connected components. No local connectedness, separation, continuous inversion
  or normality assumption is needed. The additive version applies to the zero
  component.
- **[Compact open subgroups](GroupTheory/Topology/CompactOpenSubgroup.lean) and
  [identity-component quotients](GroupTheory/Topology/ConnectedComponentQuotient.lean).**
  Every locally compact totally disconnected topological group has a compact
  open subgroup basis, without a separate Hausdorff premise. Every topological
  group's ordinary quotient by its identity component is Hausdorff and totally
  disconnected, without separation or local compactness of the original group.

- **[Grothendieck extensions](GroupTheory/MonoidLocalization/GrothendieckGroup.lean).**
  Biadditive maps from two additive commutative monoids into an additive
  commutative group extend uniquely to both completions. A semiring's additive
  completion has a [canonical ring structure](GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean)
  and universal ring lifts, without cancellation. For an additive unit in any
  semiring, [nilpotence is reflected](GroupTheory/MonoidLocalization/GrothendieckGroup/Nilpotent.lean)
  by the canonical map to that ring; the scalar step is not a polynomial criterion.

- **[Torsion in additive quotients](GroupTheory/QuotientTorsion.lean).**
  For an additive commutative group `V`, any additive subgroup `L`, and any
  natural `n` whose multiplication map is bijective on `V`, `(V/L)[n] ≃+ L/nL`
  by `[x] ↦ [n • x]`. If `L` is finitely generated, the kernel is
  [finite of cardinality](GroupTheory/QuotientTorsion/Cardinality.lean)
  `n ^ Module.finrank ℤ L`; freeness and ambient finite generation are not needed.

- **Archimedean multiplicative boundedness** ([module](GroupTheory/Algebra/Order/Subsemigroup.lean);
  [statements and API](docs/Results.md#archimedean-multiplicative-boundedness)).
  For a commutative monoid equipped with a linear order and a chosen `0` with `0 ≤ 1`,
  assume multiplicative Archimedeanness and strictly monotone multiplication by positive
  elements. A multiplication-closed selected set is bounded above iff every member is
  at most `1`; the same criterion holds for the raw range of a multiplicative map from
  a type with only multiplication. Selected sets may be empty and need not contain `1`.

The guide also covers [finite-index descent and property transport](docs/Results.md#finite-index-openness-and-automatic-continuity),
[circle characters and other topology results](docs/Results.md#topological-refinements),
[conditional cyclic norms and scalar indices](docs/Results.md#abelian-arithmetic),
and the material hypotheses, formulas and examples behind these headlines.

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

Import the full library with:

```lean
import GroupTheory
```

## Use and verification

Detailed imports, applications, client boundaries and compatibility notes are in
the [usage guide](docs/Usage.md). All interfaces are available through
`import GroupTheory`; `GroupTheoryTest` is for repository verification, not
downstream imports.

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
| Finite kernels and fibers with weak homomorphism targets | [`MonoidHom.Finite`](GroupTheory/MonoidHom/Finite.lean) |
| Coinduced cofinite topologies and finite-versus-infinite fibers | [`Topology.Cofinite`](GroupTheory/Topology/Cofinite.lean), [paired integer projections](GroupTheoryTest/Topology/Cofinite.lean) |
| Cofinite group operations and actions, coset quotients and homomorphisms | [`Group.Cofinite`](GroupTheory/Topology/Algebra/Group/Cofinite.lean) |
| Coefficient-sum kernels and factorization over semirings | [`Finsupp.CoefficientSum`](GroupTheory/Finsupp/CoefficientSum.lean), [noncancellative-target client](GroupTheoryTest/Finsupp/CoefficientSum.lean) |
| Group pushouts and normal-closure quotients | [`Category.Grp.Pushout`](GroupTheory/Category/Grp/Pushout.lean) |
| Group-diagram free-product presentations | [`Category.Grp.Colimits`](GroupTheory/Category/Grp/Colimits.lean) |
| Dense unit maps for unit-reflecting monoid homomorphisms | [`Topology.Algebra.Group.Units`](GroupTheory/Topology/Algebra/Group/Units.lean), [rational and integer-quotient examples](GroupTheoryTest/Topology/Algebra/Group/Units.lean) |
| Products of submodules and their coordinate splitting | [`LinearAlgebra.Prod`](GroupTheory/LinearAlgebra/Prod.lean), [`LinearAlgebra.Pi`](GroupTheory/LinearAlgebra/Pi.lean) |
| Fixed vectors, products, direct sums and left exactness over semirings | [`RepresentationInvariants`](GroupTheory/RepresentationInvariants.lean), [`RepresentationPi`](GroupTheory/RepresentationPi.lean), [`RepresentationDirectSum`](GroupTheory/RepresentationDirectSum.lean) |
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
| Finite free bases and finite-index free-group ranks | [`FreeGroup.Rank`](GroupTheory/FreeGroup/Rank.lean) |
| Index-two subgroups, characters and explicit generators | [`Subgroup.IndexTwo`](GroupTheory/Subgroup/IndexTwo.lean), [`FreeGroup.IndexTwo`](GroupTheory/FreeGroup/IndexTwo.lean) |
| Orbit inseparability for actions of preirreducible groups | [`MulAction.Irreducible`](GroupTheory/Topology/Algebra/MulAction/Irreducible.lean) |
| Locally closed subgroups under separate continuity | [`Group.LocallyClosed`](GroupTheory/Topology/Algebra/Group/LocallyClosed.lean), [additive intersection client](GroupTheoryTest/Topology/Algebra/Group/LocallyClosed.lean) |
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

## Credits and license

The cofinite quotient results use Mathlib's coset, quotient-topology, finite-set and
cofinite-topology APIs, together with the dense-fiber formalization in
[`Topology.DenseFibers`](GroupTheory/Topology/DenseFibers.lean).

Authors: Formal Frontier Agents. The Lean proofs and clients were developed by
Formal Frontier AI agents. Licensed under [Apache-2.0](LICENSE).
