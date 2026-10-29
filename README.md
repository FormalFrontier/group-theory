# Group Theory

Reusable Lean results on identity-component quotients of topological groups,
compact open subgroups of totally disconnected locally compact groups,
open kernels and finite images of continuous group homomorphisms,
compact-open discreteness and finite-quotient factorization of discrete-valued maps,
finite-coordinate quotient factorization on arbitrary powers of compact groups,
structured finite-coordinate factorization of continuous group homomorphisms,
finite-image and open-kernel rational-circle character subgroups,
the rational-circle inclusion and comparison with continuous circle characters,
open finite-index subgroups of compact commutative groups with dense finite generation,
continuous compatible sections of monoid diagrams, open quotients of compact
totally disconnected spaces, finite cyclic norms and natural scalar maps of
finitely generated abelian groups, kernels of induced quotient maps, torsion in
additive quotients, additive and biadditive Grothendieck extensions, ring structures
and multiplicative universal properties on additive Grothendieck groups of semirings,
canonical coset-action isomorphisms, product-coset orbits and double cosets,
invariant equivalence relations, and automorphism groups of group actions.
The library depends directly on mathlib, not on a source repository or the
incubator. The mathematical guides explain the proof ideas, examples and limits
in more detail.

## Headline results

- **Circle equivalences and codomain transport.** `AddCircle.continuousAddEquivCircle`
  identifies every nonzero-period additive circle with `Additive Circle`, using the
  exponential `x ↦ exp (2 * π / T * x)`. Codomain transport gives homeomorphisms of
  continuous homomorphism spaces for monoids with arbitrary topologies, and continuous
  multiplicative equivalences for commutative codomains with continuous multiplication.
  The period-one specialization transports continuous additive characters pointwise.

These results are available in the library. The [result guide](docs/Results.md)
gives detailed statements, examples and API qualifications, including the
constructions and prior results reused from Mathlib.

### Actions, cosets and fixed vectors

- **[Coset maps and conjugacy](GroupTheory/GroupAction/Quotient.lean).** For any group and arbitrary subgroups
  `H, K`, equivariant maps `G/H → G/K` exist exactly when `H ≤ gKg⁻¹` for some
  `g`. The coset actions are isomorphic exactly when the subgroups are conjugate;
  maps both ways alone are not enough.
  For any `G`-set `X`, equivariant maps `G/H → X` correspond to `H`-fixed
  points as a plain equivalence, not as a `G`-stable fixed subaction.
  Diagonal orbits on `G/H × G/K`, and restricted `H`-orbits on `G/K`, are
  described by [double-coset classes](GroupTheory/GroupAction/DoubleCoset.lean),
  without selecting representatives.
  For a pretransitive action with a chosen point, invariant equivalence
  relations correspond to overgroups of its stabilizer; see the
  [invariant-setoid API](GroupTheory/GroupAction/InvariantSetoid.lean).
- **[Action automorphisms](GroupTheory/GroupAction/Centralizer.lean).** For an action of a group in any category, its
  automorphisms identify with a centralizer. For a transitive `G`-set with
  chosen `x`, the [normalizer quotient](GroupTheory/GroupAction/Automorphism.lean)
  `N_G(G_x)/G_x` identifies with the automorphism group. Under ordinary composition,
  `[n]` sends `g • x` to `(g * n⁻¹) • x`: the inverse parameter matters.
- **[Left exactness of fixed vectors](GroupTheory/RepresentationInvariants.lean).** For monoid representations on modules
  over a semiring, additive commutative monoids suffice. Intertwining maps
  `f, g` with injective `f` and `Function.Exact f g` give injectivity and
  exactness on fixed submodules, not preservation of surjectivity without further
  hypotheses.
- **Products of fixed submodules.** For monoid representations over a semiring on
  their given additive commutative monoid modules, fixed vectors commute with both
  [binary products](GroupTheory/RepresentationInvariants.lean) and
  [arbitrary indexed products](GroupTheory/RepresentationPi.lean), including infinite
  and empty index types. The canonical linear equivalences preserve ambient coordinates
  and are natural in supplied intertwining maps. They reuse generic submodule
  splittings for [pairs](GroupTheory/LinearAlgebra/Prod.lean) and
  [indexed families](GroupTheory/LinearAlgebra/Pi.lean); no group or additive-inverse
  assumptions are needed.
- **[Norms and fixed-vector surjections](GroupTheory/RepresentationNorm.lean).** For finite-group
  representations over a semiring on additive commutative monoids, a surjective
  intertwining map is surjective on fixed submodules if every fixed target vector
  is a value of the target norm. It suffices that multiplication by the group order
  is surjective on the target fixed submodule, or bijective on the ambient target.
  No divisibility or cancellation in the source is required. The
  [norm naturality API](GroupTheory/RepresentationNormNaturality.lean) allows the
  two coefficient carriers to lie in independent universes.
- **[Free-group ranks](GroupTheory/FreeGroup/Rank.lean).** For finite-index `H` in a finitely generated free
  group, `rank H + [G:H] = rank G * [G:H] + 1`, including ambient rank zero.
  Mathlib supplies subgroup freeness and finite generation.

[Detailed action results](docs/Results.md#actions-cosets-and-fixed-vectors)
also include right transversals, subgroup towers and nested coset maps.

### Topological refinements

- **[Discrete actions](GroupTheory/Topology/Algebra/MulAction.lean) and subgroup quotients.** Assume continuous fixed
  **left** translations in a group with a topology. For an action on a
  discrete space, orbit-map continuity is equivalent to an open stabilizer;
  joint action continuity is equivalent to all stabilizers being open.
  For arbitrary `H`, the [canonical quotient](GroupTheory/Topology/Algebra/Group/Quotient.lean)
  `G/H` is discrete iff `H` is open, and
  T1 iff `H` is closed; open subgroups are clopen. Finite index makes closed
  imply open; compactness of `G` makes open imply finite index.
- **[Continuous coset maps](GroupTheory/Topology/Algebra/Group/Quotient.lean).** With continuous **right** translations in `G`
  and a jointly continuous action on `X`, evaluation at `[1]` identifies
  continuous equivariant maps `G/H → X` homeomorphically with the `H`-fixed
  subspace. The map-space topology is induced from compact-open continuous
  maps, and `H` is arbitrary.
- **[Dense unit maps](GroupTheory/Topology/Algebra/Group/Units.lean).** A dense monoid homomorphism that reflects units induces
  a dense map on unit groups when the target's unit coercion is an open
  embedding. No continuity of the homomorphism or source topology is needed.
- **[Subgroup bases](GroupTheory/Topology/Algebra/Group/TotalBounded.lean).** In a left-uniform group with an identity-neighborhood
  basis of subgroups, total boundedness is equivalent to finite index of
  every predicate-qualified basis member, without completeness or separation.
  Every locally compact totally disconnected topological group has a basis
  of [compact open subgroups](GroupTheory/Topology/CompactOpenSubgroup.lean),
  without a separate Hausdorff premise.
- **[Component quotients](GroupTheory/Topology/ConnectedComponentQuotient.lean).** Every topological group's ordinary quotient by
  its identity component is Hausdorff and totally disconnected, without a
  separation or local-compactness premise on the original group.

[Detailed topology results](docs/Results.md#topological-refinements) also cover
open kernels, characters, discrete-valued maps, finite-coordinate factorizations
and compatible sections, with their individual hypotheses.

### Grothendieck extensions

Biadditive maps from two additive commutative monoids into an additive
commutative group extend uniquely to their
[Grothendieck completions](GroupTheory/MonoidLocalization/GrothendieckGroup.lean).
Completion commutes canonically with arbitrary dependent products of additive
commutative monoids, including infinite and empty index types. The equivalence
preserves all tuple units, has induced evaluations as its coordinates and is
natural in families of additive homomorphisms. The completed product map is
bijective exactly when every completed coordinate map is bijective; no cancellation
or nontriviality is assumed. A semiring's additive completion carries a
[canonical ring](GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean),
commutative for commutative input;
homomorphisms from the semiring into any ring extend uniquely as ring
homomorphisms. No cancellation, nontriviality or commutative-target assumption
is needed. The additive lift equivalence packages Mathlib's existing universal
property. [Detailed extension results](docs/Results.md#grothendieck-extensions).

### Abelian arithmetic

- **[Conditional cyclic norm exactness](GroupTheory/CyclicNorm.lean).** For an endomorphism `sigma` of an
  additive commutative group and `m > 0` with `sigma ^ m = 1`, the norm kernel
  equals `range (1 - sigma)` if multiplication by that same `m` is injective
  and fixed classes modulo `mA` have fixed lifts: whenever
  `sigma a - a ∈ mA`, some fixed `z` satisfies `a - z ∈ mA`.
- **[Scalar maps](GroupTheory/FGScalarSurjectivity.lean) and indices.** For a finitely generated abelian group `A` and
  natural `n ≥ 2`, surjectivity of `n • ·` is equivalent to finiteness and
  coprimality of `n` with the group order. A single integer scalar gives its
  inverse. The separate [index formula](GroupTheory/IndexNSmul.lean) is
  `[A : nA] = n ^ Module.finrank ℤ A * Nat.card (ker [n])` for every natural
  scalar, with index and `Nat.card` zero for infinite quotients and kernels.
- **[Quotient kernels](GroupTheory/QuotientGroup/Kernel.lean) and torsion.** For normal `N ≤ G`, `M ≤ H` and an ambient
  equivalence `f : G ≃* H` with `f(N) ≤ M`, the kernel of `G/N → H/M` is
  identified with `M/f(N)`; these groups need not be commutative. For any
  natural `n`, if `n • ·` is bijective on an additive commutative `V`, the
  [`n`-torsion of `V/L`](GroupTheory/QuotientTorsion.lean), for arbitrary additive
  subgroup `L`, is `L/nL` by the positive-sign map `[x] ↦ [n • x]`.
  If `L` is finitely generated, that kernel is finite with
  [natural cardinality](GroupTheory/QuotientTorsion/Cardinality.lean)
  `n ^ Module.finrank ℤ L`; freeness and ambient finite generation are not
  needed. All natural scalars are included; at zero the premise forces `V`
  trivial.

[Detailed arithmetic results](docs/Results.md#abelian-arithmetic) retain the
representative formulas, scalar-transition naturality and zero-scalar boundaries.

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
or the incubator use the GitHub URL and full published release commit, not moving
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
and [`lake-manifest.json`](lake-manifest.json) record the Lean version and
resolved mathlib dependency. Run from this repository:

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
| Dense unit maps for unit-reflecting monoid homomorphisms | [`Topology.Algebra.Group.Units`](GroupTheory/Topology/Algebra/Group/Units.lean), [rational and integer-quotient examples](GroupTheoryTest/Topology/Algebra/Group/Units.lean) |
| Products of submodules and their coordinate splitting | [`LinearAlgebra.Prod`](GroupTheory/LinearAlgebra/Prod.lean), [`LinearAlgebra.Pi`](GroupTheory/LinearAlgebra/Pi.lean) |
| Fixed vectors, products and left exactness over semirings | [`RepresentationInvariants`](GroupTheory/RepresentationInvariants.lean), [`RepresentationPi`](GroupTheory/RepresentationPi.lean) |
| Finite-group norms and surjections on fixed submodules | [`RepresentationNorm`](GroupTheory/RepresentationNorm.lean), [`RepresentationNormNaturality`](GroupTheory/RepresentationNormNaturality.lean) |
| Additive universal property, biadditive Grothendieck extensions and arbitrary products | [`MonoidLocalization.GrothendieckGroup`](GroupTheory/MonoidLocalization/GrothendieckGroup.lean) |
| Ring structures, canonical generators and multiplicative universal properties for additive Grothendieck groups of semirings | [`MonoidLocalization.GrothendieckGroup.Ring`](GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean) |
| Equivariant maps from cosets and subgroup-fixed points | [`GroupAction.Quotient`](GroupTheory/GroupAction/Quotient.lean), [permutation-action and boundary examples](GroupTheoryTest/CosetActionHom.lean) |
| Canonical coset-action isomorphisms and subgroup conjugacy | [`GroupAction.Quotient`](GroupTheory/GroupAction/Quotient.lean), [nonnormal examples](GroupTheoryTest/Topology/Algebra/Group/Quotient.lean) |
| Product-coset orbits and double cosets | [`GroupAction.DoubleCoset`](GroupTheory/GroupAction/DoubleCoset.lean), [permutation and boundary examples](GroupTheoryTest/Topology/Algebra/Group/Quotient.lean) |
| Equivariant maps between nested coset spaces | [`GroupAction.QuotientMap`](GroupTheory/GroupAction/QuotientMap.lean) |
| Invariant equivalence relations and overgroups of point stabilizers | [`GroupAction.InvariantSetoid`](GroupTheory/GroupAction/InvariantSetoid.lean), [nonnormal model](GroupTheoryTest/GroupAction/InvariantSetoid.lean) |
| Action automorphisms, centralizers and normal stabilizers | [`Centralizer`](GroupTheory/GroupAction/Centralizer.lean) |
| Transitive-action automorphisms and normalizer quotients | [`Automorphism`](GroupTheory/GroupAction/Automorphism.lean) |
| Finite free bases and finite-index free-group ranks | [`FreeGroup.Rank`](GroupTheory/FreeGroup/Rank.lean) |
| Index-two subgroups, characters and explicit generators | [`Subgroup.IndexTwo`](GroupTheory/Subgroup/IndexTwo.lean), [`FreeGroup.IndexTwo`](GroupTheory/FreeGroup/IndexTwo.lean) |
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

Authors: Formal Frontier Agents. The Lean proofs and clients were developed by
Formal Frontier AI agents. Licensed under [Apache-2.0](LICENSE).
