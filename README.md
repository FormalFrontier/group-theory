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
and automorphism groups of group actions.
The library depends directly on mathlib, not on a source repository or the
incubator. The mathematical guides explain the proof ideas, examples and limits
in more detail.

## Headline results

**Dense maps on units.** For monoids `M` and `N`,
[`DenseRange.units_map`](GroupTheory/Topology/Algebra/Group/Units.lean) shows that
a dense homomorphism `f : M →* N` which reflects units induces a dense map on unit
groups if the canonical coercion `Nˣ → N` is an open embedding. Only `N` needs a
topology; no continuity assumption on `f` is imposed. The
[examples](GroupTheoryTest/Topology/Algebra/Group/Units.lean) verify the hypotheses
for the rational inclusion into the reals and use the integer quotient modulo five
to demonstrate why unit reflection cannot be omitted.

**Left exactness of fixed vectors.** For a monoid `G` and modules over any semiring
`R`, [`RepresentationInvariants`](GroupTheory/RepresentationInvariants.lean) provides
the fixed submodule and the restriction `f.fixedSubmoduleMap` of an intertwining map.
The modules need only be additive commutative monoids, and all carrier universes are
independent. `fixedSubmoduleMap_injective` preserves ambient injectivity. If `f` is
injective and `Function.Exact f g`, then `fixedSubmoduleMap_exact` proves
`Function.Exact f.fixedSubmoduleMap g.fixedSubmoduleMap` on the original module and
representation data. No finiteness, topology, group structure on `G` or additive
inverses are required. The identity, composition, inclusion and unique-factorization
APIs are compatible with the usual submodule maps. When `R` is a commutative ring,
`G` is a group and the module is an additive commutative group, the fixed submodule
equals Mathlib's existing invariant submodule.
The module explains a nontrivial split sequence for the coordinate-swap action on `ℕ²`
and why the sign action on `ℤ`, reduced modulo two, does not preserve surjectivity.

**Right transversals and subgroup towers.**
[`GroupTheory.Transversal`](GroupTheory/Transversal.lean) provides subgroup factors,
representative permutations, changes of representatives, and inner-times-outer
product transversals for arbitrary nested subgroups, without finiteness assumptions.
It generalizes the pure Continuous Group Cohomology formalization
and reuses Mathlib’s complement and subgroup-image API.

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
[Grothendieck lift API](GroupTheory/MonoidLocalization/GrothendieckGroup.lean)
and its [integer-valued clients](GroupTheoryTest/GrothendieckGroup.lean).

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
[ring API](GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean) and the
[signed-natural and one-element clients](GroupTheoryTest/GrothendieckGroup.lean).

**Action automorphisms as centralizers.** For a group `G` and an action `A`
on an object of any category `C`, `Action.autEquivCentralizer` constructs
`Aut A ≃* Subgroup.centralizer (Set.range A.ρAut)`. The group, object and
morphism universes are independent. The forward map is exactly the forgotten
isomorphism; its inverse equips a commuting isomorphism with equivariance.
For `[Group G] [MulAction G X]`, `Action.autEquivPermCentralizer G X`
specializes this to the centralizer of `MulAction.toPermHom G X` in `Equiv.Perm X`,
reusing Mathlib's `CategoryTheory.Aut.mulEquivPerm`. Multiplication is ordinary
composition `α (β x)` on both sides. No finite, transitive, faithful, nonempty
or topological hypothesis is needed. For a pretransitive `G`-action and `x : X`,
`MulAction.isPretransitive_centralizer_iff_stabilizer_normal` characterizes
pretransitivity of this canonical image centralizer by normality of the point
stabilizer. The general helper
`MulAction.stabilizer_normal_of_pretransitive_commuting` only needs a commuting
pretransitive scalar operation `SMul H X`, with no monoid structure on `H` or
pretransitivity of `G`. These are general group-action facts, not freeness criteria.
See the [centralizer API](GroupTheory/GroupAction/Centralizer.lean), its
[noncommuting three-point and empty-set clients](GroupTheoryTest/ActionCentralizer.lean),
and the [normal-stabilizer clients](GroupTheoryTest/GroupAction/CentralizerTransitivity.lean).

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
parameter. See the [action API](GroupTheory/GroupAction/Automorphism.lean)
and its [noncommutative and nonnormal clients](GroupTheoryTest/GroupAction/Automorphism.lean).

**Finite free bases and finite-index subgroups.** The
[free-group rank module](GroupTheory/FreeGroup/Rank.lean) proves that every free
basis of a finitely generated group has a finite indexing type of cardinality
`Group.rank G`. For every finite-index subgroup `H` of a finitely generated free
group, it proves `Group.rank H + H.index = Group.rank G * H.index + 1`, including
ambient rank zero and without normality or a separate finite-generation
hypothesis on `H`. Mathlib supplies subgroup freeness and finite generation.
The [parity-kernel client](GroupTheoryTest/FreeGroup/Rank.lean) constructs an
index-two subgroup of `FreeGroup (Fin 2)`, computes its rank as three and uses
the existing basis-reindexing API to give a basis indexed by `Fin 3`.

**Fixed-action continuity.**

- `Topology.IsCoinducing.continuousConstSMul` transports continuity of fixed
  scalar actions from `X` to `Y` along an equivariant coinducing map
  `f : X →[M] Y`, assuming `ContinuousConstSMul M X`, with topologies on
  `X` and `Y` and primitive actions of `M` on both. Scalar, source and target
  universes are independent; no scalar topology, action laws or surjectivity
  is required. `Topology.IsCoinducing.continuousConstVAdd` gives the
  corresponding transport from `X` to `Y` for fixed vector additions,
  assuming `ContinuousConstVAdd M X`. See
  [the transport API](GroupTheory/Topology/Algebra/ConstMulAction.lean).
- `QuotientGroup.continuousConstSMul` supplies continuous fixed left actions on
  the canonical coinduced left-coset quotient `G ⧸ H` for every subgroup `H`,
  assuming only `Group G`, `TopologicalSpace G` and `ContinuousConstSMul G G`.
  No normality, right continuity, joint multiplication, continuous inversion,
  separation, compactness or index assumption is required. The additive instance
  is `QuotientAddGroup.continuousConstVAdd`. See
  [the coset quotient API](GroupTheory/Topology/Algebra/Group/Quotient.lean).

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
[the subgroup and quotient API](GroupTheory/Topology/Algebra/Group/Quotient.lean)
and [the clients](GroupTheoryTest/Topology/Algebra/Group/Quotient.lean). The clients
supply open and closed singleton fibers, finite coset types and same-object
agreement with Mathlib's stronger separately continuous API. Every observer
`G ⧸ H → Y`, for any space `Y`, is continuous when `H` is closed and of finite
index; no compactness or explicit openness premise is needed.
See the [left-versus-both-sided boundary examples](docs/Results.md).

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
[total-boundedness criterion](GroupTheory/Topology/Algebra/Group/TotalBounded.lean)
and its [applications](GroupTheoryTest/Topology/FiniteIndex.lean): in the 3-adic
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
See [the subgroup API](GroupTheory/Topology/CompactOpenSubgroup.lean)
and [the boundary clients](GroupTheoryTest/Topology/CompactOpenSubgroup.lean).

**Identity-component quotients.** For any topological group, the ordinary
quotient by Mathlib's `Subgroup.connectedComponentOfOne` is Hausdorff and totally
disconnected, without a separation or local-compactness hypothesis on the
original group. `QuotientGroup.connectedComponentQuotientMk` is the canonical
continuous projection. `QuotientGroup.connectedComponentQuotientLift` factors
continuous homomorphisms into totally disconnected groups, with application,
composition, uniqueness and hom-equivalence APIs. The target group's
operations need not be continuous. See
[the quotient API](GroupTheory/Topology/ConnectedComponentQuotient.lean)
and [boundary examples](GroupTheoryTest/Topology/ConnectedComponentQuotient.lean).

**Finite cyclic norm exactness.**
[`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range`](GroupTheory/CyclicNorm.lean)
identifies `ker (∑ i ∈ Finset.range m, sigma ^ i)` with `range (1 - sigma)`
for an endomorphism `sigma` of any additive commutative group `A`. It requires
`m : ℕ` with `0 < m` and `sigma ^ m = 1` (not necessarily *exact* order `m`),
injectivity of multiplication by that **same** `m`, and an elementwise fixed
lift: if `sigma a - a ∈ m • A`, some `sigma`-fixed `z` satisfies
`a - z ∈ m • A`. This is useful when fixed classes modulo `m • A` have
fixed representatives even though multiplication by `m` is not surjective.
It does not assume divisibility or a global fixed-lift section, and does not
assert an unconditional Tate/cohomology theorem or source coverage. See the
[cyclic norm guide](GroupTheory/CyclicNorm/README.md) and its
[client examples and counterexamples](GroupTheoryTest/CyclicNorm.lean).

**Surjective natural scalars on FG abelian groups.** For `[AddCommGroup A]`,
`[AddGroup.FG A]` and `n : ℕ` with `2 ≤ n`, surjectivity of the
map `fun x : A => n • x` forces `Finite A` and
`Nat.Coprime n (Nat.card A)`. A *single* integer scalar is a two-sided
inverse for `n • ·` on every element; the finite-and-coprime condition
characterizes both surjectivity and bijectivity of that map. The four APIs in
[`GroupTheory.FGScalarSurjectivity`](GroupTheory/FGScalarSurjectivity.lean) are
`AddCommGroup.exists_zsmul_inverse_of_nsmul_surjective`,
`AddCommGroup.finite_coprime_of_nsmul_surjective`,
`AddCommGroup.nsmul_surjective_iff_finite_coprime` and
`AddCommGroup.nsmul_bijective_iff_finite_coprime`. These statements do not
apply to arbitrary surjective endomorphisms and do not formalize K-theory.
See the [FG scalar guide](GroupTheory/FGScalarSurjectivity/README.md) and its
[client examples](GroupTheoryTest/FGScalarSurjectivity.lean).

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
[quotient-kernel API](GroupTheory/QuotientGroup/Kernel.lean) and the
[independent rational-plane diagonal model](GroupTheoryTest/QuotientKernel.lean).

**Torsion in additive quotients.** If multiplication by `n : ℕ` is bijective
on an additive commutative group `V`, then
`QuotientAddGroup.nsmulTorsionEquivQuotient` identifies the `n`-torsion subgroup
of `V / L` with `L / nL` for any additive subgroup `L`. It uses the ordinary
kernel and range-quotient carriers. A class represented by `x`, with `n • x ∈ L`,
maps to `[n • x]`; the inverse is given by unique `n`-division in `V`.
No topology, lattice, finite-rank or divisibility-at-other-scalars assumption is needed.
This is the scalar specialization of the quotient-kernel comparison, with an
explicit equality identifying the two constructions after the canonical transports.
See the [equivalence and representative API](GroupTheory/QuotientTorsion.lean)
and the [rational half- and quarter-classes and unit-scalar boundaries](GroupTheoryTest/QuotientTorsion.lean).
The scalar-transition statement identifies multiplication by `d` from
`(m * d)`-torsion to `m`-torsion with reduction
`L / (m * d)L → L / mL`, assuming only ambient bijectivity at `m * d`.
This is a specialization of the quotient-kernel naturality square.

**Scalar indices on FG abelian groups.** For `[AddCommGroup A]` and
`[AddGroup.FG A]`, the [scalar-index module](GroupTheory/IndexNSmul.lean) states
`(nsmulAddMonoidHom (α := A) n).range.index =
n ^ Module.finrank ℤ A * Nat.card ((nsmulAddMonoidHom (α := A) n).ker)`
for every `n : ℕ`. Injectivity at this scalar removes the kernel factor, without
a global freeness assumption. For `[Module.Free ℤ A] [Module.Finite ℤ A]`,
a comparison collapses the right-hand side to Mathlib's existing free index
formula, including at zero. Index and `Nat.card` vanish for infinite quotients
and kernels; no all-scalar quotient finiteness is asserted.
See the [mixed free/torsion examples](GroupTheoryTest/IndexNSmul.lean).

**Finite torsion in additive quotients.** If `L : AddSubgroup V` is finitely
generated and multiplication by `n : ℕ` is bijective on the additive commutative
group `V`, then `QuotientAddGroup.finite_ker_nsmul_quotient` makes the `n`-torsion
kernel of `V / L` finite, and `QuotientAddGroup.natCard_ker_nsmul_quotient`
computes its natural cardinality as `n ^ Module.finrank ℤ L`. The subgroup need
not be free, and neither `V` nor `V / L` needs to be finitely generated.
Only bijectivity at this scalar is assumed. All natural scalars are included;
at zero the hypothesis forces `V` trivial, giving `0 ^ 0 = 1`.
See the [cardinality extension](GroupTheory/QuotientTorsion/Cardinality.lean)
and the [independent rational half-class count and boundary models](GroupTheoryTest/QuotientTorsion.lean).

[All results and their hypotheses](docs/Results.md), including open kernels,
characters, discrete-target and finite-coordinate factorizations, identity
components and compatible sections.

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
| Fixed vectors and left exactness over semirings | [`RepresentationInvariants`](GroupTheory/RepresentationInvariants.lean) |
| Additive universal property and biadditive Grothendieck extensions | [`MonoidLocalization.GrothendieckGroup`](GroupTheory/MonoidLocalization/GrothendieckGroup.lean) |
| Ring structures, canonical generators and multiplicative universal properties for additive Grothendieck groups of semirings | [`MonoidLocalization.GrothendieckGroup.Ring`](GroupTheory/MonoidLocalization/GrothendieckGroup/Ring.lean) |
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

- The fixed-vector construction generalizes Mathlib's `Representation.invariants`,
  formalized by Antoine Labelle, and reuses its intertwining-map API by Stepan Nesterov
  and Edison Xie and its `LinearMap.codRestrict` API in a file by Mario Carneiro.
  Left exactness uses `LinearMap.exact_iff` from Mathlib's exactness API by Antoine
  Chambert-Loir, together with its kernel and range membership APIs.

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, discussion
  of automorphisms of `G`-sets, motivates the centralizer identification for
  permutation actions. The categorical theorem generalizes this setting;
  it is not attributed to May as a statement for arbitrary categories.
  The construction reuses Mathlib's bundled `Action`, `ρAut`, `mkIso`,
  forgetful `mapAut`, and stock `CategoryTheory.Aut.mulEquivPerm`, together
  with its subgroup equivalence transports.

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, §4,
  first lemma, p. 24, for the transitive-action normalizer quotient.
  The parameterization uses inverse right translation for ordinary composition.
  Mathlib's bundled action automorphisms, right normalizer action on cosets,
  coset-to-orbit map and finite-normal endomorphism construction provide the
  existing interfaces; no replacement equivariant-permutation structure is used.

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 4, §5,
  first theorem, printed page 37, for the finite-index free-group rank formula.
  The free-group modules reuse Mathlib's free bases and Nielsen–Schreier theorem,
  formalized by David Wärn, Eric Wieser and Joachim Breitner, and its group rank
  and Schreier finite-generation API, formalized by Thomas Browning.
- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 4, Problem 1,
  p. 38, for the two-generator free-group application. The character construction
  uses Mathlib's quotient-group and prime-cardinality equivalences; the explicit
  spanning argument uses its Schreier generators for a right transversal.
- J. S. Milne, *Abelian Varieties*, version 2.0 (2008), I.10, Remark 10.7,
  for the complex-torus torsion application. The quotient-kernel comparison uses
  Mathlib's first isomorphism theorem, kernel/range identities and subgroup/quotient
  equivalence transports. Joël Riou's Snake-lemma formalization supplied the
  scalar comparison's original homological proof and positive-sign equation.
- Van Dantzig's compact-open subgroup theorem, used in Neukirch, Schmidt,
  and Wingberg, *Cohomology of Number Fields*, corrected second edition,
  Chapter I, §1, Proposition (1.1.9), for the identity-component discussion.
- Mathlib's `OpenSubgroup` and `MulAction.stabilizer` supply the algebraic interface;
  its compact-neighborhood and clopen-basis results supply the topological inputs.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, electronic version 2.3, Chapter I, §1, (1.1.9)(i) and its
  preceding paragraph. The continuous universal property here is an
  interpretation that does not require the source's local compactness assumption.
- Mathlib's `Subgroup.connectedComponentOfOne`, `QuotientGroup.lift` and
  closed-normal quotient topology supply the component and quotient APIs.
- Mathlib's clopen basis for compact Hausdorff totally disconnected spaces
  and open-quotient basis transport supply the generic open-quotient proof.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1, remarks following Theorem (1.1.11), motivate
  the compact totally disconnected character case; the open-kernel API applies
  more generally. Mathlib's `NonarchimedeanGroup`, locally constant functions
  and quotient-group interfaces supply the reusable proof ingredients.

- Formal Frontier Agents, *Continuous Group Cohomology*, compact/discrete
  continuous-map discreteness and compact-group factorization formalizations.
  The proofs use Mathlib's compact-open subbasic sets, compactness of fibers,
  clopen identity neighborhoods and continuous quotient elimination.
- Mathlib's canonical arbitrary-subgroup left-coset quotient and coinduced topology,
  `eq_class_eq_leftCoset`, `preimage_mk_one`, `IsOpen.smul`, `IsClosed.smul`,
  finite-T1 discreteness, compact-discrete finiteness and the finite-index API
  supply the subgroup arguments. The statements generalize the hypotheses of
  `QuotientGroup.discreteTopology_iff`, `QuotientGroup.t1Space_iff`,
  `Subgroup.quotient_finite_of_isOpen`, `Subgroup.isClosed_of_isOpen` and
  `Subgroup.isOpen_of_isClosed_of_finiteIndex`. No new quotient or action
  construction is introduced, and no external source text or source-coverage
  claim is made for them.
- Mathlib's Grothendieck completion and universal-property formalization by
  Alex J. Best and Yaël Dillies supplies the carrier, additive group, generator
  and additive lift. The ring structures and multiplicative lifts compose the
  biadditive extension and generator-extensionality APIs with Mathlib's bundled
  multiplication in `Mathlib.Algebra.Ring.Basic`, by
  Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov and
  Neil Strickland.
- Mathlib's finite-supported product neighborhoods, finite intersections of
  open subgroups and products of open quotient maps supply the finite-coordinate
  extension. The cylinder argument uses Monica Omar's product-membership API,
  in particular `Submonoid.pi_mem_of_mulSingle_mem_aux`.

**Credit and license.** Formal Frontier AI agents developed the Lean proofs and
clients. The continuous sections API builds on Mathlib's sections definitions.
The compact-open subgroup result is the classical van Dantzig theorem, used as
a prerequisite in Neukirch, Schmidt, and Wingberg's *Cohomology of Number
Fields*, Chapter I, §1. Its translation-stabilizer argument independently
assembles Mathlib's compact-neighborhood, clopen-basis and subgroup APIs;
no Pontryagin or Bourbaki passage was inspected or transcribed.
The generic open-quotient proof was first formalized in Formal Frontier's
Profinite Groups library and uses Mathlib's clopen and basis APIs.
The compact/discrete continuous-map and factorization proofs were first formalized
by Formal Frontier Agents in the Continuous Group Cohomology library; their
proofs and public declarations are preserved here, using Mathlib's compact-open
and clopen-neighborhood APIs.
The identity-component quotient API interprets Neukirch--Schmidt--Wingberg's
totally disconnected quotient and reuses Mathlib's component and quotient APIs.
The open-kernel and finite-image arguments generalize their character case
using Mathlib's nonarchimedean, locally constant and quotient APIs; this does
not assert a comparison with all abstract characters or source coverage.
The rational-circle inclusion and torsion-value lift follow the Formal Frontier
Supernatural Numbers formalization of circle-valued characters.
Prism supplied the FG scalar mathematical argument, with determinant-route
advice from Lattice. This work is credited to **Authors: Formal Frontier Agents**
and licensed under [Apache-2.0](LICENSE). Neither human review nor an external
source paper is claimed for the original cyclic norm and FG scalar proofs.
