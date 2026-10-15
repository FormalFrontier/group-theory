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
finitely generated abelian groups, and torsion in additive quotients.
The library depends directly on mathlib, not on a source repository or the
incubator. The mathematical guides explain the proof ideas, examples and limits
in more detail.

## Headline results

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

**Torsion in additive quotients.** If multiplication by `n : ℕ` is bijective
on an additive commutative group `V`, then
`QuotientAddGroup.nsmulTorsionEquivQuotient` identifies the `n`-torsion subgroup
of `V / L` with `L / nL` for any additive subgroup `L`. It uses the ordinary
kernel and range-quotient carriers. A class represented by `x`, with `n • x ∈ L`,
maps to `[n • x]`; the inverse is given by unique `n`-division in `V`.
No topology, lattice, finite-rank or divisibility-at-other-scalars assumption is needed.
See the [equivalence and representative API](GroupTheory/QuotientTorsion.lean)
and the [nonzero half-class in `ℚ / ℤ` and unit-scalar boundary](GroupTheoryTest/QuotientTorsion.lean).

[All results and their hypotheses](docs/Results.md), including open kernels,
characters, discrete-target and finite-coordinate factorizations, identity
components and compatible sections.

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
| Fixed-action continuity and subgroup quotients | [`ConstMulAction`](GroupTheory/Topology/Algebra/ConstMulAction.lean), [`Quotient`](GroupTheory/Topology/Algebra/Group/Quotient.lean) |
| Compact open subgroups, open kernels and circle characters | [`CompactOpenSubgroup`](GroupTheory/Topology/CompactOpenSubgroup.lean), [`OpenKernel`](GroupTheory/Topology/OpenKernel.lean), [`CircleCharacter`](GroupTheory/Topology/CircleCharacter.lean) |
| Character subgroups and rational-circle comparison | [`CharacterSubgroups`](GroupTheory/Topology/CharacterSubgroups.lean), [`RationalCircle`](GroupTheory/Topology/RationalCircle.lean), [`RationalCircleCharacter`](GroupTheory/Topology/RationalCircleCharacter.lean) |
| Finite index from dense finite generation | [`FiniteIndex`](GroupTheory/Topology/FiniteIndex.lean) |
| Discrete-valued maps and compact-group factorization | [`CompactDiscrete`](GroupTheory/Topology/ContinuousMap/CompactDiscrete.lean), [`DiscreteFactor`](GroupTheory/Topology/Algebra/CompactGroup/DiscreteFactor.lean) |
| Finite cylinders and coordinate factorizations | [`OpenSubgroup.Pi`](GroupTheory/Topology/Algebra/OpenSubgroup/Pi.lean), [`PiDiscreteFactor`](GroupTheory/Topology/Algebra/CompactGroup/PiDiscreteFactor.lean), [`Group.PiDiscreteFactor`](GroupTheory/Topology/Algebra/Group/PiDiscreteFactor.lean) |
| Identity components and quotients | [`ConnectedComponentOpenSubgroup`](GroupTheory/Topology/ConnectedComponentOpenSubgroup.lean), [`ConnectedComponentQuotient`](GroupTheory/Topology/ConnectedComponentQuotient.lean) |
| Open quotients and compatible sections | [`OpenQuotient`](GroupTheory/Topology/OpenQuotient.lean), [`Sections`](GroupTheory/Topology/Sections.lean) |
| Cyclic norms and scalar maps | [`CyclicNorm`](GroupTheory/CyclicNorm.lean), [`FGScalarSurjectivity`](GroupTheory/FGScalarSurjectivity.lean), [`QuotientTorsion`](GroupTheory/QuotientTorsion.lean) |

## References

- J. S. Milne, *Abelian Varieties*, version 2.0 (2008), I.10, Remark 10.7,
  for the complex-torus torsion application. The quotient-torsion equivalence
  specializes Mathlib's Snake lemma construction and representative equation,
  formalized by Joël Riou.
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
