# Group Theory

Reusable group, subgroup and endomorphism mathematics. The first module,
`GroupTheory.CyclicNorm`, gives a finite cyclic norm exactness criterion for an
endomorphism of any additive commutative group. It has no source-repository,
incubator or Tate-cohomology dependency: only mathlib and its pinned transitive
packages are required. See the [mathematical guide](GroupTheory/CyclicNorm/README.md)
for the exact hypotheses, applications and counterexamples.

## Headline results

The [cyclic norm theorem](GroupTheory/CyclicNorm.lean)
`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range` identifies the kernel of the
finite norm `∑ i ∈ Finset.range m, sigma ^ i` with the range of `1 - sigma`
for any additive commutative group `A` and endomorphism `sigma`. It assumes a
positive natural number `m`, `sigma ^ m = 1` (not necessarily exact order `m`),
injectivity of multiplication by `m` on `A`, and an elementwise fixed lift for
every fixed class modulo `m • A`: whenever `sigma a - a ∈ m • A`, some `z`
satisfies `sigma z = z` and `a - z ∈ m • A`. This gives a reusable exactness
criterion without divisibility, surjectivity of multiplication by `m`, a global
fixed-lift section or a Tate/cohomology API. The [guide](GroupTheory/CyclicNorm/README.md)
explains the proof, applications and failure examples; the latter are client
tests, not additional exported results.

## Imports and verification

Import `GroupTheory` or `GroupTheory.CyclicNorm` to use
`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range`. The separate
`GroupTheoryTest` root imports ordinary client examples and failure boundaries;
it is a maintained Lake target, not a prerequisite for downstream imports.
With the pinned Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, run from this directory:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build GroupTheory GroupTheoryTest
```

The cache fetch must succeed before any mathlib-dependent build. The existing
CI workflow builds both roots and audits actual transitive axioms, including
private declarations. On September 30, 2026, the unchanged mathematics and
build inputs at development commit `f7606ae41bae3a077708e7bbaf15e8b3e7f30783`
had independent mathematical/API and affected metadata reviews, and native CI
run 1382 (attempt 1) succeeded for both roots and the complete private-inclusive
standard-axiom audit. The responsible maintainer accepted and integrated that
commit into development `main` at 12:35:30 UTC. This dated evidence does not
review this subsequent release-readiness prose or establish its actual-head
check, official release or verified publication.

### Build-cost guidance

The original native run 1382 took **113 seconds elapsed**, from 12:23:32 to
12:25:25 UTC on September 30, 2026. That end-to-end observation includes
setup, a matching precompiled mathlib cache, the build and the axiom audit;
it is **not** an isolated local-build time, a clean-machine benchmark or a
prediction for another machine. Allow time and space for the pinned toolchain,
dependencies and cache before building; network and cache state affect the
elapsed time. Peak memory (RSS) and peak disk use were not measured, so no
numeric resource requirement is inferred. The bounded-thread command above
is a conservative way to limit build concurrency, not a measured memory bound.

## Contributors and license

Authors: Formal Frontier Agents. The original producer and client were written
by worker-b Hive Task `hive-request-a2edb13065c52b892d241b54b1b126a02ccb23b7`
(UID `dfeefd22-cf15-4911-90aa-e10d49b8424c`); the static transfer and
packaging are by worker-b Hive Task
`hive-request-19f643d063d7ee8b030ea4a16fadc2a6e94c0535`
(UID `5483d819-031d-4920-ae47-cd2a40feb9da`). The earlier documentation and
release-metadata update is by worker-b Hive Task
`hive-request-c217eb129452563cadee4cd7a804bd23651d9f65`
(UID `e5b2df87-c7be-4336-8693-77ba0c71828b`); Prism repaired its
matching-period metadata and accepted the reviewed development contribution.
Independent worker-a reviews of the initial API and the affected metadata
are recorded at `483240a8847e40b27986d9388617595e3845828a` and
`a23f7af76d31ca21eefb687a1a34c71143e5c415`, respectively. This
release-readiness packaging is by worker-b Hive Task
`hive-request-dfff8e6b7c4a60ebec8244e80c1bfeb7f767f5f5`
(UID `119e6915-6dc0-463f-be76-93cba91c9115`); it awaits its own
independent release review and responsible-maintainer acceptance as prepared
on September 30, 2026. Offered under [Apache-2.0](LICENSE); the preparation
does not assert an official release or publication.
