# Group Theory

Reusable group, subgroup and endomorphism mathematics. The first module,
`GroupTheory.CyclicNorm`, gives a finite cyclic norm exactness criterion for an
endomorphism of any additive commutative group. It has no source-repository,
incubator or Tate-cohomology dependency: only mathlib and its pinned transitive
packages are required. See the [mathematical guide](GroupTheory/CyclicNorm/README.md)
for the exact hypotheses, applications and counterexamples.

The separate `GroupTheory.FGScalarSurjectivity` module characterizes
surjectivity and bijectivity of an actual natural scalar on a finitely
generated abelian group; it requires only the same pinned mathlib graph.
See its [standalone guide](GroupTheory/FGScalarSurjectivity/README.md) for
the integer inverse, proof and limits. At transfer preparation on September 30,
2026 (13:44 UTC), this added module was a development candidate. Its exact
development commit `051d8f9565bef2b8f4ab54a2b7f811f31ba9db78` was
subsequently independently reviewed, accepted and integrated at 14:13:45 UTC;
its own separately reviewed official release is still pending.

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

The [FG scalar criterion](GroupTheory/FGScalarSurjectivity.lean) shows that,
for `[AddCommGroup A] [AddGroup.FG A]`, a natural `n ≥ 2` and actual
`Function.Surjective (fun x : A => n • x)`, the group `A` is finite and
`Nat.Coprime n (Nat.card A)`. One integer scalar uniformly inverts `n • ·`
in **both** orders. The same finite-and-coprime condition characterizes
surjectivity and bijectivity of this actual map. The public declarations are
`AddCommGroup.exists_zsmul_inverse_of_nsmul_surjective`,
`AddCommGroup.finite_coprime_of_nsmul_surjective`,
`AddCommGroup.nsmul_surjective_iff_finite_coprime` and
`AddCommGroup.nsmul_bijective_iff_finite_coprime`. The [guide](GroupTheory/FGScalarSurjectivity/README.md)
explains the necessary bounds; the result does not presume torsion,
finiteness or coprimality to obtain them, and is not a K-theory claim.

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

For this candidate, import `GroupTheory.FGScalarSurjectivity` directly or
`GroupTheory` for the FG public API. The single ordinary-import client
`GroupTheoryTest.FGScalarSurjectivity` checks uniform inverse use and zero
`ZMod 1`/nonzero `ZMod 7` examples. For a focused check, use the
same pinned cache fetched above, then
`LEAN_NUM_THREADS=1 lake --wfail build GroupTheory.FGScalarSurjectivity GroupTheoryTest.FGScalarSurjectivity`.
The transfer author's attributed focused `2236/2236` producer/client build
after repairing the client's parser syntax is not a published complete focused
log or a substitute for a **both-root** build and private-inclusive standard-
axiom audit. Original native run 1416 (attempt 1), from 13:57:24 to 13:59:19
UTC on September 30, 2026, did build both `GroupTheory` and `GroupTheoryTest`
roots at exact development commit `051d8f9565bef2b8f4ab54a2b7f811f31ba9db78`
with the pinned toolchain and nine-package graph; its complete actual-origin
transitive audit, including private/generated declarations, found only subsets
of `propext`, `Classical.choice` and `Quot.sound`. The responsible maintainer
intook the original evidence; this documentation update does not rerun it.
The dated preparation-stage caveats above were superseded for the original
first-release R after its independent review and protected integration on
September 30, 2026; its parentless first public root was unchanged with its
mirror receipt still pending at transfer preparation (13:44 UTC). That first
release was subsequently verified privately published at 13:47:58 UTC as
parentless `be37cbef6a4a0ac07cc25c70f4d77a16cd2f31f6`; its onboarding holds
are released. The earlier incubator and first-release checks do not by themselves
prove the combined FG graph: the later exact-Q run and affected independent
review supply that separate evidence. This new release-readiness prose and
public candidate still need fresh independent release review, responsible-
maintainer acceptance, protected promotions and verified publication.

### Build-cost guidance

The original native run 1382 took **113 seconds elapsed**, from 12:23:32 to
12:25:25 UTC on September 30, 2026, for the earlier CyclicNorm-only artifact.
The original exact-Q native run 1416 took **115 seconds elapsed**, from 13:57:24
to 13:59:19 UTC that day for the combined FG and CyclicNorm roots. These
end-to-end observations include setup, matching precompiled mathlib caches,
the builds and axiom audits; neither is an isolated local-build time, a
clean-machine benchmark or a prediction for another machine. Allow time and
space for the pinned toolchain, dependencies and cache before building; network
and cache state affect elapsed time. Peak memory (RSS) and peak disk use were
not measured, so no numeric resource requirement is inferred.
`LEAN_NUM_THREADS=1` tunes Lake's standard runtime worker budget; it does not
cap spawned Lean processes or their memory use, nor establish each child
compiler's thread count. Focused targets are not a verified process or memory
limit. The pinned Lake implementation does not consume `LAKE_JOBS`, so that
variable is not used here as a build-concurrency control.

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

FG mathematical argument: Prism, independently reviewed in bounded source
mathematics by worker-a Hive Task
`hive-request-33e12e1bf2da99c257c9e7740b11a8b96c959c4f`
(UID `9d1901a8-ca64-4c6c-896b-c828bc4624dc`); Lattice separately advised
the determinant route. Original FG Lean author: worker-b Hive Task
`hive-request-fa6f9c774e9d5c3857dcb2b843aab3186a954df4`
(UID `dd21e895-70e0-469c-991d-929b0bbfa519`). Incubator assembler:
worker-b Hive Task `hive-request-d2d9144bea61a93ca7dfdd582f8e6769b1baaced`
(UID `ccf0ff84-115c-44b2-a71f-a9f37051d41c`). Original FG code and
incubator-union reviewers are distinct worker-a Hive Tasks
`hive-request-9c993776c2cbe17698cfeaad702817b022cad08d`
(UID `c9917304-930b-466d-a0b3-a9a34b171357`) and
`hive-request-2a197b600bdf6d337b4f678b6a3f85a4d55a7057`
(UID `cd25b479-f2a1-42d7-a646-d6145522a536`). This destination
transfer and documentation: worker-b Hive Task
`hive-request-db92374ce7a70b10882a7d9947d9f61260685a60`
(UID `4cbf98c2-f317-4ffd-a0ed-7f5ef41be43e`); it needs its own
independent review and the responsible maintainer's acceptance as of transfer
preparation (13:44 UTC, September 30, 2026). Fresh worker-a Hive Task
`hive-request-1f8648e89b73fdd321354dcd881feca0333e8bf9`
(UID `9f3e960d-8b88-4145-bc5b-e98b328e8f5f`) independently approved exact-Q
destination content at `132a39d173e372421989c947f15ecd9a65b6fff1`;
Prism accepted and protected-integrated Q at 14:13:45 UTC. This release-readiness
update: worker-b Hive Task
`hive-request-8b069dd28caf9b065b2577f38ce6c099778dc1d5`
(UID `2e150abf-2a27-4b37-9c5f-7187ab003a69`), pending its own release review.
