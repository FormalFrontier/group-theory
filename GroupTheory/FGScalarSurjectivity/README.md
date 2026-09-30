# Surjective scalars on finitely generated abelian groups

Import `GroupTheory.FGScalarSurjectivity` or the root `GroupTheory`. Let `A` be
an additive commutative group with `[AddGroup.FG A]`, and let `n : ℕ` satisfy
`2 ≤ n`. All four results concern the **actual** function
`fun x : A => n • x`, not an arbitrary endomorphism:

- `AddCommGroup.exists_zsmul_inverse_of_nsmul_surjective hn hsurj` requires
  `hsurj : Function.Surjective (fun x : A => n • x)` and produces one `k : ℤ`
  with both `n • (k • x) = x` and `k • (n • x) = x` for every `x : A`. The
  inverse is uniform in `x`, but its integer representative need not be unique.
- `AddCommGroup.finite_coprime_of_nsmul_surjective hn hsurj` derives
  `Finite A ∧ Nat.Coprime n (Nat.card A)` from the same hypotheses; torsion,
  finiteness and coprimality are conclusions, not additional assumptions.
- `AddCommGroup.nsmul_surjective_iff_finite_coprime hn` states that actual
  `n`-scalar surjectivity is equivalent to
  `Finite A ∧ Nat.Coprime n (Nat.card A)`.
- `AddCommGroup.nsmul_bijective_iff_finite_coprime hn` gives the same
  criterion for bijectivity of the actual scalar map.

For the forward direction, finite generation of the top integer submodule
and surjectivity give `⊤ ≤ Ideal.span {(n : ℤ)} • ⊤`. Mathlib's
finite-generation form of Nakayama's lemma then supplies an annihilator
`d = 1 + (n : ℤ) * k`; `2 ≤ n` implies `d ≠ 0`. This derives torsion,
which together with finite generation implies finiteness. The same identity
produces the uniform two-sided integer inverse `-k`. Cauchy's theorem and
that inverse rule out a prime common to `n` and `Nat.card A`. The converse
uses mathlib's `Nat.Coprime.nsmul_right_bijective`.

The private ordinary-import client `GroupTheoryTest.FGScalarSurjectivity`
checks the four public APIs, both inverse equations, the zero group `ZMod 1`
and a nonzero `ZMod 7` example at `n = 2`. The lower bound and finite
generation matter: multiplication by `1` is surjective on infinite FG `ℤ`,
and positive-scalar multiplication is surjective on infinite non-FG `ℚ`.
There is no theorem here about arbitrary endomorphisms, nonabelian power
maps, all-scalar divisibility, K-theory or coverage of an external source.

With the pinned Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, from the repository root:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build GroupTheory.FGScalarSurjectivity GroupTheoryTest.FGScalarSurjectivity
```

The matching mathlib cache must be fetched successfully before building.
`LEAN_NUM_THREADS=1` tunes Lake's standard runtime worker budget, not the
number of spawned Lean processes or a memory bound; it does not establish
each child compiler's thread count. The pinned Lake implementation does not
consume `LAKE_JOBS`. These focused targets are not a verified process cap.
These focused targets alone do not certify the combined `GroupTheory` and
`GroupTheoryTest` roots or their complete private-inclusive transitive axiom
audit. The transfer author's attributed focused `2236/2236` producer/client
build followed a repair of the client's parser syntax; its complete original
focused logs were not published as release evidence. Original native run 1416
(attempt 1), from 13:57:24 to 13:59:19 UTC on September 30, 2026, built both
roots at exact development commit `051d8f9565bef2b8f4ab54a2b7f811f31ba9db78`
with the pinned toolchain and nine-package graph. Its owner-intaken complete
actual-origin transitive audit, including private/generated declarations,
found only subsets of `propext`, `Classical.choice` and `Quot.sound`.
That original combined run took 115 seconds end-to-end including setup, the
matching cache, build and audit; it is not a clean-machine benchmark or a
resource minimum, and peak memory and disk use were not measured.

This transfer from the accepted incubator donor onto the separately accepted
Group Theory base was prepared as a September 30, 2026 (13:44 UTC)
**development candidate**; at that time its destination review, both-root
verification, acceptance and release were pending. Fresh independent review
at `132a39d173e372421989c947f15ecd9a65b6fff1` approved the exact-Q
destination content. The responsible maintainer accepted and protected-
integrated Q at 14:13:45 UTC that day. This accepted development code is not
itself the existing first public release or a new official FG dependency.
At release preparation, before the 15:27 UTC promotions on September 30,
this release-readiness prose, its public candidate, protected promotions and
private publication still needed separate review, acceptance and verification.
Subsequently, independent consolidated review
`fc2bdb069ec12f112f3b32f89c2ab13dc4d750f9` approved corrected release content
`f10b107e30f49ed020323abd8bb517681410e197`; protected main/internal/public
promotions completed at 15:27:30/15:27:48/15:27:54 UTC. Official release
`3a73363199049f9e05e7f74455ec0ff747ba67f8`, tree
`2bb587febf95464365b3270c4daf0f529d22bab1`, sole prior official
`be37cbef6a4a0ac07cc25c70f4d77a16cd2f31f6`, was independently verified on
private GitHub at 15:30:40.937154 UTC. This exact-release receipt supersedes
the preparation-stage pending language, not review or publication requirements
for later revisions.

Authors: Formal Frontier Agents. Prism developed the bounded mathematical
annihilator argument, independently reviewed by worker-a Hive Task
`hive-request-33e12e1bf2da99c257c9e7740b11a8b96c959c4f`
(UID `9d1901a8-ca64-4c6c-896b-c828bc4624dc`); Lattice separately
advised the determinant route. Original Lean producer and client: worker-b
Hive Task `hive-request-fa6f9c774e9d5c3857dcb2b843aab3186a954df4`
(UID `dd21e895-70e0-469c-991d-929b0bbfa519`). Incubator registration
and packaging: worker-b Hive Task
`hive-request-d2d9144bea61a93ca7dfdd582f8e6769b1baaced`
(UID `ccf0ff84-115c-44b2-a71f-a9f37051d41c`). Independent original-code
review: worker-a Hive Task
`hive-request-9c993776c2cbe17698cfeaad702817b022cad08d`
(UID `c9917304-930b-466d-a0b3-a9a34b171357`). Independent incubator
union review: worker-a Hive Task
`hive-request-2a197b600bdf6d337b4f678b6a3f85a4d55a7057`
(UID `cd25b479-f2a1-42d7-a646-d6145522a536`). This destination transfer
and packaging: worker-b Hive Task
`hive-request-db92374ce7a70b10882a7d9947d9f61260685a60`
(UID `4cbf98c2-f317-4ffd-a0ed-7f5ef41be43e`), subject to its own
independent review and maintainer acceptance as of transfer preparation.
Independent destination-content reviewer: worker-a Hive Task
`hive-request-1f8648e89b73fdd321354dcd881feca0333e8bf9`
(UID `9f3e960d-8b88-4145-bc5b-e98b328e8f5f`); Prism accepted and integrated
exact Q. This release-readiness documentation: worker-b Hive Task
`hive-request-8b069dd28caf9b065b2577f38ce6c099778dc1d5`
(UID `2e150abf-2a27-4b37-9c5f-7187ab003a69`), not yet independently
release-reviewed at preparation on September 30, 2026, before the 15:27 UTC
promotions. Prism corrected the concurrency guidance; worker-a Hive Task
`hive-request-9cb89bb149a3628a95503fbca5c0bba43e3ed3f3`
(UID `69d45cb7-a905-4841-b020-4fe87dfafe0d`) independently reviewed the
corrected release recorded above. This later lifecycle-date clarification is
by Prism; it repeats no original proof or build. Licensed under
[Apache-2.0](../../LICENSE).
