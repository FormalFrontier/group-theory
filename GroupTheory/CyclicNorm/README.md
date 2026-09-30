# Finite cyclic norm exactness

For `[AddCommGroup A]`, `sigma : AddMonoid.End A` and `m : ℕ`, import
`GroupTheory.CyclicNorm` (or the root `GroupTheory`) and apply
`AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m`. Its premises are:

1. `0 < m` and `sigma ^ m = 1` in the endomorphism ring; exact order is not
   required.
2. `Function.Injective (nsmulAddMonoidHom (α := A) m)`; surjectivity and
   divisibility are not required.
3. For every `a : A` with `sigma a - a` in
   `(nsmulAddMonoidHom (α := A) m).range`, there is a `z : A` with
   `sigma z = z` and `a - z` in the same range. This is elementwise lifting of
   fixed quotient classes; no global section is assumed.

The conclusion is an equality of mathlib's native additive subgroups:

```lean
(∑ i ∈ Finset.range m, sigma ^ i).ker = (1 - sigma).range
```

The proof uses both orientations of the geometric-sum telescope. For a
norm-zero `v`, its finite double sum `w` satisfies `(1 - sigma) w = m • v`.
A fixed lift of `w` modulo `m • A` gives one divisibility witness, and
injectivity of multiplication by `m` cancels the resulting equation. The
argument does not invert the multiplication map.

The client `GroupTheoryTest.CyclicNorm`, using public imports and a public section, checks arbitrary
universes, the period-one and trivial-group cases, bijective multiplication by
`m`, and transfer through an independently supplied injective restriction. Its
coordinate swap on `ℤ × ℤ`, `m = 2`, has exactness although multiplication by two
is not onto; minus the identity on `ZMod 3`, `m = 2`, provides another
application. The client also tests both necessary failure boundaries: on `ℤ`,
`sigma = -1`, `m = 2`, a fixed quotient class lacks a fixed integral lift and
the kernel/range equality fails; on `ZMod 2`, `sigma = 1`, `m = 2`, multiplication
by two is not injective and the equality fails. The client's quotient-induced
map and coordinate-swap helper are private examples, not published API.

With the pinned Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, from the repository root:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build GroupTheory GroupTheoryTest
```

The cache fetch must succeed first. On September 30, 2026, development commit
`f7606ae41bae3a077708e7bbaf15e8b3e7f30783` had independently reviewed
mathematics and affected metadata, and native CI run 1382 (attempt 1) built
both roots and audited every actual-origin declaration, including private
examples, against the three standard axioms. The responsible maintainer
accepted and integrated that commit into development `main` at 12:35:30 UTC.
As prepared on September 30, 2026, the later release-readiness
documentation/metadata had not yet received affected independent review or
an applicable actual-head check; that earlier run does not approve changed
prose or constitute an official release.

For build planning, run 1382 took **113 seconds elapsed** from 12:23:32 to
12:25:25 UTC, including setup, precompiled mathlib cache retrieval, build
and axiom audit. This is a historical end-to-end CI observation, not a
clean-machine, CPU or standalone local-build benchmark; other hardware,
network and cache states can change the time. Allow time and disk for the
toolchain, dependencies and cache. Peak RSS and peak disk were not measured;
the bounded-thread command is guidance rather than a numerical resource bound.

Authors: Formal Frontier Agents. Original producer/client contributor: worker-b
Hive Task `hive-request-a2edb13065c52b892d241b54b1b126a02ccb23b7`
(UID `dfeefd22-cf15-4911-90aa-e10d49b8424c`); transfer/packaging contributor:
worker-b Hive Task `hive-request-19f643d063d7ee8b030ea4a16fadc2a6e94c0535`
(UID `5483d819-031d-4920-ae47-cd2a40feb9da`). Licensed under
[Apache-2.0](../../LICENSE). Earlier documentation/metadata contributor:
worker-b Task `hive-request-c217eb129452563cadee4cd7a804bd23651d9f65`
(UID `e5b2df87-c7be-4336-8693-77ba0c71828b`). Prism repaired the
matching-period metadata and accepted development integration; independent
worker-a reviews are recorded at `483240a8847e40b27986d9388617595e3845828a`
and `a23f7af76d31ca21eefb687a1a34c71143e5c415`. This subsequent
release-readiness packaging is by worker-b Task
`hive-request-dfff8e6b7c4a60ebec8244e80c1bfeb7f767f5f5`
(UID `119e6915-6dc0-463f-be76-93cba91c9115`); the responsible
maintainer retains its release acceptance and publication decisions.
