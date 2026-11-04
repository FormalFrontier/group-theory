# Using the interfaces

[Back to the overview and build instructions](../README.md#use-and-verification) ·
[Complete headline catalogue](HeadlineResults.md) · [Detailed result guide](Results.md).

### Imports and interfaces

Import `GroupTheory` for these results, or import
`GroupTheory.Topology.OpenQuotient`,
`GroupTheory.Topology.ConnectedComponentQuotient`,
`GroupTheory.Topology.ConnectedComponentOpenSubgroup`,
`GroupTheory.Topology.Sections`, `GroupTheory.CyclicNorm` or
`GroupTheory.FGScalarSurjectivity`, `GroupTheory.Topology.CompactOpenSubgroup`,
`GroupTheory.Topology.OpenKernel` or `GroupTheory.Topology.CircleCharacter`
individually. The finite-index results are also available through
`GroupTheory.Topology.FiniteIndex`; the open/closed/clopen subgroup and left-coset
statements through `GroupTheory.Topology.Algebra.Group.Quotient`; and character subgroups through
`GroupTheory.Topology.CharacterSubgroups`. The rational-circle inclusion and
character comparisons are available through `GroupTheory.Topology.RationalCircle`
and `GroupTheory.Topology.RationalCircleCharacter`. The compact/discrete map
results are available through `GroupTheory.Topology.ContinuousMap.CompactDiscrete`
and `GroupTheory.Topology.Algebra.CompactGroup.DiscreteFactor`.
Import `GroupTheory.Topology.Algebra.OpenSubgroup.Pi` for finite-cylinder
containment, or `GroupTheory.Topology.Algebra.CompactGroup.PiDiscreteFactor`
for finite-coordinate map factorization. Import
`GroupTheory.Topology.Algebra.Group.PiDiscreteFactor` for the homomorphism
projection and descent APIs; all are re-exported by `GroupTheory`.
For a discrete-group-valued homomorphism `f : (∀ i, G i) →ₜ* H`, use
`obtain ⟨s, N, fbar, hfactor, hquot, hstage⟩ :=
ContinuousMonoidHom.exists_finset_openNormalSubgroup_pi_factor f`.
Here `hfactor` is a bundled homomorphism equality, and `hquot` and `hstage`
give intrinsic quotient and stage discreteness. With compact factors, the
`_finite` theorem returns coordinate finiteness and product finiteness instead.
Use `letI := ContinuousMap.discreteTopology_of_compactSpace (X := X) (Y := Y)`
when a local map-space discreteness instance is needed, or obtain the quotient
map with `obtain ⟨N, fbar, hfactor⟩ := f.exists_openNormalSubgroup_factor`.
For `f : C(I → G, Y)`, use
`obtain ⟨s, N, fbar, hfactor⟩ := f.exists_finset_openNormalSubgroup_pi_factor`;
`hfactor x` identifies `f x` with evaluation of `fbar` on the selected quotient
coordinates. For an open normal subgroup `M` of a dependent product, use
`obtain ⟨s, N, hsubset⟩ := M.exists_finset_pi_subset`; for a constant family,
use `obtain ⟨s, N, hsubset⟩ := M.exists_finset_uniform_pi_subset`.
For example, after
`import GroupTheory`, use `MonCat.sectionsLift F q hq` to bundle a compatible
continuous family and `MonCat.sectionsπ_comp_sectionsLift F q hq j` to recover
its `j`th component; use
`QuotientGroup.connectedComponentQuotientLift_mk_apply f x` to recover `f x`;
use `Topology.IsOpenQuotientMap.totallyDisconnectedSpace hf` for an open
quotient map `hf` between compact Hausdorff totally disconnected and Hausdorff
spaces;
use `AddMonoid.End.cyclicNorm_ker_eq_one_sub_range sigma m hm hperiod hinjective hlift`
or `(AddCommGroup.nsmul_surjective_iff_finite_coprime (A := A) (n := n) hn).mp hsurj`.
The maintained `GroupTheoryTest` root exercises the interfaces but is not
required by downstream imports. Its sections clients include empty indexing,
parallel arrows, non-group stages, discontinuous transitions, nonsurjective
projections and a nontrivial consequence of `sections_topology`. The cyclic
clients cover fixed-class lifting, the coordinate swap on `ℤ × ℤ` and
counterexamples when hypotheses are dropped; the scalar clients include
concrete `ZMod` examples. The quotient clients cover connected real, discrete,
indiscrete non-Hausdorff and mixed connected/discrete groups. The compact/discrete
clients exhibit distinct Boolean values, isolated maps and continuous observers;
they derive right invariance and separation of quotient points from factorization.
The power clients use a Boolean observer that depends on both coordinates and
cannot be a homomorphism for any group structure on `Bool`. They also exhibit
a nonconstant observer with infinite index and infinite discrete target,
finite/discrete selected stages, empty indices and targets, and an explicit
empty-coordinate factorization of a constant map. The homomorphism clients
include two essential coordinates with proper nontrivial kernels, heterogeneous
factors, arbitrary topologies on ignored factors, noninjective descent,
infinite discrete targets and a surjective integer observer that rules out
finite stages. Empty and trivial cases and a closed nonopen real normal
subgroup test the boundaries of the canonical projection.

### Zero-sum pairs and multiplicative images

Import
[`GroupTheory.Algebra.IsAddUnit`](../GroupTheory/Algebra/IsAddUnit.lean).
Given `[NonUnitalNonAssocSemiring S]`, `a b : S` and `h : a + b = 0`,
use `mul_self_eq_mul_self_of_add_eq_zero h` for `a * a = b * b`.
For a target `[Monoid T]`, a family `F` with `[FunLike F S T]` and
`[MulHomClass F S T]`, and a supplied `μ : F`, use
`MulHomClass.isUnit_apply_iff_of_add_eq_zero μ h` for
`IsUnit (μ a) ↔ IsUnit (μ b)`.
The universes of `S`, `T` and `F` are independent. This needs only
multiplication preservation: no source multiplicative identity or
associativity, target commutativity, or preservation of addition, zero or one.
The result is an equivalence of unit predicates, not unconditional unitness
of either value. The [result guide](Results.md#zero-sum-pairs-and-multiplicative-images)
explains the self-product argument and the reused source/API.

### Subgroup membership through finite powers

Import
[`GroupTheory.Algebra.Group.Subgroup.Power`](../GroupTheory/Algebra/Group/Subgroup/Power.lean),
or the aggregate `GroupTheory`. For `[Group G]`, `[SetLike S G]`,
`[SubgroupClass S G]`, `H : S`, `a : G`, `s : Finset ι` and `e : ι → ℕ`, use
`SubgroupClass.pow_finset_gcd_mem_iff H a s e` for
`a ^ (s.gcd e) ∈ H ↔ ∀ i ∈ s, a ^ (e i) ∈ H`.
With `hg : s.gcd e = 1` and `hpowers : ∀ i ∈ s, a ^ (e i) ∈ H`,
`SubgroupClass.mem_of_forall_pow_mem_of_gcd_eq_one H hg hpowers` gives `a ∈ H`.
The carrier, subgroup-like object type and index universes are independent.
The additive peers use an `AddGroup`, an additive subgroup-like object and
natural multiples; neither commutativity nor normality is needed.

For an ordinary subgroup generated by selected powers,
`Subgroup.closure_pow_image_eq_zpowers_finset_gcd a s e` gives
`Subgroup.closure ((fun i => a ^ (e i)) '' (s : Set ι)) =
Subgroup.zpowers (a ^ (s.gcd e))`.
The additive formula is
`AddSubgroup.closure ((fun i => (e i) • a) '' (s : Set ι)) =
AddSubgroup.zmultiples ((s.gcd e) • a)`.
Here closure means algebraic subgroup generation, not topological closure.
There is no finite or nonempty index-type assumption. Empty or all-zero
families have gcd zero and generate the bottom subgroup. Zero exponents are
legal, and gcd one is a condition on the whole family, not on a selected pair.

For `[Group G]`, `a : G` and any `m n : ℕ`, use
`Subgroup.zpowers_pow_inf a m n` for
`Subgroup.zpowers (a ^ m) ⊓ Subgroup.zpowers (a ^ n) =
Subgroup.zpowers (a ^ (Nat.lcm m n))`.
For `[AddGroup A]` and `a : A`, use
`AddSubgroup.zmultiples_nsmul_inf a m n` for the corresponding intersection of
the integer-multiple subgroups of `m • a` and `n • a`. These are binary
intersections. Zero exponents require no separate premise; no commutativity or
order assumption is needed. The import is the same subgroup-power module above.

For `s : Finset ι` and `e : ι → ℕ`, use
`Subgroup.zpowers_inf_finsetInf_pow a s e` for
`Subgroup.zpowers a ⊓ (s.inf fun i => Subgroup.zpowers (a ^ (e i))) =
Subgroup.zpowers (a ^ (s.lcm e))`.
With `hs : s.Nonempty`, use `Subgroup.finsetInf_zpowers_pow a s e hs` for
the same formula without the initial `Subgroup.zpowers a` intersection.
The additive calls are `AddSubgroup.zmultiples_inf_finsetInf_nsmul a s e`
and `AddSubgroup.finsetInf_zmultiples_nsmul a s e hs`.
Only a `Group` or `AddGroup` is needed, in independent carrier and index
universes. Zero and repeated coefficients are allowed. For an empty family,
the plain intersection is top and the lcm is one, so retain the initial
cyclic factor; no nonempty or finite index-type premise is imposed.

### Power kernels and restriction

Import [`GroupTheory.MonoidHom.PositivePower`](../GroupTheory/MonoidHom/PositivePower.lean),
or the aggregate `GroupTheory`. For `[Monoid T]`, `ha : IsLeftRegular a`,
`b : T`, `s : Finset ι` and `e : ι → ℕ`, use
`ha.pow_finset_gcd_eq_pow_finset_gcd_iff b s e` for
`a ^ (s.gcd e) = b ^ (s.gcd e) ↔ ∀ i ∈ s, a ^ (e i) = b ^ (e i)`.
Here `IsLeftRegular a` means that `x ↦ a * x` is injective; no condition is
imposed on `b`. Given `hg : s.gcd e = 1` and the memberwise equalities `h`,
`ha.eq_of_forall_pow_eq_of_gcd_eq_one hg h` gives `a = b`.
The criterion is the gcd of the whole finite family, not the existence of a
coprime selected pair. At the empty family the gcd is zero and only the
vacuous equivalence remains. Zero exponents are allowed.

Separately, for `ha : IsRightRegular a`, the same finite-family methods
`ha.pow_finset_gcd_eq_pow_finset_gcd_iff b s e` and
`ha.eq_of_forall_pow_eq_of_gcd_eq_one hg h` use injectivity of `x ↦ x * a`.
Again `b` is arbitrary, and the index and carrier universes are independent.
The empty-family gcd is zero in both routes, and zero exponents are allowed.

For two exponents, `ha.pow_gcd_eq_pow_gcd_iff b m n` gives the binary
criterion for either left or right regularity. In the right-regular route,
`ha.eq_of_pow_eq_pow_of_coprime hcop hm hn` gives equality from
`hcop : Nat.Coprime m n` and equalities at `m` and `n`. The binary gcd
criteria include `(m, n) = (0, 0)`. The left- and right-regular results have
additive counterparts over an `AddMonoid`, with natural multiples in place
of powers and injective left or right addition by `a`, respectively;
no commutativity, group or global cancellation is assumed.
The `Finset.pow_gcd_eq_pow_gcd_iff` and
`Finset.eq_of_forall_pow_eq_of_gcd_eq_one` specializations retain the
`LeftCancelMonoid` interface.

Homomorphism restriction is a separate interface. For `f : M →* N`,
`[MulOne M]` and `[Monoid N]`, the input
`∀ x : N, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ Set.range f` goes to
`MonoidHom.comp_right_injective_of_forall_pow_mem_range` or
`MonoidHom.cancel_right_of_forall_pow_mem_range` for unique-positive-root
monoid targets. The additive versions use an `AddZero` source and
torsion-free additive monoid targets. These source classes supply only
multiplication and a distinguished one, or addition and a distinguished zero,
not associativity or identity laws.

For indexed left-regular image detection, use
`MonoidHom.cancel_right_of_finite_powers_mem_range_of_isLeftRegular f hfamily g h hg`,
with:

- `f : A →* M`, `[MulOne A] [Monoid M] [Monoid N]` and an index type `ι`,
  all in four independent universes;
- `hfamily : ∀ x : M, ∃ s : Finset ι, ∃ e : ι → ℕ,
  s.gcd e = 1 ∧ ∀ i ∈ s, x ^ (e i) ∈ Set.range f`;
- fixed `g h : M →* N` and `hg : ∀ x : M, IsLeftRegular (g x)`.

The conclusion is `g.comp f = h.comp f ↔ g = h`. Left regularity means
injectivity of `y ↦ g x * y`; `h` is arbitrary. Both `s` and `e` may depend
on `x`. There is no global cancellation, commutativity, group, surjectivity,
finite or nonempty index-type, decidable equality or positivity premise.
Zero and repeated exponents are allowed; singleton exponent one is valid,
but empty or all-zero families cannot have gcd one. The generated additive peer
`AddMonoidHom.cancel_right_of_finite_multiples_mem_range_of_isAddLeftRegular`
uses `[AddZero A] [AddMonoid M] [AddMonoid N]`, natural multiples
`(e i) • x ∈ Set.range f`, and `hg : ∀ x : M, IsAddLeftRegular (g x)`.
Its conclusion is again equality of the two composites iff equality of the
fixed comparison maps; it has the same four independent universes.

For the retained finite-natural-set left-regular specialization, use
`MonoidHom.cancel_right_of_finite_powers_mem_range h hpowers f g hf`, with:

- `h : A →* M`, `[MulOne A] [Monoid M] [Monoid N]`, in three independent universes;
- `hpowers : ∀ x : M, ∃ s : Finset ℕ, s.gcd id = 1 ∧
  ∀ n ∈ s, x ^ n ∈ Set.range h`;
- fixed `f g : M →* N` and `hf : ∀ x : M, IsLeftRegular (f x)`.

The conclusion is `f.comp h = g.comp h ↔ f = g`. Only `f x` must be
left-regular; no regularity of `g` or global cancellation, commutativity, group,
surjectivity or positivity hypothesis is imposed. The finite set may depend
on `x`. The additive peer
`AddMonoidHom.cancel_right_of_finite_multiples_mem_range` uses `AddZero A`,
additive monoids and natural multiples, with add-left-regular first-map values.
Singleton `{1}` is valid; empty or all-zero sets cannot have gcd one.
Zero exponents are legal. This natural-set interface is exactly the indexed
left-regular criterion with `ι = ℕ` and `e = id`; its signature is unchanged.

The coprime-image adapter retains the signature
`MonoidHom.cancel_right_of_coprime_powers_mem_range h hpowers f g hf`, with:

- `h : A →* M`, `[MulOne A] [Monoid M] [Monoid N]`, in independent universes;
- `hpowers : ∀ x : M, ∃ m n : ℕ, Nat.Coprime m n ∧
  x ^ m ∈ Set.range h ∧ x ^ n ∈ Set.range h`;
- fixed `f g : M →* N` and `hf : ∀ x : M, IsLeftRegular (f x)`.

The conclusion is `f.comp h = g.comp h ↔ f = g`. Only the first map's
values need left regularity; `g` is unrestricted. No global target cancellation,
commutativity, group, surjectivity or positive-exponent premise is imposed.
The additive peer is `AddMonoidHom.cancel_right_of_coprime_multiples_mem_range`,
with `AddZero A`, additive monoids, natural multiples and add-left-regular
values of the first map. Exponents or coefficients may be zero and depend on `x`.
This fixed-pair equality criterion is not itself a claim of global injectivity
on all homomorphisms into an arbitrary monoid.

For the separate right-regular image criterion, use
`MonoidHom.cancel_right_of_finite_powers_mem_range_of_isRightRegular f hfamily g h hg`,
with:

- `f : A →* M`, `[MulOne A] [Monoid M] [Monoid N]` and an index type `ι`,
  all in four independent universes;
- `hfamily : ∀ x : M, ∃ s : Finset ι, ∃ e : ι → ℕ,
  s.gcd e = 1 ∧ ∀ i ∈ s, x ^ (e i) ∈ Set.range f`;
- fixed `g h : M →* N` and `hg : ∀ x : M, IsRightRegular (g x)`.

The conclusion is `g.comp f = h.comp f ↔ g = h`. Right regularity means
injectivity of `y ↦ y * g x`; the second comparison map `h` is arbitrary.
Both `s` and `e` may depend on `x`. No global target cancellation,
commutativity, group, surjectivity, finite or nonempty index type, decidable
equality or positivity is required. The generated additive peer
`AddMonoidHom.cancel_right_of_finite_multiples_mem_range_of_isAddRightRegular`
uses `AddZero A`, additive monoids, natural multiples and
`hg : ∀ x : M, IsAddRightRegular (g x)`. Zero and repeated exponents and singleton
exponent one are legal; empty or all-zero families cannot have gcd one.
The indexed left- and right-regular image interfaces have the same family input
shape, with the respective regularity of the first comparison map. Unlike the
elementwise power-equality kernels above, their premise asks for powers in the
image of `f`. Neither fixed-pair criterion itself asserts injectivity on all
homomorphisms into an arbitrary monoid.

For `[LeftCancelMonoid T]`, use
`MonoidHom.comp_injective_of_successive_powers_mem_range f h` with
`h : ∀ x : N, ∃ n : ℕ, x ^ n ∈ Set.range f ∧ x ^ (n + 1) ∈ Set.range f`.
The first exponent may be zero. With only `[Monoid T]`,
`MonoidHom.cancel_right_of_successive_powers_mem_range` instead asks that
every value of the first of the two compared homomorphisms be left-regular;
the second homomorphism's values are unrestricted.

### Monoid cochains and Noetherian cohomology

Import [`GroupTheory.Cohomology.Basic`](../GroupTheory/Cohomology/Basic.lean) for
the cochains, cohomology and degree-zero equivalences, or
[`GroupTheory.Cohomology.Noetherian`](../GroupTheory/Cohomology/Noetherian.lean)
for the Noetherian instances. The latter publicly imports the former; both
are available through `GroupTheory`.

For `{R : Type u} {G : Type v} [Ring R] [Monoid G]` and `A : Rep.{w} R G`,
use `Rep.inhomogeneousCochains A` and `Rep.cohomology A n` for `n : ℕ`.
The three universes are independent. `Rep.inhomogeneousCochains_X A n`
identifies the degree `n` module with `ModuleCat.of R ((Fin n → G) → A)`;
`Rep.inhomogeneousCochains_d_apply A n f g` evaluates its differential on a
tuple using the given linear action and alternating integer signs.

Use `Rep.cohomologyZeroEquiv A` to pass from a degree-zero class to a member
of `A.ρ.fixedSubmodule`; its `.symm` takes a fixed vector back to its constant
class, with `Rep.cohomologyZeroEquiv_symm_apply A x` as the computation law.
Under `[IsNoetherian R A]`, `Rep.isNoetherian_cohomology_zero A` supplies
`IsNoetherian R (Rep.cohomology A 0)` for arbitrary `G`. With `[Finite G]`,
`Rep.isNoetherian_cohomology A n` supplies it in every natural degree.
These are typeclass instances. No `IsNoetherianRing R`, commutative-ring,
trivial-action, finite underlying coefficient type or separate finite-generation
hypothesis is needed. Noetherian coefficients do themselves imply finite generation.

For `[CommRing R] [Group G]`, `Rep.cohomologyZeroEquivInvariants A` gives the
invariant-submodule version, still with independent universes. Its `_apply`
lemma identifies values in `A` with those of `Rep.cohomologyZeroEquiv A`.
For the full Mathlib comparison, instead take `{R G : Type u}` and
`A : Rep.{u} R G`, with ring, group and coefficient carrier in one universe.
Use `Rep.inhomogeneousCochains_eq A` for the complex equality and
`Rep.cohomology_eq A n` for the cohomology equality. For `x : Rep.cohomology A 0`,
`Rep.cohomologyZeroEquivInvariants_eq_H0Iso A x` compares values in `A` after
`eqToHom (Rep.cohomology_eq A 0)` transports the class to Mathlib's cohomology.
It does not assert a full Mathlib bridge for a noncommutative ring, a monoid
that is not a group or independent universes. See the
[construction and hypotheses](Results.md#monoid-cochains-and-noetherian-cohomology).

### Inverses in a subsemigroup's closure

Import
[`GroupTheory.Topology.Algebra.Group.Subsemigroup.Closure`](../GroupTheory/Topology/Algebra/Group/Subsemigroup/Closure.lean),
or the aggregate `GroupTheory`. The public theorem
`Subsemigroup.inv_mem_closure_of_noetherianSpace` has ambient inputs
`{G : Type u} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]`.
The last instance refers to the canonical regular **left** action, so every
map `x ↦ g * x` is continuous. For `S : Subsemigroup G`, supply:

- `hR : ∀ s ∈ S, ContinuousOn (fun x : G => x * s) (_root_.closure (S : Set G))`;
- `[NoetherianSpace {x : G // x ∈ _root_.closure (S : Set G)}]`;
- `hx : x ∈ _root_.closure (S : Set G)` for the element under consideration.

Then `S.inv_mem_closure_of_noetherianSpace hR hx` gives
`x⁻¹ ∈ _root_.closure (S : Set G)`. Use the actual closure subtype with
the topology induced from the given topology on `G`, not a replacement
topology or an abstractly equivalent carrier. No ambient `NoetherianSpace G`,
global right-translation continuity, joint multiplication, inversion continuity,
T1, compactness or commutativity is required. No closedness hypothesis on `S`
is needed, and `S` may be empty. This API supplies membership under inversion,
not a bundled topological group or subgroup classification.

For an already closed subsemigroup, the separate
[`Subsemigroup.inv_mem_of_isClosed_of_noetherianSpace`](../GroupTheory/Topology/Algebra/Group/Subsemigroup.lean)
uses `hS : IsClosed (S : Set G)` and `[NoetherianSpace S]`, with no
right-translation hypothesis. Its additive and submonoid consequences are
described in the [result guide](Results.md#closed-noetherian-subsemigroups).

For the preirreducible-closure variant, keep exactly the same group, topology,
canonical regular **left** action and local right-continuity input `hR`, and supply:

- `hS : IsPreirreducible (S : Set G)`;
- `[WellFoundedLT (TopologicalSpace.IrreducibleCloseds G)]`;
- `hx : x ∈ _root_.closure (S : Set G)`.

Then `S.inv_mem_closure_of_isPreirreducible hR hS hx` gives membership of `x⁻¹`
in that closure, for any closure element, not only `x ∈ S`. The instance concerns
strict inclusion of nonempty irreducible closed subsets of the **ambient** `G`
with its original topology: `LT`, not `GT`. No ambient Noetherian, global right,
joint-multiplication, inversion-continuity, T1, compactness or commutativity
premise is added. Empty `S` is allowed, but then `hx` is impossible.
Do not drop `hR`: it is used to make the topological closure a subsemigroup.
For an already closed preirreducible subsemigroup,
`Subsemigroup.inv_mem_of_isClosed_of_isPreirreducible` instead takes closedness,
preirreducibility and the same ambient well-foundedness, with no right-continuity
premise.

### Closed self-embeddings

Import [`GroupTheory.Topology.ClosedEmbedding`](../GroupTheory/Topology/ClosedEmbedding.lean)
directly, or the aggregate `GroupTheory` through its public subsemigroup import.
For arbitrary `{X : Type v} [TopologicalSpace X]`, `{f : X → X}`, supply:

- `hf : Topology.IsClosedEmbedding f`;
- `hfin : (irreducibleComponents X).Finite`;
- `[WellFoundedLT (TopologicalSpace.IrreducibleCloseds X)]`.

Then `hf.surjective_of_finite_irreducibleComponents hfin` proves
`Function.Surjective f`. The order is strict inclusion of **nonempty** irreducible
closed sets. Finitely many irreducible components does not mean finitely many
points, connected components or path components, and no dimension condition
substitutes for the given hypotheses. Neither Noetherianity, separation nor
algebraic structure is needed; `X` may be empty. See the
[proof outline](Results.md#closed-self-embeddings-and-irreducible-components).

### Maps of group-diagram colimits

Import `GroupTheory.Category.Grp.ColimitMap` for `GrpCat.Colimits.map`, or
`GroupTheory.Category.Grp.ColimitMapKernel` for its surjectivity and kernel
formula; both are exported by `GroupTheory`. Supply two diagrams over the same
category and component homomorphisms `α j` with compatibility
`(α k).comp (F.map f).hom = (G.map f).hom.comp (α j)` for every arrow `f`.
The object groups of the two diagrams may have independent universes.

`map_ι` and `map_comp_ι` describe the restrictions to the original generators;
`eq_map_iff` characterizes the induced homomorphism by those restrictions.
With `∀ j, Function.Surjective (α j)`, `map_surjective` gives surjectivity and
`ker_map` identifies the kernel with the normal closure of
`⋃ j, ι F j '' ((α j).ker : Set (F.obj j))`. This is a statement about the
canonical colimits, not an injectivity claim for arbitrary componentwise
injections. No nonempty-index premise is needed. See the
[map construction](../GroupTheory/Category/Grp/ColimitMap.lean) and
[kernel theorem](../GroupTheory/Category/Grp/ColimitMapKernel.lean).

### Finite orbits of integral elements

Import
[`GroupTheory.GroupAction.Integral`](../GroupTheory/GroupAction/Integral.lean)
directly. For `R : Type u`, `A : Type v` and `M : Type w` with
`[CommRing R] [CommRing A] [IsDomain A] [Algebra R A]`,
`[Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]`, and
`hx : IsIntegral R x`, use `hx.finite_orbit (M := M)` to obtain
`(MulAction.orbit M x).Finite`. The universes are independent.

Scalar commutation is the coefficient-fixing hypothesis; no action on `R`
is needed. There is no field or domain assumption on `R`, injectivity
assumption on `algebraMap R A`, faithfulness requirement, global
integrality hypothesis on `A`, or group or finiteness assumption on `M`.
See the [result guide](Results.md#finite-orbits-of-integral-elements).

### Action automorphisms

Import `GroupTheory.GroupAction.Centralizer` (or `GroupTheory`). For an action
`A` in a category, use `Action.autEquivCentralizer A α` to obtain its underlying
automorphism as a centralizer element, or `(Action.autEquivCentralizer A).symm f`
to equip a commuting isomorphism with equivariance. The lemmas
`Action.coe_autEquivCentralizer` and `Action.mapIso_autEquivCentralizer_symm`
characterize both forgetful maps.

For `[Group G] [MulAction G X]`, use `Action.autEquivPermCentralizer G X` for
permutations instead. Its `_apply`, `_apply_symm`, `_symm_hom_apply` and
`_symm_inv_apply` lemmas are simp lemmas for the four coordinates. Use
`Action.autEquivPermCentralizer_eq_iff` to prove equality with a supplied
centralizer member by evaluation. Stock `map_mul`, `map_one` and `map_inv`
apply directly to both multiplicative equivalences. The `_mul_apply` lemma
makes the order `α.hom.hom (β.hom.hom x)` explicit. No unfolding of the
constructors or choice of an element of `X` is needed.

### Compatibility

Older Profinite Groups versions that also define
`Topology.IsOpenQuotientMap.totallyDisconnectedSpace` cannot share an import
graph with `GroupTheory.Topology.OpenQuotient` or the aggregate `GroupTheory`
import. Removing that duplicate prevents the collision. Preserving that Profinite
Groups API also requires re-exporting Group Theory's canonical declaration.

Continuous Group Cohomology versions that define
`ContinuousMap.discreteTopology_of_compactSpace` and
`ContinuousMap.exists_openNormalSubgroup_factor` cannot share an import graph
with these Group Theory modules or the aggregate `GroupTheory` import.
Compatible versions must re-export the Group Theory declarations rather than
defining them again.

### Additional theory imports

For the occurrence-sensitive positive-power product criterion, import its theory module:

```lean
import GroupTheory.Algebra.GroupWithZero.Reduced.List
```

For nilpotence and nilpotency-class bounds of finite orthogonal sums, and vanishing
powers of finite commuting sums in an arbitrary semiring, import:

```lean
import GroupTheory.Ring.Nilpotent.Finset
```

`Finset.isNilpotent_sum_iff_of_pairwise_mul_eq_zero` says that the sum is
nilpotent if and only if every supported summand is nilpotent.
`Finset.nilpotencyClass_sum_le_of_pairwise_mul_eq_zero` bounds its class by
`max (nilpotencyClass (0 : R)) (s.sup (fun i => nilpotencyClass (f i)))`.
The generic `SemiconjBy.nilpotencyClass_le_add_one` is also available through
this import. For `i ∈ s`, a left row
`∀ j ∈ s, j ≠ i → f i * f j = 0` gives
`SemiconjBy (f i) (∑ j ∈ s, f j) (f i)` using `Finset.mul_sum` and
`Finset.sum_eq_single`. When the sum is nilpotent, the generic bound gives
`nilpotencyClass (f i) ≤ nilpotencyClass (∑ j ∈ s, f j) + 1`.
For semiconjugacy, powers and zero-reflecting maps, import
`GroupTheory.Algebra.GroupWithZero.Nilpotent`. The power formula includes all
natural exponents. The map formula uses the generic `MonoidWithZeroHomClass`
interface and the zero-reflection hypothesis `∀ a, f a = 0 → a = 0`.

For the quantitative commuting bound, use
`Finset.sum_pow_eq_zero_of_pairwise_commute s f n hpow hcomm`, where
`hpow : ∀ i ∈ s, (f i) ^ n i = 0` and
`hcomm : (s : Set ι).Pairwise (fun i j => Commute (f i) (f j))`.
It yields the vanishing power at `1 + ∑ i ∈ s, (n i - 1)` without a common
exponent, positivity, or an externally supplied decidable equality instance.
The coefficient and index universes are independent. The hypotheses constrain only
indices in `s`; empty support and the zero semiring are included.

The aggregate module does not re-export every theory module; the imports above
select these interfaces explicitly. Character integration is available in
`GroupTheory.Topology.PontryaginDual.Integral`.

For finite orthogonal nonunital sums and the finite-product unital factory, import
`GroupTheory.Ring.Hom.FiniteSum` (also re-exported by `GroupTheory`).
`NonUnitalRingHom.sum s f h` uses mutual annihilation of the whole component
images on the finite support, with no unitality or associativity requirement.
`Pi.liftRingHom φ horth hone` instead has unital nonassociative component
semirings and an associative target semiring: the nonunital component maps'
unit images must annihilate in both orders and sum to one. Its application
formula needs no external decidable equality; the `Pi.single` extension,
uniqueness and equality-by-restrictions APIs use `[DecidableEq ι]`.
No coordinate-recovery or injectivity criterion for this lift is asserted here.

For whole compact-open dual transport, use `PontryaginDual.mapEquiv` from
`GroupTheory.Topology.PontryaginDual`: its direction reverses a continuous
multiplicative equivalence, with only monoids and topologies. The same module's
continuous `eval` and naturality retain the stated locally compact pair
hypotheses; transport itself does not require them. For injectivity of this
canonical evaluation on a discrete commutative group, explicitly import
`GroupTheory.Topology.PontryaginDual.Discrete` and use
`PontryaginDual.eval_injective_of_discrete G`. This is not a surjectivity or
full-reflexivity interface, nor a change to the original character topology.

For power divisibility from `a ∣ c` and `Commute a c` in a monoid, import
`GroupTheory.Algebra.Divisibility.Basic` and use
`Commute.pow_dvd_pow_of_dvd hcomm hdvd n` for any natural `n`.
`GroupTheory.Algebra.GroupWithZero.Nilpotent` supplies
`Commute.nilpotencyClass_le_of_dvd` and `Commute.nilpotencyClass_mul_le_left`
when the chosen divisor or factor is nilpotent. For the list bound, import
`GroupTheory.Algebra.BigOperators.GroupWithZero.List` and use
`List.nilpotencyClass_prod_le_of_mem`: it needs membership of the chosen
nilpotent entry and its commutation with every entry, not pairwise commutation
of all other entries or their nilpotence. These direct imports select the new
interfaces; no aggregate re-export is promised.

For a generator map `σ : I → J`, `FreeGroup.ker_map σ` in
`GroupTheory.FreeGroup.Map` gives the kernel as a normal closure of equal-label
generator differences, even when `σ` is not surjective. The same module supplies
`FreeGroup.map_injective_iff` and `FreeGroup.map_surjective_iff`.
