/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Coordinates
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Finite-coordinate factorization into groups with no small subgroups

A homomorphism from a product of groups to a group with no small subgroups,
continuous at the identity, kills the subgroup whose coordinates are one on some
finite set. The product has its pointwise group structure and the product topology;
no continuity of the group operations is needed.

For products of unital magmas, continuity at the identity has the same whole-tail
conclusion if inversion in the target is continuous at the identity. In this case
the canonical finite-coordinate factor is continuous at the identity; global
continuity of the homomorphism or of its factor is not assumed.

Composing a homomorphism with extension by the identity gives finite-factor data
for products of unital magmas and unital-magma targets, without any topological
assumptions. If the whole complementary tail is killed, composing this factor with
coordinate restriction recovers the original homomorphism. The factor is unique for
the fixed set of coordinates. With arbitrary topologies, global continuity of the
homomorphism makes the factor continuous; no continuity of the operations is needed.

For products of unital magmas, global continuity and continuity of the fixed left
translations in the target give a different sufficient condition for finite
coordinate support. The whole tail is then killed using the T₀ consequence of no
small subgroups and continuous left translations. Neither source associativity nor
continuity of any source operation is required. These results do not replace the
continuous-at-identity results for products of groups.

The diagonal finite-support argument compares finite cylinders at the identity
and at a chosen product element. The truncation argument uses both specialization
directions, rather than uniqueness of limits in a T₀ space. The constructions and
finite truncation comparisons follow the product homomorphism formalizations by
Formal Frontier Agents and Mathlib.
-/

@[expose] public section

open Set Filter
open scoped Topology

universe u v w

variable {ι : Type u} {G : ι → Type v} {D : Type w}

attribute [local instance] Classical.propDecidable

private theorem exists_finset_agreement_subset [∀ i, TopologicalSpace (G i)]
    {x : ∀ i, G i} {U : Set (∀ i, G i)} (hU : U ∈ 𝓝 x) :
    ∃ s : Finset ι, ∀ y : ∀ i, G i, (∀ i ∈ s, y i = x i) → y ∈ U := by
  rw [nhds_pi] at hU
  obtain ⟨s, V, hV, hVU⟩ := Filter.mem_pi'.mp hU
  refine ⟨s, fun y hy => hVU ?_⟩
  intro i hi
  rw [hy i hi]
  exact mem_of_mem_nhds (hV i)

namespace MonoidHom

section MulOneClass

variable [∀ i, MulOneClass (G i)] [MulOneClass D]

/-- The finite-coordinate factor obtained by extending by the identity and then
applying the given homomorphism. -/
noncomputable def finiteCoordinateFactor (f : (∀ i, G i) →* D) (s : Finset ι) :
    (∀ i : {i // i ∈ s}, G i) →* D :=
  { toFun := fun x => f (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1)
    map_one' := by
      have h : (fun i => if hi : i ∈ s then
          (1 : ∀ j : {i // i ∈ s}, G j) ⟨i, hi⟩ else 1) = (1 : ∀ i, G i) := by
        funext i
        simp
      rw [h]
      exact map_one f
    map_mul' := by
      intro x y
      have h : (fun i => if hi : i ∈ s then (x * y) ⟨i, hi⟩ else 1) =
          (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1) *
            (fun i => if hi : i ∈ s then y ⟨i, hi⟩ else 1) := by
        funext i
        by_cases hi : i ∈ s <;> simp [hi]
      rw [h]
      exact map_mul f
        (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1)
        (fun i => if hi : i ∈ s then y ⟨i, hi⟩ else 1) }

@[simp]
theorem finiteCoordinateFactor_apply (f : (∀ i, G i) →* D) (s : Finset ι)
    (x : ∀ i : {i // i ∈ s}, G i) :
    f.finiteCoordinateFactor s x =
      f (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1) := rfl

universe z

/-- Taking a finite-coordinate factor commutes with postcomposition by a
homomorphism. -/
theorem finiteCoordinateFactor_comp {E : Type z} [MulOneClass E]
    (f : D →* E) (g : (∀ i, G i) →* D) (s : Finset ι) :
    (f.comp g).finiteCoordinateFactor s = f.comp (g.finiteCoordinateFactor s) := by
  apply DFunLike.ext
  intro x
  simp only [finiteCoordinateFactor_apply, comp_apply]

/-- A factor through a fixed coordinate restriction is necessarily the
finite-coordinate factor obtained by extension by the identity. -/
theorem finiteCoordinateFactor_unique (f : (∀ i, G i) →* D) (s : Finset ι)
    (g : (∀ i : {i // i ∈ s}, G i) →* D)
    (hg : ∀ x : ∀ i, G i, f x = g (fun i => x i)) :
    g = f.finiteCoordinateFactor s := by
  apply DFunLike.ext
  intro x
  rw [finiteCoordinateFactor_apply]
  have hx := hg (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1)
  have he : (fun i : {i // i ∈ s} =>
      if hi : (i : ι) ∈ s then x ⟨i, hi⟩ else 1) = x := by
    funext i
    simp only [dite_eq_left i.property]
  simpa only [he] using hx.symm

/-- Pointwise annihilation of the whole tail suffices for the canonical factor
to recover the homomorphism. Only the unit laws are needed in source and target. -/
theorem finiteCoordinateFactor_restrict_of_eq_one (f : (∀ i, G i) →* D)
    (s : Finset ι) (hs : ∀ z : ∀ i, G i, (∀ i ∈ s, z i = 1) → f z = 1)
    (x : ∀ i, G i) : f.finiteCoordinateFactor s (fun i => x i) = f x := by
  rw [finiteCoordinateFactor_apply]
  let y : ∀ i, G i := fun i => if hi : i ∈ s then
    (fun j : {i // i ∈ s} => x j) ⟨i, hi⟩ else 1
  let z : ∀ i, G i := fun i => if i ∈ s then 1 else x i
  have hz : f z = 1 := hs z (by
    intro i hi
    simp [z, hi])
  have he : x = y * z := by
    funext i
    by_cases hi : i ∈ s <;> simp [y, z, hi]
  have hm : f x = f y := by
    calc
      f x = f (y * z) := congrArg f he
      _ = f y * f z := map_mul f _ _
      _ = f y := by rw [hz, mul_one]
  exact hm.symm

/-- Function factorization through a fixed coordinate restriction, from pointwise
annihilation of its entire complementary tail. -/
theorem eq_finiteCoordinateFactor_comp_restrict_of_eq_one
    (f : (∀ i, G i) →* D) (s : Finset ι)
    (hs : ∀ z : ∀ i, G i, (∀ i ∈ s, z i = 1) → f z = 1) :
    (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  funext x
  exact (f.finiteCoordinateFactor_restrict_of_eq_one s hs x).symm

section Topology

variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace D]

/-- The finite-coordinate factor of a continuous homomorphism is continuous for
the product topologies, without continuity of any source or target operation. -/
theorem continuous_finiteCoordinateFactor (f : (∀ i, G i) →* D) (hf : Continuous f)
    (s : Finset ι) : Continuous (f.finiteCoordinateFactor s) :=
  hf.comp (by
    apply continuous_pi
    intro i
    by_cases hi : i ∈ s
    · simpa only [dite_eq_left hi] using
        (continuous_apply (⟨i, hi⟩ : {i // i ∈ s}))
    · simpa only [dite_eq_right hi] using
        (continuous_const :
          Continuous (fun _ : ∀ j : {i // i ∈ s}, G j => (1 : G i))))

/-- The finite-coordinate factor of a homomorphism continuous at the identity
is continuous at the identity for the product topologies. -/
theorem continuousAt_one_finiteCoordinateFactor (f : (∀ i, G i) →* D)
    (hf : ContinuousAt f (1 : ∀ i, G i)) (s : Finset ι) :
    ContinuousAt (f.finiteCoordinateFactor s)
      (1 : ∀ i : {i // i ∈ s}, G i) := by
  have hfactor :
      f.finiteCoordinateFactor s =
        f.comp ((MonoidHom.id (∀ i, G i)).finiteCoordinateFactor s) := by
    simpa only [comp_id] using
      (finiteCoordinateFactor_comp f (MonoidHom.id (∀ i, G i)) s)
  rw [hfactor]
  have he : Continuous ((MonoidHom.id (∀ i, G i)).finiteCoordinateFactor s) :=
    continuous_finiteCoordinateFactor (MonoidHom.id (∀ i, G i)) continuous_id s
  have hf' : ContinuousAt f
      ((MonoidHom.id (∀ i, G i)).finiteCoordinateFactor s 1) := by
    simpa only [map_one] using hf
  exact hf'.comp he.continuousAt

end Topology

end MulOneClass

private theorem exists_inv_apply_not_mem {M : Type v} [MulOneClass M]
    [Group D] (h : M →* D) {U : Set D}
    (hsub : ∀ H : Subgroup D, (H : Set D) ⊆ U → H = ⊥)
    (himage : ∀ a, h a ∈ U) (hne : ∃ a, h a ≠ 1) :
    ∃ b, (h b)⁻¹ ∉ U := by
  classical
  by_contra hb
  push Not at hb
  obtain ⟨a, ha⟩ := hne
  -- Positive target powers have source preimages, without source powers.
  have hpow : ∀ n : ℕ, ∃ b, h b = h a ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, by simp⟩
    | succ n ih =>
        obtain ⟨b, hb⟩ := ih
        exact ⟨b * a, by rw [map_mul, hb, pow_succ]⟩
  have hZ : (Subgroup.zpowers (h a) : Set D) ⊆ U := by
    intro d hd
    rcases Subgroup.mem_zpowers_iff.mp hd with ⟨n, rfl⟩
    cases n with
    | ofNat n =>
        obtain ⟨b, he⟩ := hpow n
        have hNat : h a ^ n ∈ U := he ▸ himage b
        have hInt : h a ^ Int.ofNat n = h a ^ n := zpow_natCast (h a) n
        exact hInt.symm ▸ hNat
    | negSucc n =>
        obtain ⟨b, he⟩ := hpow (n + 1)
        simpa only [zpow_negSucc, ← he] using hb b
  have hbot := hsub (Subgroup.zpowers (h a)) hZ
  have haZ : h a ∈ Subgroup.zpowers (h a) :=
    Subgroup.mem_zpowers_iff.mpr ⟨(1 : ℤ), by simp⟩
  exact ha (Subgroup.mem_bot.mp (hbot ▸ haZ))

section ContinuousConstSMul

variable [∀ i, MulOneClass (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [TopologicalSpace D] [ContinuousConstSMul D D] [NoSmallSubgroups D]

/-- Only finitely many coordinate homomorphisms of a globally continuous product
homomorphism are nontrivial. The source needs only the unit laws. On the target,
`ContinuousConstSMul D D` refers to the canonical group self-action, so only fixed
left multiplication is assumed continuous. -/
theorem finite_mulSupport_coordinateHom (f : (∀ i, G i) →* D) (hf : Continuous f) :
    ({i : ι | f.coordinateHom i ≠ 1} : Set ι).Finite := by
  classical
  obtain ⟨W, hW, hsub⟩ := (noSmallSubgroups_iff (G := D)).mp inferInstance
  obtain ⟨U, hUW, hU, hU1⟩ := mem_nhds_iff.mp hW
  have hUsub : ∀ H : Subgroup D, (H : Set D) ⊆ U → H = ⊥ :=
    fun H hH => hsub H (hH.trans hUW)
  have hpre : f ⁻¹' U ∈ 𝓝 (1 : ∀ i, G i) :=
    hf.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU.mem_nhds hU1)
  obtain ⟨C, hC⟩ := exists_finset_agreement_subset hpre
  have hcoeff : ∀ i, i ∉ C → ∀ a : G i, f.coordinateHom i a ∈ U := by
    intro i hi a
    rw [coordinateHom_apply]
    apply hC
    intro j hj
    have hji : j ≠ i := by
      intro he
      subst j
      exact hi hj
    simp [hji]
  let A : ι → Prop := fun i => i ∉ C ∧ f.coordinateHom i ≠ 1
  have hex : ∀ i, A i → ∃ b : G i, (f.coordinateHom i b)⁻¹ ∉ U := by
    intro i hi
    apply exists_inv_apply_not_mem (f.coordinateHom i) hUsub (hcoeff i hi.1)
    obtain ⟨a, ha⟩ := (coordinateHom_ne_one_iff f i).mp hi.2
    exact ⟨a, by simpa only [coordinateHom_apply] using ha⟩
  let b : ∀ i, G i := fun i => if hi : A i then Classical.choose (hex i hi) else 1
  have hb : ∀ i, A i → (f.coordinateHom i (b i))⁻¹ ∉ U := by
    intro i hi
    simpa only [b, dite_eq_left hi] using Classical.choose_spec (hex i hi)
  let V : Set D := (fun y : D => (f b)⁻¹ * y) ⁻¹' U
  have hleft : Continuous (fun y : D => (f b)⁻¹ * y) :=
    (continuous_const_smul ((f b)⁻¹) : Continuous (fun y : D => (f b)⁻¹ • y))
  have hV : IsOpen V := hU.preimage hleft
  have hVb : f b ∈ V := by
    change (f b)⁻¹ * f b ∈ U
    simpa using hU1
  obtain ⟨B, hB⟩ := exists_finset_agreement_subset
    (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hVb))
  apply (C ∪ B).finite_toSet.subset
  intro i hi
  by_contra his
  have hiC : i ∉ C := fun h => his (Finset.mem_union.mpr (Or.inl h))
  have hiB : i ∉ B := fun h => his (Finset.mem_union.mpr (Or.inr h))
  let c : ∀ j, G j := fun j => if j = i then 1 else b j
  have hc : f c ∈ V := by
    apply hB
    intro j hj
    have hji : j ≠ i := by
      intro he
      subst j
      exact hiB hj
    simp [c, hji]
  have hbc : b = c * Pi.mulSingle i (b i) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [c]
    · simp [c, hji]
  have hfb : f b = f c * f (Pi.mulSingle i (b i)) := by
    calc
      f b = f (c * Pi.mulSingle i (b i)) := congrArg f hbc
      _ = f c * f (Pi.mulSingle i (b i)) := map_mul f _ _
  have he : (f b)⁻¹ * f c = (f.coordinateHom i (b i))⁻¹ := by
    rw [coordinateHom_apply, hfb, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  apply hb i ⟨hiC, hi⟩
  change (f b)⁻¹ * f c ∈ U at hc
  rw [he] at hc
  exact hc

/-- Under no small subgroups and continuous fixed left translations, a globally
continuous product homomorphism kills an entire finite-coordinate tail. -/
theorem exists_finset_eq_one_of_coordinates_eq_one_of_continuousConstSMul
    (f : (∀ i, G i) →* D) (hf : Continuous f) :
    ∃ s : Finset ι, ∀ x : ∀ i, G i, (∀ i ∈ s, x i = 1) → f x = 1 := by
  have hfinite := f.finite_mulSupport_coordinateHom hf
  let s := hfinite.toFinset
  refine ⟨s, f.eq_one_of_coordinates_eq_one hf s ?_⟩
  intro i hi
  by_contra hfi
  apply hi
  simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hfi

/-- A globally continuous homomorphism from a product of unital magmas factors
through a finite subproduct when the target has no small subgroups and continuous
fixed left multiplication. The continuous factor is unique for that restriction. -/
theorem exists_finset_factor_of_continuousConstSMul
    (f : (∀ i, G i) →* D) (hf : Continuous f) :
    ∃ s : Finset ι, ∃! g : (∀ i : {i // i ∈ s}, G i) →* D,
      Continuous g ∧ ∀ x : ∀ i, G i, f x = g (fun i => x i) := by
  obtain ⟨s, hs⟩ :=
    f.exists_finset_eq_one_of_coordinates_eq_one_of_continuousConstSMul hf
  refine ⟨s, f.finiteCoordinateFactor s,
    ⟨f.continuous_finiteCoordinateFactor hf s,
      fun x => (f.finiteCoordinateFactor_restrict_of_eq_one s hs x).symm⟩, ?_⟩
  intro g hg
  exact f.finiteCoordinateFactor_unique s g hg.2

end ContinuousConstSMul

end MonoidHom

section MulOneClass

variable [∀ i, MulOneClass (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [TopologicalSpace D]

/-- A homomorphism from a product of unital magmas, continuous at the identity,
is one on every element that is one on a suitable finite set of coordinates,
provided the target has no small subgroups and inversion is continuous at the
identity. The coordinates outside that finite set are unrestricted. -/
theorem MonoidHom.exists_finset_eq_one_of_coordinates_eq_one_of_continuousAt_inv
    [NoSmallSubgroups D] (f : (∀ i, G i) →* D) (hf : ContinuousAt f 1)
    (hinv : ContinuousAt (fun d : D => d⁻¹) (1 : D)) :
    ∃ s : Finset ι, ∀ x : ∀ i, G i, (∀ i ∈ s, x i = 1) → f x = 1 := by
  obtain ⟨U, hU, hUsub⟩ := (noSmallSubgroups_iff_submonoid hinv).mp inferInstance
  have hpre : f ⁻¹' U ∈ 𝓝 (1 : ∀ i, G i) :=
    hf.preimage_mem_nhds (by simpa only [map_one] using hU)
  obtain ⟨s, hs⟩ := exists_finset_agreement_subset hpre
  let S : Submonoid (∀ i, G i) :=
    { carrier := {x | ∀ i ∈ s, x i = 1}
      one_mem' := by
        intro i _
        rfl
      mul_mem' := by
        intro x y hx hy i hi
        change x i * y i = 1
        rw [hx i hi, hy i hi, one_mul] }
  have hmap : S.map f = ⊥ := hUsub _ (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submonoid.mem_map.mp hy
    exact hs x hx)
  refine ⟨s, ?_⟩
  intro x hx
  have hmem : f x ∈ S.map f := Submonoid.mem_map_of_mem f hx
  exact Submonoid.mem_bot.mp (hmap ▸ hmem)

/-- A homomorphism from a product of unital magmas, continuous at the identity,
factors through its canonical finite-coordinate factor, which is continuous at the
identity, if the target has no small subgroups and inversion is continuous there. -/
theorem MonoidHom.exists_finset_factor_of_continuousAt_inv
    [NoSmallSubgroups D] (f : (∀ i, G i) →* D) (hf : ContinuousAt f 1)
    (hinv : ContinuousAt (fun d : D => d⁻¹) (1 : D)) :
    ∃ s : Finset ι,
      ContinuousAt (f.finiteCoordinateFactor s) (1 : ∀ i : {i // i ∈ s}, G i) ∧
        ∀ x : ∀ i, G i, f x = f.finiteCoordinateFactor s (fun i => x i) := by
  obtain ⟨s, hs⟩ :=
    f.exists_finset_eq_one_of_coordinates_eq_one_of_continuousAt_inv hf hinv
  exact ⟨s, f.continuousAt_one_finiteCoordinateFactor hf s,
    fun x => (f.finiteCoordinateFactor_restrict_of_eq_one s hs x).symm⟩

end MulOneClass

namespace ContinuousMonoidHom

section Monoid

variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]

/-- The finite-coordinate factor obtained by extending by the identity and then
applying the given continuous homomorphism. -/
noncomputable def finiteCoordinateFactor (f : (∀ i, G i) →ₜ* D) (s : Finset ι) :
    (∀ i : {i // i ∈ s}, G i) →ₜ* D :=
  { toMonoidHom := f.toMonoidHom.finiteCoordinateFactor s
    continuous_toFun :=
      f.toMonoidHom.continuous_finiteCoordinateFactor f.continuous s }

@[simp]
theorem finiteCoordinateFactor_apply (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (x : ∀ i : {i // i ∈ s}, G i) :
    f.finiteCoordinateFactor s x =
      f (fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 1) := rfl

/-- A factor through a fixed coordinate restriction is necessarily the
finite-coordinate factor obtained by extension by the identity. -/
theorem finiteCoordinateFactor_unique (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (g : (∀ i : {i // i ∈ s}, G i) →ₜ* D)
    (hg : ∀ x : ∀ i, G i, f x = g (fun i => x i)) :
    g = f.finiteCoordinateFactor s := by
  have h := f.toMonoidHom.finiteCoordinateFactor_unique s g.toMonoidHom hg
  apply DFunLike.ext
  intro x
  exact congrArg (fun k : (∀ i : {i // i ∈ s}, G i) →* D => k x) h

/-- Pointwise annihilation of the whole tail suffices for the canonical factor
to recover the homomorphism. No source inverses are needed. -/
theorem finiteCoordinateFactor_restrict_of_eq_one (f : (∀ i, G i) →ₜ* D)
    (s : Finset ι) (hs : ∀ z : ∀ i, G i, (∀ i ∈ s, z i = 1) → f z = 1)
    (x : ∀ i, G i) : f.finiteCoordinateFactor s (fun i => x i) = f x :=
  f.toMonoidHom.finiteCoordinateFactor_restrict_of_eq_one s hs x

/-- Function factorization through a fixed coordinate restriction, from pointwise
annihilation of its entire complementary tail. -/
theorem eq_finiteCoordinateFactor_comp_restrict_of_eq_one
    (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (hs : ∀ z : ∀ i, G i, (∀ i ∈ s, z i = 1) → f z = 1) :
    (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) :=
  f.toMonoidHom.eq_finiteCoordinateFactor_comp_restrict_of_eq_one s hs

end Monoid

section ContinuousConstSMul

variable [∀ i, Monoid (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [TopologicalSpace D] [ContinuousConstSMul D D] [NoSmallSubgroups D]

/-- Only finitely many continuous coordinate restrictions are nontrivial, under
continuous fixed left multiplication in the target. -/
theorem finite_mulSupport_coordinateHom_of_continuousConstSMul
    (f : (∀ i, G i) →ₜ* D) :
    ({i : ι | f.coordinateHom i ≠ 1} : Set ι).Finite := by
  apply (f.toMonoidHom.finite_mulSupport_coordinateHom f.continuous).subset
  intro i hi he
  apply hi
  apply DFunLike.ext
  intro a
  change f.coordinateHom i a = 1
  rw [coordinateHom_apply]
  have ha := congrArg (fun g : G i →* D => g a) he
  change f.toMonoidHom.coordinateHom i a = 1 at ha
  rw [MonoidHom.coordinateHom_apply] at ha
  exact ha

/-- A continuous homomorphism from a product of monoids factors through a finite
subproduct when the target has no small subgroups and continuous fixed left
multiplications. The factor is unique for the fixed finite coordinate set. -/
theorem exists_finset_factor_of_continuousConstSMul (f : (∀ i, G i) →ₜ* D) :
    ∃ s : Finset ι, ∃! g : (∀ i : {i // i ∈ s}, G i) →ₜ* D,
      ∀ x : ∀ i, G i, f x = g (fun i => x i) := by
  obtain ⟨s, hs⟩ :=
    MonoidHom.exists_finset_eq_one_of_coordinates_eq_one_of_continuousConstSMul
      f.toMonoidHom f.continuous
  exact ⟨s, f.finiteCoordinateFactor s,
    fun x => (f.finiteCoordinateFactor_restrict_of_eq_one s hs x).symm,
    fun g hg => f.finiteCoordinateFactor_unique s g hg⟩

end ContinuousConstSMul

end ContinuousMonoidHom

section Group

variable [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Group D] [TopologicalSpace D]

/-- A homomorphism continuous at the identity into a group with no small subgroups
kills the subgroup whose coordinates are one on some finite set. -/
theorem MonoidHom.exists_finset_coordinateKernel_le_ker (f : (∀ i, G i) →* D)
    (hf : ContinuousAt f 1) [NoSmallSubgroups D] :
    ∃ s : Finset ι, Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.ker := by
  obtain ⟨U, hU, hUsub⟩ := (noSmallSubgroups_iff (G := D)).mp inferInstance
  have hpre : f ⁻¹' U ∈ 𝓝 (1 : ∀ i, G i) :=
    hf.preimage_mem_nhds (by simpa only [map_one] using hU)
  rw [nhds_pi] at hpre
  obtain ⟨s, V, hV, hVU⟩ := Filter.mem_pi'.mp hpre
  refine ⟨s, ?_⟩
  have hmap : (Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i)))).map f = ⊥ :=
    hUsub _ (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      apply hVU
      intro i hi
      have hxi : x i = 1 := Subgroup.mem_bot.mp (hx i hi)
      rw [hxi]
      exact mem_of_mem_nhds (hV i))
  intro x hx
  exact MonoidHom.mem_ker.mpr
    (Subgroup.mem_bot.mp (hmap ▸ Subgroup.mem_map_of_mem f hx))

/-- A homomorphism continuous at the identity into a group with no small subgroups
is one on every product element that is one on a suitable finite set of coordinates. -/
theorem MonoidHom.exists_finset_eq_one_of_coordinates_eq_one (f : (∀ i, G i) →* D)
    (hf : ContinuousAt f 1) [NoSmallSubgroups D] :
    ∃ s : Finset ι, ∀ x : ∀ i, G i, (∀ i ∈ s, x i = 1) → f x = 1 := by
  obtain ⟨s, hs⟩ := f.exists_finset_coordinateKernel_le_ker hf
  refine ⟨s, fun x hx => MonoidHom.mem_ker.mp (hs ?_)⟩
  intro i hi
  exact Subgroup.mem_bot.mpr (hx i hi)

namespace ContinuousMonoidHom

/-- If a continuous homomorphism kills a coordinate kernel, its finite-coordinate
factor recovers it after restriction to those coordinates. -/
theorem finiteCoordinateFactor_restrict (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (hs : Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.toMonoidHom.ker)
    (x : ∀ i, G i) : f.finiteCoordinateFactor s (fun i => x i) = f x := by
  apply f.finiteCoordinateFactor_restrict_of_eq_one s ?_ x
  intro z hz
  apply MonoidHom.mem_ker.mp
  apply hs
  intro i hi
  exact Subgroup.mem_bot.mpr (hz i hi)

/-- Factorization as an equality of functions through the coordinate restriction. -/
theorem eq_finiteCoordinateFactor_comp_restrict (f : (∀ i, G i) →ₜ* D) (s : Finset ι)
    (hs : Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i))) ≤ f.toMonoidHom.ker) :
    (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  funext x
  exact (f.finiteCoordinateFactor_restrict s hs x).symm

/-- A continuous homomorphism from a product to a group with no small subgroups
factors through some finite coordinate restriction, uniquely for that restriction. -/
theorem exists_finset_factor (f : (∀ i, G i) →ₜ* D) [NoSmallSubgroups D] :
    ∃ s : Finset ι, ∃! g : (∀ i : {i // i ∈ s}, G i) →ₜ* D,
      ∀ x : ∀ i, G i, f x = g (fun i => x i) := by
  obtain ⟨s, hs⟩ :=
    f.toMonoidHom.exists_finset_coordinateKernel_le_ker f.continuous.continuousAt
  exact ⟨s, f.finiteCoordinateFactor s,
    fun x => (f.finiteCoordinateFactor_restrict s hs x).symm,
    fun g hg => f.finiteCoordinateFactor_unique s g hg⟩

end ContinuousMonoidHom

end Group
