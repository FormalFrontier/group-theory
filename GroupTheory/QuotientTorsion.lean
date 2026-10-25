/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.QuotientGroup.Kernel

/-!
# Torsion in additive quotients

For an additive commutative group `V`, if multiplication by `n` is bijective,
then `(V / L)[n] ≃+ L / nL`. The `n`-torsion group is the kernel of
`nsmulAddMonoidHom n`, and `nL` is the range of that homomorphism on `L`;
no new torsion or quotient carrier is introduced. No topology, lattice,
finiteness, freeness or divisibility at other scalars is needed. There is no
`n ≠ 0` premise: the bijectivity premise permits `n = 0` exactly when `V`
is trivial, and always permits `n = 1`.

For a complex vector space, multiplication by a positive integer is invertible
with inverse multiplication by its reciprocal. Taking an additive lattice `L`
therefore recovers the algebraic identification `n⁻¹L / L ≃+ L / nL` behind
Milne's complex-torus calculation. The lattice's topological and finite-rank
properties are used for further conclusions, not for this identification.

For `n = m * d`, the scalar-transition identity says that the equivalence
intertwines multiplication by `d` on torsion with reduction `L / nL → L / mL`.
It uses the quotient map and the restriction of the scalar map to kernels.
Bijectivity at `n` already implies bijectivity at `m`.

The construction specializes `QuotientAddGroup.kerMapEquivQuotientOfEquiv`.
Its underlying homomorphism `ψ : L →+ V ⧸ L` sends `l` to the quotient class
of its unique `n`-division in `V`. Mathlib's first isomorphism theorem identifies
`L / ker ψ` with `range ψ`; the kernel is `nL`, and the range is the `n`-torsion
of `V / L`. Inverting this comparison gives the positive representative formula
`[x] ↦ [n • x]`. The induced quotient map and the subgroup of multiples are
identified with the usual scalar homomorphism and its range.

The snake lemma applied to multiplication by `n` on `L → V → V / L` gives
another description: bijectivity makes the middle vertical kernel and cokernel
zero, so the connecting morphism is invertible. The direct first-isomorphism
construction needs no integer-module or categorical comparison objects.

## References

* J. S. Milne, *Abelian Varieties*, version 2.0 (2008), I.10, Remark 10.7,
  p. 45, for the complex-torus application.
* Mathlib's `QuotientAddGroup.quotientKerEquivRange` for the first isomorphism
  theorem, specialized by `QuotientAddGroup.kerMapEquivQuotientOfEquiv` with
  the canonical kernel/range identifications.
* Joël Riou, Mathlib's `Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean`,
  for the snake-lemma formalization approach used in the original construction,
  its connecting morphism and positive-sign characteristic equation.
-/

@[expose] public section

universe u

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V] (L : AddSubgroup V) (n : ℕ)

/-- The quotient map induced by multiplication by `n` is multiplication by `n`
on the quotient. -/
theorem map_nsmulAddMonoidHom :
    map L L (nsmulAddMonoidHom (α := V) n)
      (by intro x hx; exact L.nsmul_mem hx n) =
        nsmulAddMonoidHom (α := V ⧸ L) n := by
  apply addMonoidHom_ext
  ext x
  simpa only [AddMonoidHom.comp_apply, mk'_apply, map_mk, nsmulAddMonoidHom_apply] using
    mk_nsmul L x n

variable (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n))

/-- The `n`-torsion of `V / L` is canonically `L / nL` when multiplication by
`n` is bijective on `V`. On representatives the equivalence sends `[x]`
to `[n • x]`, and its inverse sends `[l]` to the class of the unique
`n`-division of `l` in `V`. This is the additive quotient identification used
in Milne, *Abelian Varieties*, I.10, Remark 10.7. -/
@[no_expose] noncomputable def nsmulTorsionEquivQuotient
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    (nsmulAddMonoidHom (α := V ⧸ L) n).ker ≃+
      L ⧸ (nsmulAddMonoidHom (α := L) n).range := by
  exact (AddEquiv.addSubgroupCongr
    (congrArg AddMonoidHom.ker (map_nsmulAddMonoidHom L n).symm)).trans
    ((kerMapEquivQuotientOfEquiv L L
      (AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn)
      (AddSubgroup.map_le_iff_le_comap.mpr
        (by intro x hx; exact L.nsmul_mem hx n))).trans
      (quotientAddEquivOfEq
        (AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range L n)))

/-- A torsion class represented by `x` maps to the class of `n • x` in `L / nL`. -/
@[simp] theorem nsmulTorsionEquivQuotient_apply_mk (x : V) (hx : n • x ∈ L) :
    nsmulTorsionEquivQuotient L n hn
        ⟨(x : V ⧸ L), by simpa using (eq_zero_iff (n • x)).mpr hx⟩ =
      (⟨n • x, hx⟩ : L) := by
  let f := AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn
  let h : L.map (f : V →+ V) ≤ L :=
    AddSubgroup.map_le_iff_le_comap.mpr (by intro y hy; exact L.nsmul_mem hy n)
  -- The kernel congruence preserves the underlying quotient representative.
  change quotientAddEquivOfEq
      (AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range L n)
      (kerMapEquivQuotientOfEquiv L L f h
        ⟨(x : V ⧸ L), by
          change ((f x : V) : V ⧸ L) = 0
          exact (eq_zero_iff (f x)).mpr hx⟩) =
    (⟨n • x, hx⟩ : L)
  rw [kerMapEquivQuotientOfEquiv_apply_mk L L f h x hx]
  rfl

/-- The inverse sends `[l]` to its unique `n`-division class in `V / L`. -/
@[simp] theorem nsmulTorsionEquivQuotient_symm_apply_mk (l : L) :
    ((nsmulTorsionEquivQuotient L n hn).symm
      (l : L ⧸ (nsmulAddMonoidHom (α := L) n).range) : V ⧸ L) =
        ((AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn).symm
          (l : V) : V) := by
  let x := (AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn).symm (l : V)
  have hx : n • x = (l : V) :=
    (AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn).apply_symm_apply _
  have hxL : n • x ∈ L := hx ▸ l.property
  have hl : (⟨n • x, hxL⟩ : L) = l := Subtype.ext hx
  have h := nsmulTorsionEquivQuotient_apply_mk L n hn x hxL
  rw [hl] at h
  have h' := congrArg (nsmulTorsionEquivQuotient L n hn).symm h
  simpa using congrArg
    (fun y : (nsmulAddMonoidHom (α := V ⧸ L) n).ker => (y : V ⧸ L)) h'.symm

end QuotientAddGroup

namespace AddMonoidHom

variable {A : Type u}

/-- Bijectivity of a product scalar implies bijectivity of its first factor. -/
theorem nsmul_bijective_of_mul [AddCommMonoid A] (m d : ℕ)
    (hmd : Function.Bijective (nsmulAddMonoidHom (α := A) (m * d))) :
    Function.Bijective (nsmulAddMonoidHom (α := A) m) := by
  constructor
  · intro a b hab
    apply hmd.1
    change (m * d) • a = (m * d) • b
    simpa only [mul_nsmul, nsmulAddMonoidHom_apply] using congrArg (fun x : A => d • x) hab
  · intro y
    obtain ⟨x, hx⟩ := hmd.2 y
    exact ⟨d • x, by simpa only [nsmulAddMonoidHom_apply, mul_nsmul'] using hx⟩

/-- Multiples of a product scalar are multiples of its first factor. -/
theorem range_nsmul_mul_le [AddCommGroup A] (m d : ℕ) :
    (nsmulAddMonoidHom (α := A) (m * d)).range ≤
      (nsmulAddMonoidHom (α := A) m).range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨d • x, (mul_nsmul' x m d).symm⟩

/-- Multiplication by `d` takes `(m * d)`-torsion to `m`-torsion. -/
theorem nsmul_mapsTo_ker [AddCommGroup A] (m d : ℕ) :
    Set.MapsTo (nsmulAddMonoidHom (α := A) d)
      (nsmulAddMonoidHom (α := A) (m * d)).ker
      (nsmulAddMonoidHom (α := A) m).ker := by
  intro x hx
  change (m * d) • x = 0 at hx
  change m • (d • x) = 0
  simpa only [mul_nsmul'] using hx

end AddMonoidHom

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V] (L : AddSubgroup V) (n : ℕ)

/-- The quotient-torsion equivalence is the quotient-map kernel equivalence for
multiplication by `n`, after identifying the induced map and the subgroup of multiples. -/
theorem nsmulTorsionEquivQuotient_eq_kerMapEquivQuotientOfEquiv
    (hn : Function.Bijective (nsmulAddMonoidHom (α := V) n)) :
    nsmulTorsionEquivQuotient L n hn =
      (AddEquiv.addSubgroupCongr
        (congrArg AddMonoidHom.ker (map_nsmulAddMonoidHom L n).symm)).trans
        ((kerMapEquivQuotientOfEquiv L L
          (AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) n) hn)
          (AddSubgroup.map_le_iff_le_comap.mpr
            (by intro x hx; exact L.nsmul_mem hx n))).trans
          (quotientAddEquivOfEq
            (AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range L n))) := by
  rfl

end QuotientAddGroup

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V]

/-- The quotient-torsion equivalences commute with scalar-divisibility transitions.
For `n = m * d`, multiplication by `d` on `(V / L)[n]` corresponds to
reduction `L / nL → L / mL`. Only bijectivity at `n` is assumed; bijectivity
at `m` follows from the commuting scalar factors. The two arrows below are
`QuotientAddGroup.map` and `AddMonoidHom.restrict` on their usual carriers.
No positivity hypothesis is needed: a zero product forces `V` to be trivial. -/
theorem nsmulTorsionEquivQuotient_naturality (L : AddSubgroup V) (m d : ℕ)
    (hmd : Function.Bijective (nsmulAddMonoidHom (α := V) (m * d))) :
    let reduction : (L ⧸ (nsmulAddMonoidHom (α := L) (m * d)).range) →+
        L ⧸ (nsmulAddMonoidHom (α := L) m).range :=
      map _ _ (AddMonoidHom.id L) (by
        simpa only [AddSubgroup.comap_id] using
          AddMonoidHom.range_nsmul_mul_le (A := L) m d)
    let torsionMap : (nsmulAddMonoidHom (α := V ⧸ L) (m * d)).ker →+
        (nsmulAddMonoidHom (α := V ⧸ L) m).ker :=
      AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker m d)
    reduction.comp (nsmulTorsionEquivQuotient L (m * d) hmd).toAddMonoidHom =
      (nsmulTorsionEquivQuotient L m
        (AddMonoidHom.nsmul_bijective_of_mul m d hmd)).toAddMonoidHom.comp torsionMap := by
  let hm := AddMonoidHom.nsmul_bijective_of_mul m d hmd
  let f := AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) (m * d)) hmd
  let f' := AddEquiv.ofBijective (nsmulAddMonoidHom (α := V) m) hm
  -- Match the kernel API's coercion view throughout the dependent map and carrier types.
  let h : L.map (f : V →+ V) ≤ L :=
    AddSubgroup.map_le_iff_le_comap.mpr (by intro v hv; exact L.nsmul_mem hv (m * d))
  let h' : L.map (f' : V →+ V) ≤ L :=
    AddSubgroup.map_le_iff_le_comap.mpr (by intro v hv; exact L.nsmul_mem hv m)
  let c := AddEquiv.addSubgroupCongr
    (congrArg AddMonoidHom.ker (map_nsmulAddMonoidHom L (m * d)).symm)
  let c' := AddEquiv.addSubgroupCongr
    (congrArg AddMonoidHom.ker (map_nsmulAddMonoidHom L m).symm)
  let e := quotientAddEquivOfEq
    (AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range L (m * d))
  let e' := quotientAddEquivOfEq
    (AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range L m)
  let reduction : (L ⧸ (nsmulAddMonoidHom (α := L) (m * d)).range) →+
      L ⧸ (nsmulAddMonoidHom (α := L) m).range :=
    map _ _ (AddMonoidHom.id L) (by
      simpa only [AddSubgroup.comap_id] using
        AddMonoidHom.range_nsmul_mul_le (A := L) m d)
  let torsionMap := AddMonoidHom.restrict (AddMonoidHom.nsmul_mapsTo_ker (A := V ⧸ L) m d)
  let kernelMap : (map L L (f : V →+ V) (AddSubgroup.map_le_iff_le_comap.mp h)).ker →+
      (map L L (f' : V →+ V) (AddSubgroup.map_le_iff_le_comap.mp h')).ker :=
    AddMonoidHom.restrict (f := map L L (nsmulAddMonoidHom (α := V) d)
      (by intro v hv; exact L.nsmul_mem hv d)) (by
        have hf : (f : V →+ V) =
            nsmulAddMonoidHom (α := V) (m * d) := rfl
        have hf' : (f' : V →+ V) =
            nsmulAddMonoidHom (α := V) m := rfl
        simpa only [hf, hf', map_nsmulAddMonoidHom,
          AddSubgroup.coe_toAddSubmonoid] using
          AddMonoidHom.nsmul_mapsTo_ker (A := V ⧸ L) m d)
  have hcomm : ∀ v : V, f' (nsmulAddMonoidHom d v) = (AddMonoidHom.id V) (f v) :=
    fun v => (mul_nsmul' v m d).symm
  let subgroupMap : L →+ L :=
    AddMonoidHom.restrict (f := AddMonoidHom.id V) (by intro v hv; exact hv)
  let latticeMap := map ((L.map (f : V →+ V)).addSubgroupOf L)
      ((L.map (f' : V →+ V)).addSubgroupOf L) subgroupMap (by
        intro l hl
        change (l : V) ∈ L.map (f : V →+ V) at hl
        change (AddMonoidHom.id V) (l : V) ∈ L.map (f' : V →+ V)
        obtain ⟨v, hv, hvl⟩ := AddSubgroup.mem_map.mp hl
        exact AddSubgroup.mem_map.mpr
          ⟨d • v, L.nsmul_mem hv d, (hcomm v).trans (congrArg (AddMonoidHom.id V) hvl)⟩)
  have square : latticeMap.comp (kerMapEquivQuotientOfEquiv L L f h).toAddMonoidHom =
      (kerMapEquivQuotientOfEquiv L L f' h').toAddMonoidHom.comp kernelMap :=
    kerMapEquivQuotientOfEquiv_naturality L L f h L L f' h'
      (nsmulAddMonoidHom d) (AddMonoidHom.id V)
      (by intro v hv; exact L.nsmul_mem hv d) (by intro v hv; exact hv) hcomm
  have hquot (z : L ⧸ (L.map (f : V →+ V)).addSubgroupOf L) :
      reduction (e z) = e' (latticeMap z) := by
    obtain ⟨l, rfl⟩ := mk'_surjective _ z
    simp only [reduction, e, e', latticeMap]
    rfl
  change reduction.comp (nsmulTorsionEquivQuotient L (m * d) hmd).toAddMonoidHom =
    (nsmulTorsionEquivQuotient L m hm).toAddMonoidHom.comp torsionMap
  apply AddMonoidHom.ext
  intro x
  have hkernel : kernelMap (c x) = c' (torsionMap x) := by
    apply Subtype.ext
    change map L L (nsmulAddMonoidHom (α := V) d)
      (by intro v hv; exact L.nsmul_mem hv d) (c x : V ⧸ L) =
        (c' (torsionMap x) : V ⧸ L)
    simp only [c, c', AddEquiv.addSubgroupCongr_apply, map_nsmulAddMonoidHom]
    rfl
  have hpoint : latticeMap (kerMapEquivQuotientOfEquiv L L f h (c x)) =
      kerMapEquivQuotientOfEquiv L L f' h' (kernelMap (c x)) :=
    DFunLike.congr_fun square (c x)
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [nsmulTorsionEquivQuotient_eq_kerMapEquivQuotientOfEquiv,
    nsmulTorsionEquivQuotient_eq_kerMapEquivQuotientOfEquiv]
  change reduction (e (kerMapEquivQuotientOfEquiv L L f h (c x))) =
    e' (kerMapEquivQuotientOfEquiv L L f' h' (c' (torsionMap x)))
  rw [hquot, hpoint, hkernel]

end QuotientAddGroup
