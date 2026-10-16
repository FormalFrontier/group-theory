/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Automorphisms of transitive group actions

The automorphism group of a transitive left `G`-action, with chosen point `x`,
is the quotient of the normalizer of `stabilizer G x` by that stabilizer.
The target is Mathlib's `CategoryTheory.Aut (Action.ofMulAction G X)`.
The group and the acted-on type may lie in independent universes.

`Action.normalizerToAut` first constructs inverse right translation on `G ⧸ H`
for an arbitrary subgroup `H`. Its kernel is `H` inside its normalizer.
After forgetting invertibility and including finite sets into types, it agrees
with `Action.FintypeCat.toEndHom` under the latter's normality and finiteness
hypotheses. Neither hypothesis is needed for the general construction.

## Multiplication convention

Automorphisms multiply by ordinary function composition: `(a * b) y = a (b y)`.
Accordingly, the class of `n` sends `g • x` to `(g * n⁻¹) • x`.
May's displayed formula in Chapter 3, §4 instead uses `g * n`, without the inverse;
that formula reverses multiplication under this convention. The abstract group
isomorphism is unchanged, but the parameterization here is inverse to that formula.
No assumption about an unstated convention in the source is made.

The coset-to-orbit bridge uses `MulAction.ofQuotientStabilizer` as a function,
not a categorical isomorphism between actions on types in different universes.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, §4,
  first lemma, p. 24, for the normalizer-quotient classification.
* Mathlib's `Action.FintypeCat.toEndHom`, `MulAction.right_quotientAction`,
  and `MulAction.ofQuotientStabilizer` supply the coset-action constructions.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Action

variable {G : Type u} [Group G] (H : Subgroup G)

/-- Inverse right translation by the normalizer on the left-coset action.
The parameter `n` sends `[g]` to `[g * n⁻¹]`, so this is a homomorphism into
ordinary equivariant automorphisms. No normality or finiteness is assumed. -/
noncomputable def normalizerToAut :
    Subgroup.normalizer (H : Set G) →* Aut (Action.ofMulAction G (G ⧸ H)) := by
  refine
    { toFun := fun n =>
        Action.mkIso
          (MulAction.toPerm ((Subgroup.normalizer (H : Set G)).equivOp n⁻¹) :
            Equiv.Perm (G ⧸ H)).toIso
          (fun g => by
            ext q
            induction q using Quotient.inductionOn with | h k =>
              change QuotientGroup.mk ((g * k) * (n : G)⁻¹) =
                QuotientGroup.mk (g * (k * (n : G)⁻¹))
              rw [mul_assoc])
      map_one' := ?_
      map_mul' := fun n m => ?_ }
  · apply Aut.ext
    apply Action.hom_ext
    ext q
    induction q using Quotient.inductionOn with | h k =>
      change QuotientGroup.mk (k * (1 : G)⁻¹) = QuotientGroup.mk k
      simp
  · apply Aut.ext
    apply Action.hom_ext
    ext q
    induction q using Quotient.inductionOn with | h k =>
      change QuotientGroup.mk (k * ((n : G) * (m : G))⁻¹) =
        QuotientGroup.mk ((k * (m : G)⁻¹) * (n : G)⁻¹)
      rw [mul_inv_rev, mul_assoc]

/-- The representative formula for inverse right translation. -/
@[simp] theorem normalizerToAut_apply (n : Subgroup.normalizer (H : Set G)) (g : G) :
    (normalizerToAut H n).hom.hom (QuotientGroup.mk g) =
      QuotientGroup.mk (g * (n : G)⁻¹) := by
  rfl

/-- Precisely the elements of `H` act trivially on `G ⧸ H`. -/
@[simp] theorem normalizerToAut_ker :
    (normalizerToAut H).ker = H.subgroupOf (Subgroup.normalizer (H : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hn
    have he := congrArg
      (fun a : Aut (Action.ofMulAction G (G ⧸ H)) => a.hom.hom (QuotientGroup.mk (1 : G))) hn
    change (normalizerToAut H n).hom.hom (QuotientGroup.mk (1 : G)) =
      QuotientGroup.mk (1 : G) at he
    rw [normalizerToAut_apply, one_mul] at he
    change QuotientGroup.mk ((n : G)⁻¹) = (QuotientGroup.mk (1 : G) : G ⧸ H) at he
    simpa using QuotientGroup.eq.mp he
  · intro hn
    apply Aut.ext
    apply Action.hom_ext
    ext q
    induction q using Quotient.inductionOn with | h g =>
      change (normalizerToAut H n).hom.hom (QuotientGroup.mk g) = QuotientGroup.mk g
      rw [normalizerToAut_apply]
      apply QuotientGroup.eq.mpr
      simpa [mul_inv_rev, mul_assoc] using hn

/-- On the same Type-valued action, forgetting invertibility agrees with
Mathlib's finite-normal construction after including finite sets into types. -/
theorem normalizerToAut_toEnd [H.Normal] [Fintype (G ⧸ H)]
    (n : Subgroup.normalizer (H : Set G)) :
    Aut.toEnd (Action.ofMulAction G (G ⧸ H)) (normalizerToAut H n) =
      (FintypeCat.incl.mapAction G).mapEnd _ (Action.FintypeCat.toEndHom H (n : G)) := by
  apply Action.hom_ext
  ext q
  induction q using Quotient.inductionOn with | h g =>
    exact normalizerToAut_apply H n g

end Action

namespace MulAction

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

private theorem actionAut_eq_of_value_eq [IsPretransitive G X] (x : X)
    (a b : CategoryTheory.Aut (Action.ofMulAction G X))
    (h : a.hom.hom x = b.hom.hom x) : a = b := by
  let fa : X → X := fun y => a.hom.hom y
  let fb : X → X := fun y => b.hom.hom y
  apply CategoryTheory.Aut.ext
  apply Action.hom_ext
  ext y
  change fa y = fb y
  obtain ⟨g, rfl⟩ := exists_smul_eq G x y
  have ha : fa (g • x) = g • fa x :=
    ConcreteCategory.congr_hom (a.hom.comm g) x
  have hb : fb (g • x) = g • fb x :=
    ConcreteCategory.congr_hom (b.hom.comm g) x
  rw [ha, hb, show fa x = fb x from h]

private theorem exists_normalizer_inv_smul_eq [IsPretransitive G X] (x : X)
    (a : CategoryTheory.Aut (Action.ofMulAction G X)) :
    ∃ n : Subgroup.normalizer (stabilizer G x : Set G),
      a.hom.hom x = (n : G)⁻¹ • x := by
  let f : X → X := fun y => a.hom.hom y
  let fInv : X → X := fun y => a.inv.hom y
  have hinv : Function.LeftInverse fInv f := fun y =>
    ConcreteCategory.congr_hom (Action.hom_inv_hom a) y
  have hcomm (g : G) (y : X) : f (g • y) = g • f y :=
    ConcreteCategory.congr_hom (a.hom.comm g) y
  have hstab : stabilizer G (f x) = stabilizer G x := by
    ext g
    simp only [mem_stabilizer_iff, ← hcomm, hinv.injective.eq_iff]
  obtain ⟨g, hg⟩ := exists_smul_eq G x (f x)
  have hn : g ∈ Subgroup.normalizer (stabilizer G x : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [← MulEquiv.toMonoidHom_eq_coe, ← stabilizer_smul_eq_stabilizer_map_conj, hg]
    exact hstab
  refine ⟨⟨g⁻¹, Subgroup.inv_mem _ hn⟩, ?_⟩
  change f x = (g⁻¹)⁻¹ • x
  simpa only [inv_inv] using hg.symm

private noncomputable def quotientStabilizerEquiv [IsPretransitive G X] (x : X) :
    (G ⧸ stabilizer G x) ≃ X :=
  Equiv.ofBijective (ofQuotientStabilizer (X := X) G x)
    ⟨injective_ofQuotientStabilizer (X := X) G x, fun y => by
      obtain ⟨g, rfl⟩ := exists_smul_eq G x y
      exact ⟨QuotientGroup.mk g, rfl⟩⟩

private theorem quotientStabilizerEquiv_smul [IsPretransitive G X] (x : X)
    (g : G) (q : G ⧸ stabilizer G x) :
    quotientStabilizerEquiv (G := G) x (g • q) =
      g • quotientStabilizerEquiv (G := G) x q :=
  ofQuotientStabilizer_smul G x g q

private theorem quotientStabilizerEquiv_symm_smul [IsPretransitive G X] (x : X)
    (g : G) (y : X) :
    (quotientStabilizerEquiv (G := G) x).symm (g • y) =
      g • (quotientStabilizerEquiv (G := G) x).symm y := by
  apply (quotientStabilizerEquiv (G := G) x).injective
  simp only [Equiv.apply_symm_apply, quotientStabilizerEquiv_smul]

private noncomputable def orbitAutConj [IsPretransitive G X] (x : X) :
    Aut (Action.ofMulAction G (G ⧸ stabilizer G x)) →* Aut (Action.ofMulAction G X) where
  toFun a := Action.mkIso
    (((quotientStabilizerEquiv (G := G) x).symm.trans
      ((Action.forget (Type u) G).mapIso a).toEquiv).trans
        (quotientStabilizerEquiv (G := G) x)).toIso (fun g => by
      ext y
      change X at y
      change quotientStabilizerEquiv (G := G) x
          (a.hom.hom ((quotientStabilizerEquiv (G := G) x).symm (g • y))) =
        g • quotientStabilizerEquiv (G := G) x
          (a.hom.hom ((quotientStabilizerEquiv (G := G) x).symm y))
      rw [quotientStabilizerEquiv_symm_smul]
      exact (congrArg (quotientStabilizerEquiv (G := G) x)
        (ConcreteCategory.congr_hom (a.hom.comm g) _)).trans
          (quotientStabilizerEquiv_smul (G := G) x g _))
  map_one' := by
    apply Aut.ext
    apply Action.hom_ext
    ext y
    change X at y
    exact (quotientStabilizerEquiv (G := G) x).apply_symm_apply y
  map_mul' a b := by
    apply Aut.ext
    apply Action.hom_ext
    ext y
    change X at y
    exact (congrArg (fun q => (quotientStabilizerEquiv (G := G) x) (a.hom.hom q))
      ((quotientStabilizerEquiv (G := G) x).symm_apply_apply
        (b.hom.hom ((quotientStabilizerEquiv (G := G) x).symm y)))).symm

private theorem orbitAutConj_apply [IsPretransitive G X] (x : X)
    (a : Aut (Action.ofMulAction G (G ⧸ stabilizer G x))) (q : G ⧸ stabilizer G x) :
    ((orbitAutConj (G := G) x) a).hom.hom (ofQuotientStabilizer (X := X) G x q) =
      ofQuotientStabilizer (X := X) G x (a.hom.hom q) := by
  change quotientStabilizerEquiv (G := G) x
      (a.hom.hom ((quotientStabilizerEquiv (G := G) x).symm
        (quotientStabilizerEquiv (G := G) x q))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem orbitAutConj_injective [IsPretransitive G X] (x : X) :
    Function.Injective (orbitAutConj (G := G) x) := by
  intro a b h
  apply Aut.ext
  apply Action.hom_ext
  ext q
  apply injective_ofQuotientStabilizer (X := X) G x
  exact (orbitAutConj_apply (G := G) x a q).symm.trans
    ((congrArg (fun c : Aut (Action.ofMulAction G X) =>
      c.hom.hom (ofQuotientStabilizer (X := X) G x q)) h).trans
        (orbitAutConj_apply (G := G) x b q))

private theorem orbitAutConj_normalizer_surjective [IsPretransitive G X] (x : X) :
    Function.Surjective
      ((orbitAutConj (G := G) x).comp (Action.normalizerToAut (stabilizer G x))) := by
  intro a
  obtain ⟨n, hn⟩ := exists_normalizer_inv_smul_eq x a
  refine ⟨n, actionAut_eq_of_value_eq x _ a ?_⟩
  change (orbitAutConj x (Action.normalizerToAut (stabilizer G x) n)).hom.hom x = a.hom.hom x
  rw [hn]
  simpa only [ofQuotientStabilizer_mk, Action.normalizerToAut_apply, one_smul, one_mul] using
    orbitAutConj_apply x (Action.normalizerToAut (stabilizer G x) n)
      (QuotientGroup.mk (1 : G))

private theorem orbitAutConj_normalizer_ker [IsPretransitive G X] (x : X) :
    ((orbitAutConj (G := G) x).comp (Action.normalizerToAut (stabilizer G x))).ker =
      (stabilizer G x).subgroupOf (Subgroup.normalizer (stabilizer G x : Set G)) := by
  rw [MonoidHom.ker_comp_of_injective _ _ (orbitAutConj_injective (G := G) x),
    Action.normalizerToAut_ker]

/-- For a transitive left action, equivariant automorphisms form the normalizer
quotient of a point stabilizer (May, *A Concise Course*, Chapter 3, §4).
The class of `n` sends `g • x` to `(g * n⁻¹) • x`, using ordinary composition.
This inverse parameter differs from the source's displayed right translation. -/
noncomputable def normalizerQuotientEquivAut [IsPretransitive G X] (x : X) :
    (Subgroup.normalizer (stabilizer G x : Set G) ⧸
      (stabilizer G x).subgroupOf (Subgroup.normalizer (stabilizer G x : Set G))) ≃*
      Aut (Action.ofMulAction G X) := private_decl%
  (QuotientGroup.liftEquiv _ (orbitAutConj_normalizer_surjective x)
    (orbitAutConj_normalizer_ker x).symm)

variable [IsPretransitive G X] (x : X)

/-- The classification intertwines inverse right translation on cosets with
its action on the orbit. This equation also applies when `G` and `X` lie in
different universes. -/
theorem normalizerQuotientEquivAut_mk_apply_ofQuotientStabilizer
    (n : Subgroup.normalizer (stabilizer G x : Set G)) (q : G ⧸ stabilizer G x) :
    (normalizerQuotientEquivAut (G := G) x (QuotientGroup.mk n)).hom.hom
        (ofQuotientStabilizer G x q : X) =
      ofQuotientStabilizer G x ((Action.normalizerToAut (stabilizer G x) n).hom.hom q) := by
  exact orbitAutConj_apply x (Action.normalizerToAut (stabilizer G x) n) q

/-- The class of `n` sends every orbit point `g • x` to `(g * n⁻¹) • x`. -/
@[simp] theorem normalizerQuotientEquivAut_mk_apply
    (n : Subgroup.normalizer (stabilizer G x : Set G)) (g : G) :
    (normalizerQuotientEquivAut (G := G) x (QuotientGroup.mk n)).hom.hom (g • x : X) =
      (g * (n : G)⁻¹) • x := by
  simpa only [ofQuotientStabilizer_mk, Action.normalizerToAut_apply] using
    normalizerQuotientEquivAut_mk_apply_ofQuotientStabilizer x n (QuotientGroup.mk g)

/-- Evaluation at the chosen point fixes the inverse-translation convention. -/
@[simp] theorem normalizerQuotientEquivAut_mk_apply_self
    (n : Subgroup.normalizer (stabilizer G x : Set G)) :
    (normalizerQuotientEquivAut (G := G) x (QuotientGroup.mk n)).hom.hom x = (n : G)⁻¹ • x := by
  simpa only [one_smul, one_mul] using normalizerQuotientEquivAut_mk_apply x n (1 : G)

/-- An automorphism has inverse image `[n]` exactly when its value at the
chosen point is `n⁻¹ • x`. Thus representatives can be recognized by evaluation,
without unfolding the equivalence or choosing orbit representatives. -/
theorem normalizerQuotientEquivAut_symm_apply_eq_mk_iff
    (a : Aut (Action.ofMulAction G X)) (n : Subgroup.normalizer (stabilizer G x : Set G)) :
    (normalizerQuotientEquivAut (G := G) x).symm a = QuotientGroup.mk n ↔
      a.hom.hom x = (n : G)⁻¹ • x := by
  rw [MulEquiv.symm_apply_eq]
  constructor
  · intro h
    rw [h, normalizerQuotientEquivAut_mk_apply_self]
  · intro h
    apply actionAut_eq_of_value_eq x
    rw [normalizerQuotientEquivAut_mk_apply_self]
    exact h

end MulAction
