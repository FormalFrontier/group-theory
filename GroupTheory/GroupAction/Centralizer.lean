/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Automorphisms of actions as centralizers

For a group acting on an object of any category, `Action.autEquivCentralizer`
identifies equivariant automorphisms with the centralizer of the action in the
underlying object's automorphism group. The group, object and morphism universes
are independent.

`Action.autEquivPermCentralizer` specializes this construction to a group acting on
a type, using Mathlib's `CategoryTheory.Aut.mulEquivPerm`. Both groups multiply by
ordinary composition: the permutation of `α * β` sends `x` to `α (β x)`, not to the
inverse permutation. No finiteness, transitivity, faithfulness or chosen point is
required, including for the empty type.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, discussion of
  automorphisms of `G`-sets, motivates the permutation statement. The construction
  for an arbitrary category generalizes that setting.
* Mathlib's `Action.ρAut`, `Action.mkIso`, forgetful functor and
  `CategoryTheory.Aut.mulEquivPerm` supply the action and automorphism interfaces.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Action

section Category

variable {G : Type u} [Group G] {C : Type v} [Category.{w} C] (A : Action C G)

/-- Equivariant automorphisms are exactly the automorphisms of the underlying
object commuting with the group action. The forward map forgets equivariance;
the inverse equips a commuting isomorphism with its equivariance proof. -/
def autEquivCentralizer : Aut A ≃* Subgroup.centralizer (Set.range A.ρAut) where
  toFun α := ⟨(forget C G).mapIso α, by
    rintro _ ⟨g, rfl⟩
    apply Aut.ext
    exact (α.hom.comm g).symm⟩
  invFun f := mkIso f.val fun g => by
    have h := congrArg Iso.hom (f.property _ ⟨g, rfl⟩)
    exact h.symm
  left_inv α := by
    apply Aut.ext
    apply hom_ext
    rfl
  right_inv f := by
    apply Subtype.ext
    apply Aut.ext
    rfl
  map_mul' α β := by
    apply Subtype.ext
    exact ((forget C G).mapAut A).map_mul α β

/-- The centralizer element is the exact underlying isomorphism. -/
@[simp]
theorem coe_autEquivCentralizer (α : Aut A) :
    (autEquivCentralizer A α : Aut A.V) = (forget C G).mapIso α := rfl

/-- Forgetting the inverse construction recovers the given centralizer element. -/
@[simp]
theorem mapIso_autEquivCentralizer_symm
    (f : Subgroup.centralizer (Set.range A.ρAut)) :
    (forget C G).mapIso ((autEquivCentralizer A).symm f) = f.val := by
  apply Aut.ext
  rfl

/-- The bundled forward homomorphism agrees with the forgetful functor's `mapAut`. -/
theorem subtype_comp_autEquivCentralizer :
    (Subgroup.subtype _).comp (autEquivCentralizer A).toMonoidHom =
      (forget C G).mapAut A := rfl

end Category

section Types

variable (G : Type u) (X : Type v) [Group G] [MulAction G X]

/-- The stock isomorphism from type automorphisms to permutations sends the
categorical action homomorphism to the usual action permutations. -/
@[simp]
theorem mulEquivPerm_ρAut (g : G) :
    (Aut.mulEquivPerm (α := X)) ((ofMulAction G X).ρAut g) = MulAction.toPermHom G X g := by
  ext x
  rfl

-- Transport only the centralizer subgroup; equivariance and its inverse are
-- constructed once, in `autEquivCentralizer`.
private theorem map_centralizer_ρAut :
    (Subgroup.centralizer (Set.range (ofMulAction G X).ρAut)).map
        (Aut.mulEquivPerm (α := X)).toMonoidHom =
      Subgroup.centralizer (Set.range (MulAction.toPermHom G X)) := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩ _ ⟨g, rfl⟩
    change MulAction.toPermHom G X g * Aut.mulEquivPerm a =
      Aut.mulEquivPerm a * MulAction.toPermHom G X g
    rw [← mulEquivPerm_ρAut G X]
    exact ((Aut.mulEquivPerm (α := X)).map_mul _ _).symm.trans
      ((congrArg (Aut.mulEquivPerm (α := X)) (ha _ ⟨g, rfl⟩)).trans
        ((Aut.mulEquivPerm (α := X)).map_mul _ _))
  · intro hf
    refine ⟨Aut.mulEquivPerm.symm f, ?_, Aut.mulEquivPerm.apply_symm_apply f⟩
    rintro _ ⟨g, rfl⟩
    apply (Aut.mulEquivPerm (α := X)).injective
    calc
      _ = (Aut.mulEquivPerm (α := X)) ((ofMulAction G X).ρAut g) * f :=
        ((Aut.mulEquivPerm (α := X)).map_mul _ _).trans
          (congrArg ((Aut.mulEquivPerm (α := X)) ((ofMulAction G X).ρAut g) * ·)
            (Aut.mulEquivPerm.apply_symm_apply f))
      _ = f * (Aut.mulEquivPerm (α := X)) ((ofMulAction G X).ρAut g) := by
        rw [mulEquivPerm_ρAut]
        exact hf _ ⟨g, rfl⟩
      _ = _ := (congrArg (· * (Aut.mulEquivPerm (α := X)) ((ofMulAction G X).ρAut g))
        (Aut.mulEquivPerm.apply_symm_apply f).symm).trans
          ((Aut.mulEquivPerm (α := X)).map_mul _ _).symm

/-- Automorphisms of a `G`-set are the permutations centralizing the action.
This is `autEquivCentralizer` followed by the stock `Aut.mulEquivPerm`
conversion, with ordinary composition on both sides. Inspired by May's
Chapter 3 discussion of automorphisms of `G`-sets. -/
def autEquivPermCentralizer :
    Aut (ofMulAction G X) ≃*
      Subgroup.centralizer (Set.range (MulAction.toPermHom G X)) :=
  (autEquivCentralizer (ofMulAction G X)).trans
    (((Aut.mulEquivPerm (α := X)).subgroupMap
      (Subgroup.centralizer (Set.range (ofMulAction G X).ρAut) : Subgroup (Aut X))).trans
      (MulEquiv.subgroupCongr (by exact map_centralizer_ρAut G X)))

/-- The type-level specialization is the generic construction followed by
Mathlib's automorphism-to-permutation conversion. -/
theorem coe_autEquivPermCentralizer (α : Aut (ofMulAction G X)) :
    (autEquivPermCentralizer G X α : Equiv.Perm X) =
      Aut.mulEquivPerm (autEquivCentralizer (ofMulAction G X) α).val := rfl

/-- The forward permutation is the equivalence of the exact forgotten isomorphism. -/
theorem autEquivPermCentralizer_eq_toEquiv (α : Aut (ofMulAction G X)) :
    (autEquivPermCentralizer G X α : Equiv.Perm X) =
      ((forget (Type v) G).mapIso α).toEquiv := rfl

/-- The forward homomorphism is the composite of the two stock homomorphisms. -/
theorem subtype_comp_autEquivPermCentralizer :
    (Subgroup.subtype _).comp (autEquivPermCentralizer G X).toMonoidHom =
      (Aut.mulEquivPerm (α := X)).toMonoidHom.comp
        ((forget (Type v) G).mapAut (ofMulAction G X)) := rfl

/-- Evaluation of the forward permutation. -/
@[simp]
theorem autEquivPermCentralizer_apply (α : Aut (ofMulAction G X)) (x : X) :
    (autEquivPermCentralizer G X α : Equiv.Perm X) x = α.hom.hom x := rfl

/-- Evaluation of the inverse of the forward permutation. -/
@[simp]
theorem autEquivPermCentralizer_apply_symm (α : Aut (ofMulAction G X)) (x : X) :
    (autEquivPermCentralizer G X α : Equiv.Perm X).symm x = α.inv.hom x := rfl

/-- Evaluation of the automorphism constructed from a centralizing permutation. -/
@[simp]
theorem autEquivPermCentralizer_symm_hom_apply
    (f : Subgroup.centralizer (Set.range (MulAction.toPermHom G X))) (x : X) :
    ((autEquivPermCentralizer G X).symm f).hom.hom x = (f : Equiv.Perm X) x := rfl

/-- Evaluation of the inverse automorphism constructed from a centralizing permutation. -/
@[simp]
theorem autEquivPermCentralizer_symm_inv_apply
    (f : Subgroup.centralizer (Set.range (MulAction.toPermHom G X))) (x : X) :
    ((autEquivPermCentralizer G X).symm f).inv.hom x = (f : Equiv.Perm X).symm x := rfl

/-- Multiplication is ordinary composition, in the same order as permutations. -/
@[simp]
theorem autEquivPermCentralizer_mul_apply (α β : Aut (ofMulAction G X)) (x : X) :
    (autEquivPermCentralizer G X (α * β) : Equiv.Perm X) x =
      α.hom.hom (β.hom.hom x) := rfl

/-- Equality with a given centralizer element can be checked on forward values. -/
theorem autEquivPermCentralizer_eq_iff (α : Aut (ofMulAction G X))
    (f : Subgroup.centralizer (Set.range (MulAction.toPermHom G X))) :
    autEquivPermCentralizer G X α = f ↔ ∀ x : X, α.hom.hom x = (f : Equiv.Perm X) x := by
  constructor
  · intro h x
    exact congrArg (fun k : Subgroup.centralizer (Set.range (MulAction.toPermHom G X)) =>
      (k : Equiv.Perm X) x) h
  · intro h
    apply Subtype.ext
    exact Equiv.ext h

end Types

end Action
