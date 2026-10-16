/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import Mathlib.Data.ZMod.Basic

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.Schreier
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Ranks of finitely generated free groups

A free basis of a finitely generated group has finitely many elements, and its cardinality
is the minimum number of group generators, `Group.rank`. For a finite-index subgroup of a
finitely generated free group, the Nielsen–Schreier rank formula is expressed without
subtraction in `ℕ`.

Subgroup freeness is supplied by Mathlib's `subgroupIsFreeOfIsFree`, and finite generation
of finite-index subgroups by Mathlib's `Subgroup.fg_of_index_ne_zero`. No additional
finite-generation hypothesis on the subgroup is needed. The numerical formula uses the
coset action groupoid: an indexed basis of its root group consists of the loops associated
to positive generating arrows outside a spanning tree. The tree contributes one fewer
arrow than there are cosets. All counts are finite before the complementary parts are
added, and the argument uses no subtraction or assumption that the ambient rank is positive.

The private indexed-basis construction retains the indexing data from David Wärn's
`IsFreeGroupoid.SpanningTree.endIsFree` argument; `FreeGroupBasis.map` transports that basis
to the subgroup. This is the algebraic groupoid proof, not a construction of topological
coverings or an Euler-characteristic calculation.

## References

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 4, §5, first theorem,
  printed page 37: the finite-index numerical clause. The generator count there is the
  size of a free basis, not the size of an arbitrary generating set.
- Mathlib's free-group bases and Nielsen–Schreier theorem, formalized by David Wärn,
  Eric Wieser and Joachim Breitner; its group rank and Schreier finite-generation API,
  formalized by Thomas Browning.
-/

@[expose] public section

universe u v

namespace Quiver

/-! ## Counting the edges of a rooted tree -/

private theorem arborescence_target_ne_root {V : Type u} [Quiver.{v} V]
    [Arborescence V] {a b : V} (e : a ⟶ b) : b ≠ root V := by
  intro h
  subst b
  exact Path.cons_ne_nil (default : Path (root V) a) e (Subsingleton.elim _ _)

private theorem arborescence_target_injective {V : Type u} [Quiver.{v} V]
    [Arborescence V] : Function.Injective (Total.right : Total V → V) := by
  rintro ⟨a, b, e⟩ ⟨c, d, f⟩ h
  dsimp at h
  subst d
  have hp : (default : Path (root V) a).cons e =
      (default : Path (root V) c).cons f := Subsingleton.elim _ _
  obtain rfl := Path.obj_eq_of_cons_eq_cons hp
  obtain rfl := eq_of_heq (Path.hom_heq_of_cons_eq_cons hp)
  rfl

private theorem natCard_total_add_one {V : Type u} [Quiver.{v} V]
    [Arborescence V] [Finite V] : Nat.card (Total V) + 1 = Nat.card V := by
  classical
  -- Each non-root vertex has exactly one incoming edge, the last edge of its root path.
  let f : Total V → {b : V // b ≠ root V} :=
    fun e => ⟨e.right, arborescence_target_ne_root e.hom⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e e' h
      exact arborescence_target_injective (congrArg Subtype.val h)
    · rintro ⟨b, hb⟩
      rcases (default : Path (root V) b) with _ | ⟨p, e⟩
      · exact (hb rfl).elim
      · exact ⟨⟨_, _, e⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf)]
  exact Finite.card_option.symm.trans (Nat.card_congr (Equiv.optionSubtypeNe (root V)))

private theorem arborescence_no_opposite {V : Type u} [Quiver.{v} V]
    [Arborescence V] {a b : V} (e : a ⟶ b) (f : b ⟶ a) : False := by
  have h : ((default : Path (root V) a).cons e).cons f =
      (default : Path (root V) a) := Subsingleton.elim _ _
  have := congrArg Path.length h
  simp only [Path.length_cons] at this
  omega

-- Forget the formal orientation, but retain the underlying labelled edge.
private def totalToSymmetrifySet {V : Type u} [Quiver.{v} V]
    (T : WideSubquiver (Symmetrify V)) :
    Total T → wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  | ⟨a, b, ⟨Sum.inl e, h⟩⟩ => ⟨⟨a, b, e⟩, Or.inl h⟩
  | ⟨a, b, ⟨Sum.inr e, h⟩⟩ => ⟨⟨b, a, e⟩, Or.inr h⟩

private theorem totalToSymmetrifySet_bijective {V : Type u} [Quiver.{v} V]
    (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Function.Bijective (totalToSymmetrifySet T) := by
  -- Opposite orientations cannot both occur in an arborescence: they make a two-cycle.
  constructor
  · rintro ⟨a, b, ⟨e, he⟩⟩ ⟨c, d, ⟨f, hf⟩⟩ h
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        have h' : (⟨a, b, e⟩ : Total V) = ⟨c, d, f⟩ := congrArg Subtype.val h
        cases h'
        rfl
      | inr f =>
        have h' : (⟨a, b, e⟩ : Total V) = ⟨d, c, f⟩ := congrArg Subtype.val h
        cases h'
        exact (@arborescence_no_opposite T T.quiver _ a b ⟨Sum.inl e, he⟩ ⟨Sum.inr e, hf⟩).elim
    | inr e =>
      cases f with
      | inl f =>
        have h' : (⟨b, a, e⟩ : Total V) = ⟨c, d, f⟩ := congrArg Subtype.val h
        cases h'
        exact (@arborescence_no_opposite T T.quiver _ a b ⟨Sum.inr e, he⟩ ⟨Sum.inl e, hf⟩).elim
      | inr f =>
        have h' : (⟨b, a, e⟩ : Total V) = ⟨d, c, f⟩ := congrArg Subtype.val h
        cases h'
        rfl
  · rintro ⟨⟨a, b, e⟩, he⟩
    change Sum.inl e ∈ T a b ∨ Sum.inr e ∈ T b a at he
    rcases he with he | he
    · exact ⟨⟨a, b, ⟨Sum.inl e, he⟩⟩, rfl⟩
    · exact ⟨⟨b, a, ⟨Sum.inr e, he⟩⟩, rfl⟩

private theorem natCard_wideSubquiverSymmetrify_add_one {V : Type u} [Quiver.{v} V]
    [Finite V] (T : WideSubquiver (Symmetrify V)) [Arborescence T] :
    Nat.card (wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)) + 1 = Nat.card V := by
  rw [← Nat.card_congr
    (Equiv.ofBijective (totalToSymmetrifySet T) (totalToSymmetrifySet_bijective T))]
  let : Finite T := inferInstanceAs (Finite V)
  exact natCard_total_add_one (V := T)

end Quiver

namespace FreeGroupBasis

variable {ι : Type u} {G : Type v} [Group G]

private theorem lift_restrict_injective {K : Type*} [Group K] (b : FreeGroupBasis ι G)
    {s : Finset G} (hs : Subgroup.closure (s : Set G) = ⊤) :
    Function.Injective (fun f : ι → K => fun x : s => b.lift f x) := by
  intro f g h
  apply b.lift.injective
  exact MonoidHom.eq_of_eqOn_dense hs fun x hx => congr_fun h ⟨x, hx⟩

/-- A free basis of a finitely generated group has a finite indexing type. -/
theorem finite (b : FreeGroupBasis ι G) [Group.FG G] : Finite ι := by
  -- Restriction to finitely many generators bounds the maps to a fixed two-element group.
  obtain ⟨s, hs⟩ := Group.FG.out (G := G)
  have : Finite (ι → Multiplicative (ZMod 2)) :=
    Finite.of_injective _ (lift_restrict_injective b hs)
  apply Finite.of_not_infinite
  intro h
  let := h
  exact (inferInstance : Infinite (ι → Multiplicative (ZMod 2))).false

/-- The cardinality of any free basis of a finitely generated group is the minimum number
of group generators. In particular, the count of free generators in May's finite-index
rank formula (Chapter 4, §5, first theorem) agrees with `Group.rank`. -/
theorem natCard_eq_rank (b : FreeGroupBasis ι G) [Group.FG G] :
    Nat.card ι = Group.rank G := by
  classical
  let _ : Finite ι := b.finite
  let _ : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · -- A generating set determines every homomorphism into the two-element group.
    obtain ⟨s, hs, hgen⟩ := Group.rank_spec G
    have hc2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)
    have hcount := Nat.card_le_card_of_injective _
      (lift_restrict_injective (K := Multiplicative (ZMod 2)) b hgen)
    rw [Nat.card_fun, Nat.card_fun, hc2, Nat.card_eq_finsetCard, hs] at hcount
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcount
  · -- The basis itself generates the group, giving the opposite inequality.
    have hlift : FreeGroup.lift (b : ι → G) = b.repr.symm.toMonoidHom := by
      ext i
      apply b.repr.injective
      simp
    have hgen : Subgroup.closure (Set.range b) = ⊤ := by
      apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mp
      rw [hlift]
      exact b.repr.symm.surjective
    have hupper : Group.rank G ≤ (Finset.univ.image b).card :=
      Group.rank_le (by simpa using hgen)
    exact hupper.trans (Finset.card_image_le.trans_eq (by simp [Nat.card_eq_fintype_card]))

end FreeGroupBasis

open CategoryTheory Quiver IsFreeGroupoid IsFreeGroupoid.SpanningTree

/-
The indexed tree-loop construction below refines the proof of `SpanningTree.endIsFree`
in Mathlib, retaining its specified indexing set as `FreeGroupBasis` data.

Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
private theorem map_treePath_eq_one {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C]
    (T : WideSubquiver (Symmetrify (Generators C))) [Arborescence T]
    {K : Type u} [Group K] (F : C ⥤ CategoryTheory.SingleObj K)
    (hF : ∀ (a b) (e : a ⟶ b), e ∈ wideSubquiverSymmetrify T a b →
      F.map (IsFreeGroupoid.of e) = 1)
    {a : C} (p : Path (root T) a) : F.map (homOfPath T p) = 1 := by
  induction p with
  | nil =>
    change F.map (𝟙 _) = 1
    rw [F.map_id, SingleObj.id_as_one]
  | cons p e ih =>
    change F.map (homOfPath T p ≫ _) = 1
    rw [F.map_comp, SingleObj.comp_as_mul, ih, mul_one]
    rcases e with ⟨e | e, he⟩
    · exact hF _ _ e (Or.inl he)
    · rw [F.map_inv, SingleObj.inv_as_inv, inv_eq_one]
      exact hF _ _ e (Or.inr he)

/-- The complement of the tree indexes a free basis of the root group. -/
private noncomputable def treeLoopBasis {C : Type u} [Groupoid.{u} C] [IsFreeGroupoid C]
    (T : WideSubquiver (Symmetrify (Generators C))) [Arborescence T] :
    FreeGroupBasis
      ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ : Set (Total (Generators C)))
      (End (show C from root T)) := by
  classical
  apply FreeGroupBasis.ofUniqueLift _ (fun e => loopOfHom T (IsFreeGroupoid.of e.val.hom))
  intro K _ f
  let labels : Labelling (Generators C) K := fun a b e =>
    if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
  obtain ⟨F, hF, uniqueF⟩ := IsFreeGroupoid.unique_lift labels
  have htree {a : C} (p : Path (root T) a) : F.map (homOfPath T p) = 1 := by
    apply map_treePath_eq_one T F _ p
    intro a b e he
    rw [hF]
    exact dite_eq_left he
  have hloop {a b : C} (q : a ⟶ b) : F.map (loopOfHom T q) = (F.map q : K) := by
    simp only [loopOfHom, Functor.map_comp, Functor.map_inv, treeHom, htree,
      SingleObj.comp_as_mul, SingleObj.inv_as_inv, inv_one, mul_one, one_mul]
  refine ⟨F.mapEnd _, ?_, ?_⟩
  · rintro ⟨⟨a, b, e⟩, he⟩
    change F.map (loopOfHom T (IsFreeGroupoid.of e)) = _
    rw [hloop (IsFreeGroupoid.of e), hF]
    exact dite_eq_right he
  · intro E hE
    have hEF : functorOfMonoidHom T E = F := by
      apply uniqueF
      intro a b e
      change E (loopOfHom T (IsFreeGroupoid.of e)) = labels e
      dsimp only [labels]
      split_ifs with he
      · rw [loopOfHom_eq_id T e he, ← End.one_def, E.map_one]
      · exact hE ⟨⟨a, b, e⟩, he⟩
    ext p
    have hp := congrArg (fun L : C ⥤ CategoryTheory.SingleObj K => L.map p) hEF
    simpa only [functorOfMonoidHom, loopOfHom, treeHom_root, IsIso.inv_id,
      Category.id_comp, Category.comp_id, Functor.mapEnd, DFunLike.coe] using hp

/-- Positive generating arrows are determined by source and ambient free generator. -/
private noncomputable def actionGeneratorArrowEquiv {G A : Type u} [Group G] [IsFreeGroup G]
    [MulAction G A] :
    Total (Generators (ActionCategory G A)) ≃ A × IsFreeGroup.Generators G where
  toFun t := ((show ActionCategory G A from t.left).back, t.hom.val)
  invFun s := ⟨(ActionCategory.objEquiv G A) s.1,
    (ActionCategory.objEquiv G A) (IsFreeGroup.of s.2 • s.1), ⟨s.2, rfl⟩⟩
  left_inv := by
    rintro ⟨a, b, ⟨e, he⟩⟩
    cases a with
    | mk a =>
      cases b with
      | mk b =>
        change A at a b
        change IsFreeGroup.of e • a = b at he
        cases he
        rfl
  right_inv s := rfl

namespace Subgroup

variable {G : Type u} [Group G] [IsFreeGroup G] [Group.FG G]

/-- The Nielsen–Schreier rank formula for a finite-index subgroup of a finitely generated
free group, in subtraction-free natural-number arithmetic. This is the finite-index
numerical clause of May, Chapter 4, §5, first theorem (printed page 37).

Finite index is essential: the trivial subgroup of a rank-one free group has infinite
index, encoded by `Subgroup.index` as zero, and would give the false equation `0 = 1`.
No normality, nontriviality or separate finite-generation assumption on `H` is required. -/
theorem rank_add_index_eq (H : Subgroup G) [H.FiniteIndex] :
    Group.rank H + H.index = Group.rank G * H.index + 1 := by
  classical
  let C := ActionCategory G (G ⧸ H)
  let r : C := (ActionCategory.objEquiv G (G ⧸ H)) ↑(1 : G)
  let _ : RootedConnected (show Symmetrify (Generators C) from r) :=
    @IsFreeGroupoid.generators_connected C inferInstance
      ActionCategory.instIsConnectedOfIsPretransitiveOfNonempty inferInstance r
  let T := geodesicSubtree (show Symmetrify (Generators C) from r)
  let W : Set (Total (Generators C)) :=
    wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T)
  let _ : Finite (IsFreeGroup.Generators G) := (IsFreeGroup.basis G).finite
  let _ : Finite C := Finite.of_equiv (G ⧸ H) (ActionCategory.objEquiv G (G ⧸ H))
  let _ : Finite (Generators C) := inferInstanceAs (Finite C)
  -- The partition count needs finite arrows, not just finite vertices.
  let _ : Finite (Total (Generators C)) :=
    Finite.of_equiv ((G ⧸ H) × IsFreeGroup.Generators G)
      (actionGeneratorArrowEquiv (G := G) (A := G ⧸ H)).symm
  have hH : Nat.card (Wᶜ : Set (Total (Generators C))) = Group.rank H :=
    ((treeLoopBasis T).map (ActionCategory.endMulEquivSubgroup H)).natCard_eq_rank
  have htree : Nat.card W + 1 = Nat.card C :=
    Quiver.natCard_wideSubquiverSymmetrify_add_one T
  have hpartition : Nat.card W + Nat.card (Wᶜ : Set (Total (Generators C))) =
      Nat.card (Total (Generators C)) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.Set.sumCompl W)
  have hvertices : Nat.card C = H.index := by
    rw [H.index_eq_card]
    exact Nat.card_congr (ActionCategory.objEquiv G (G ⧸ H)).symm
  have harrows : Nat.card (Total (Generators C)) =
      H.index * Nat.card (IsFreeGroup.Generators G) := by
    rw [Nat.card_congr (actionGeneratorArrowEquiv (G := G) (A := G ⧸ H)),
      Nat.card_prod, ← H.index_eq_card]
  calc
    Group.rank H + H.index =
        Nat.card (Wᶜ : Set (Total (Generators C))) + (Nat.card W + 1) := by
      rw [hH, htree, hvertices]
    _ = (Nat.card W + Nat.card (Wᶜ : Set (Total (Generators C)))) + 1 := by omega
    _ = Nat.card (Total (Generators C)) + 1 := by rw [hpartition]
    _ = Group.rank G * H.index + 1 := by
      rw [harrows, (IsFreeGroup.basis G).natCard_eq_rank, Nat.mul_comm]

end Subgroup
