/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.GroupAction.QuotientMap
public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Invariant equivalence relations and blocks

An invariant equivalence relation on a left `G`-set is a `Setoid` preserved by every
scalar. On a pretransitive action with a chosen point `a`, its class at `a` is a block,
and the translates of this block recover the equivalence relation.

`stabilizerInvariantSetoidOrderIso` composes this bridge with Mathlib's
`block_stabilizerOrderIso`. For the left action on `G ⧸ H`, its value at `K ≥ H` is
characterized as the kernel of `MulActionHom.quotientMapOfLE`. No normality is needed.
The inverse takes the preimage of the identity class, not the orbit equivalence relation
of the restricted left `K`-action.

## Implementation notes

The forward construction from an overgroup uses `Setoid.mkClasses` on all translates
of its basepoint orbit; it is not definitionally a function kernel. The coset kernel
theorem states equality of these `Setoid`s, rather than definitional equality.

## References

The block classification is Mathlib's `MulAction.block_stabilizerOrderIso`
(`Mathlib.GroupTheory.GroupAction.Blocks`, following Wielandt, theorem 7.5).
The partition construction is Mathlib's `Setoid.mkClasses`, also used by
`Setoid.Partition.orderIso` in `Mathlib.Data.Setoid.Partition`.
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace MulAction

/-- Equivalence relations on a left `G`-set preserved by all scalars, ordered by
relation refinement through the inherited order on `Setoid X`. -/
abbrev InvariantSetoid (G : Type u) (X : Type v) [Group G] [MulAction G X] :=
  {r : Setoid X // ∀ (g : G) (x y : X), r x y → r (g • x) (g • y)}

variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

namespace InvariantSetoid

/-- Invariant equivalence relations are determined by their relations. -/
@[ext] theorem ext {r s : InvariantSetoid G X}
    (h : ∀ x y, r.1 x y ↔ s.1 x y) : r = s :=
  Subtype.ext (Setoid.ext h)

/-- The order on invariant equivalence relations is implication of relations. -/
theorem le_iff {r s : InvariantSetoid G X} :
    r ≤ s ↔ ∀ {x y}, r.1 x y → s.1 x y :=
  Iff.rfl

/-- Preservation of the relation by a scalar. -/
theorem smul (r : InvariantSetoid G X) (g : G) {x y : X} (h : r.1 x y) :
    r.1 (g • x) (g • y) :=
  r.2 g x y h

/-- Translating a relation class gives the class of the translated point. -/
theorem smul_class (r : InvariantSetoid G X) (a : X) (g : G) :
    g • {x | r.1 x a} = {x | r.1 x (g • a)} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact r.smul g hy
  · intro hx
    refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
    change r.1 (g⁻¹ • x) a
    simpa only [inv_smul_smul] using r.smul g⁻¹ hx

/-- The equivalence class of the chosen point, as a block containing it. -/
def toBlock (r : InvariantSetoid G X) (a : X) : BlockMem G a :=
  ⟨{x | r.1 x a}, r.1.refl' a, by
    apply isBlock_iff_smul_eq_smul_of_nonempty.mpr
    intro g h hgh
    rw [smul_class r a g, smul_class r a h] at hgh ⊢
    obtain ⟨x, hx, hy⟩ := hgh
    exact Setoid.eq_of_mem_classes (r.1.mem_classes _) hx (r.1.mem_classes _) hy⟩

/-- Membership in the basepoint block is the original relation to the basepoint. -/
@[simp] theorem mem_toBlock (r : InvariantSetoid G X) (a x : X) :
    x ∈ (toBlock r a).1 ↔ r.1 x a :=
  Iff.rfl

/-- Under pretransitivity every relation class is a translate of the basepoint class. -/
theorem classes_eq_range_toBlock [IsPretransitive G X] (r : InvariantSetoid G X) (a : X) :
    r.1.classes = Set.range (fun g : G => g • (toBlock r a).1) := by
  ext C
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := exists_smul_eq G a y
    exact ⟨g, smul_class r a g⟩
  · rintro ⟨g, rfl⟩
    change g • {x | r.1 x a} ∈ r.1.classes
    rw [smul_class]
    exact r.1.mem_classes _

/-- Inclusion of the basepoint classes detects refinement of invariant relations. -/
theorem toBlock_le_toBlock_iff [IsPretransitive G X] (a : X)
    (r s : InvariantSetoid G X) : toBlock r a ≤ toBlock s a ↔ r ≤ s := by
  constructor
  · intro h x y hxy
    obtain ⟨g, hg⟩ := exists_smul_eq G y a
    have hr : r.1 (g • x) a := by
      simpa only [hg] using r.smul g hxy
    have hs : s.1 (g • x) (g • y) := by
      rw [hg]
      exact h hr
    simpa only [inv_smul_smul] using s.smul g⁻¹ hs
  · intro h x hx
    exact h hx

/-- The invariant relation induced by the partition consisting of all translates of a
block containing the basepoint. The partition proof comes from `IsBlock.isBlockSystem`. -/
def ofBlock [IsPretransitive G X] {a : X} (B : BlockMem G a) : InvariantSetoid G X :=
  ⟨Setoid.mkClasses (Set.range fun g : G => g • B.1)
      (B.2.2.isBlockSystem ⟨a, B.2.1⟩).1.2,
    by
      rintro g x y h C ⟨k, rfl⟩ hx
      have hx' : x ∈ (g⁻¹ * k) • B.1 := by
        simpa only [mul_smul, inv_smul_smul] using
          (Set.smul_mem_smul_set hx :
            g⁻¹ • (g • x) ∈ g⁻¹ • (k • B.1))
      have hy := h ((g⁻¹ * k) • B.1) ⟨g⁻¹ * k, rfl⟩ hx'
      simpa only [mul_smul, smul_inv_smul] using
        (Set.smul_mem_smul_set hy : g • y ∈ g • ((g⁻¹ * k) • B.1))⟩

/-- The relation constructed from a block is the relation of its translate partition. -/
theorem ofBlock_rel [IsPretransitive G X] {a : X} (B : BlockMem G a) (x y : X) :
    (ofBlock B).1 x y ↔
      ∀ C ∈ Set.range (fun g : G => g • B.1), x ∈ C → y ∈ C :=
  Iff.rfl

/-- Once one point lies in a translate, relatedness is membership in that translate. -/
theorem ofBlock_rel_iff_mem_smul [IsPretransitive G X] {a : X} (B : BlockMem G a)
    (g : G) {x y : X} (hx : x ∈ g • B.1) :
    (ofBlock B).1 x y ↔ y ∈ g • B.1 := by
  have hC : g • B.1 = {z | (ofBlock B).1 z x} :=
    Setoid.eq_eqv_class_of_mem (B.2.2.isBlockSystem ⟨a, B.2.1⟩).1.2 ⟨g, rfl⟩ hx
  rw [hC]
  exact (ofBlock B).1.comm'

/-- The classes of the relation constructed from a block are precisely its translates. -/
theorem classes_ofBlock [IsPretransitive G X] {a : X} (B : BlockMem G a) :
    (ofBlock B).1.classes = Set.range (fun g : G => g • B.1) :=
  Setoid.classes_mkClasses _ (B.2.2.isBlockSystem ⟨a, B.2.1⟩).1

/-- The basepoint class in the translate partition is the original block. -/
@[simp] theorem toBlock_ofBlock [IsPretransitive G X] {a : X} (B : BlockMem G a) :
    toBlock (ofBlock B) a = B := by
  apply Subtype.ext
  exact (Setoid.eq_eqv_class_of_mem (B.2.2.isBlockSystem ⟨a, B.2.1⟩).1.2
    (show B.1 ∈ Set.range (fun g : G => g • B.1) from ⟨1, one_smul G B.1⟩)
    B.2.1).symm

variable (G) in
/-- Invariant equivalence relations correspond to blocks containing a chosen point of a
pretransitive action. Both orders express refinement of the basepoint class. -/
def blockOrderIso [IsPretransitive G X] (a : X) :
    InvariantSetoid G X ≃o BlockMem G a where
  toFun r := toBlock r a
  invFun B := ofBlock B
  left_inv := by
    intro r
    apply Subtype.ext
    apply Setoid.classes_inj.mpr
    exact (classes_ofBlock (toBlock r a)).trans (classes_eq_range_toBlock r a).symm
  right_inv := toBlock_ofBlock
  map_rel_iff' := by
    intro r s
    exact toBlock_le_toBlock_iff a r s

/-- Applying the block correspondence takes the basepoint class. -/
@[simp] theorem blockOrderIso_apply [IsPretransitive G X] (a : X)
    (r : InvariantSetoid G X) : blockOrderIso G a r = toBlock r a :=
  rfl

/-- The inverse block correspondence uses the partition of translates. -/
@[simp] theorem blockOrderIso_symm_apply [IsPretransitive G X] (a : X)
    (B : BlockMem G a) : (blockOrderIso G a).symm B = ofBlock B :=
  rfl

end InvariantSetoid

variable (G) in
/-- Subgroups containing the point stabilizer correspond to invariant equivalence
relations. This is the composite of Mathlib's block classification with the inverse of
`InvariantSetoid.blockOrderIso`, without a new subgroup classification. -/
def stabilizerInvariantSetoidOrderIso [IsPretransitive G X] (a : X) :
    Set.Ici (stabilizer G a) ≃o InvariantSetoid G X :=
  (block_stabilizerOrderIso G a).symm.trans (InvariantSetoid.blockOrderIso G a).symm

/-- The forward map forms the relation from all translates of the basepoint orbit. -/
theorem stabilizerInvariantSetoidOrderIso_apply [IsPretransitive G X] (a : X)
    (K : Set.Ici (stabilizer G a)) :
    stabilizerInvariantSetoidOrderIso G a K =
      InvariantSetoid.ofBlock ((block_stabilizerOrderIso G a).symm K) :=
  rfl

/-- The inverse map is the setwise stabilizer of the basepoint class. -/
theorem stabilizerInvariantSetoidOrderIso_symm_apply [IsPretransitive G X] (a : X)
    (r : InvariantSetoid G X) :
    ((stabilizerInvariantSetoidOrderIso G a).symm r).1 =
      stabilizer G {x | r.1 x a} := by
  have h (B : BlockMem G a) :
      ((block_stabilizerOrderIso G a) B).1 = stabilizer G B.1 := by
    -- Expose both proof fields matched by the stock forward map.
    rcases B with ⟨B, ha, hB⟩
    rw [← OrderIso.coe_toEquiv (block_stabilizerOrderIso G a)]
    simp only [block_stabilizerOrderIso, Equiv.coe_fn_mk]
  simp only [stabilizerInvariantSetoidOrderIso, OrderIso.symm_trans_apply,
    OrderIso.symm_symm, InvariantSetoid.blockOrderIso_apply]
  exact h (InvariantSetoid.toBlock r a)

/-- Inverse subgroup membership is membership in the basepoint relation class. -/
theorem mem_stabilizerInvariantSetoidOrderIso_symm [IsPretransitive G X] (a : X)
    (r : InvariantSetoid G X) (g : G) :
    g ∈ ((stabilizerInvariantSetoidOrderIso G a).symm r).1 ↔ r.1 a (g • a) := by
  rw [stabilizerInvariantSetoidOrderIso_symm_apply, mem_stabilizer_set]
  constructor
  · intro hg
    exact r.1.symm' ((hg a).2 (r.1.refl' a))
  · intro hg x
    change r.1 (g • x) a ↔ r.1 x a
    constructor
    · intro hx
      simpa only [inv_smul_smul] using
        (r.2 (g⁻¹) (g • x) (g • a) (r.1.trans' hx hg))
    · intro hx
      exact r.1.trans' (r.2 g x a hx) (r.1.symm' hg)

/-- The forward relation on translates of the basepoint has the left-coset orientation. -/
theorem stabilizerInvariantSetoidOrderIso_apply_smul [IsPretransitive G X] (a : X)
    (K : Set.Ici (stabilizer G a)) (g h : G) :
    (stabilizerInvariantSetoidOrderIso G a K).1 (g • a) (h • a) ↔ g⁻¹ * h ∈ K.1 := by
  let r := stabilizerInvariantSetoidOrderIso G a K
  have hK : ((stabilizerInvariantSetoidOrderIso G a).symm r).1 = K.1 :=
    congrArg Subtype.val ((stabilizerInvariantSetoidOrderIso G a).symm_apply_apply K)
  -- Translate back to the basepoint before applying the inverse correspondence.
  calc
    r.1 (g • a) (h • a) ↔ r.1 a ((g⁻¹ * h) • a) := by
      constructor
      · intro hgh
        simpa only [← mul_smul, inv_mul_cancel, one_smul] using
          (r.2 (g⁻¹) (g • a) (h • a) hgh)
      · intro hah
        simpa only [mul_smul, smul_inv_smul] using
          (r.2 g a ((g⁻¹ * h) • a) hah)
    _ ↔ g⁻¹ * h ∈ ((stabilizerInvariantSetoidOrderIso G a).symm r).1 :=
      (mem_stabilizerInvariantSetoidOrderIso_symm a r (g⁻¹ * h)).symm
    _ ↔ g⁻¹ * h ∈ K.1 := by rw [hK]

/-- The inverse subgroup is the preimage of the basepoint class under the orbit map. -/
theorem coe_stabilizerInvariantSetoidOrderIso_symm [IsPretransitive G X] (a : X)
    (r : InvariantSetoid G X) :
    (↑((stabilizerInvariantSetoidOrderIso G a).symm r).1 : Set G) =
      (fun g : G => g • a) ⁻¹' {x | r.1 a x} := by
  ext g
  exact mem_stabilizerInvariantSetoidOrderIso_symm a r g

/-- Subgroup inclusion corresponds to refinement, in the same direction. -/
theorem stabilizerInvariantSetoidOrderIso_le_iff [IsPretransitive G X] (a : X)
    (K L : Set.Ici (stabilizer G a)) :
    stabilizerInvariantSetoidOrderIso G a K ≤ stabilizerInvariantSetoidOrderIso G a L ↔
      K.1 ≤ L.1 := by
  exact (stabilizerInvariantSetoidOrderIso G a).map_rel_iff'

/-- For a coset action, the forward relation equals the kernel of the canonical
equivariant quotient map. The domain bound uses `stabilizer_quotient H`. -/
theorem stabilizerInvariantSetoidOrderIso_quotient_ker {H K : Subgroup G} (hHK : H ≤ K) :
    (stabilizerInvariantSetoidOrderIso G (QuotientGroup.mk (s := H) (1 : G))
      ⟨K, (stabilizer_quotient H).le.trans hHK⟩).1 =
        Setoid.ker (MulActionHom.quotientMapOfLE hHK) := by
  apply Setoid.ext
  intro x y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Setoid.ker_def, MulActionHom.quotientMapOfLE_apply_mk,
    MulActionHom.quotientMapOfLE_apply_mk, QuotientGroup.eq]
  simpa only [Quotient.smul_mk, smul_eq_mul, mul_one] using
    (stabilizerInvariantSetoidOrderIso_apply_smul
      (QuotientGroup.mk (s := H) (1 : G))
      ⟨K, (stabilizer_quotient H).le.trans hHK⟩ g h)

/-- The coset forward relation is equality of images under the canonical map. -/
theorem stabilizerInvariantSetoidOrderIso_quotient_rel {H K : Subgroup G} (hHK : H ≤ K)
    (x y : G ⧸ H) :
    (stabilizerInvariantSetoidOrderIso G (QuotientGroup.mk (s := H) (1 : G))
      ⟨K, (stabilizer_quotient H).le.trans hHK⟩).1 x y ↔
        MulActionHom.quotientMapOfLE hHK x = MulActionHom.quotientMapOfLE hHK y := by
  rw [stabilizerInvariantSetoidOrderIso_quotient_ker hHK, Setoid.ker_def]

/-- On representatives the coset forward relation is the usual left-coset criterion. -/
theorem stabilizerInvariantSetoidOrderIso_quotient_mk {H K : Subgroup G} (hHK : H ≤ K)
    (g h : G) :
    (stabilizerInvariantSetoidOrderIso G (QuotientGroup.mk (s := H) (1 : G))
      ⟨K, (stabilizer_quotient H).le.trans hHK⟩).1
        (QuotientGroup.mk g) (QuotientGroup.mk h) ↔ g⁻¹ * h ∈ K := by
  rw [stabilizerInvariantSetoidOrderIso_quotient_rel hHK,
    MulActionHom.quotientMapOfLE_apply_mk, MulActionHom.quotientMapOfLE_apply_mk,
    QuotientGroup.eq]

/-- The identity class is the fiber of the canonical map over the identity coset. -/
theorem stabilizerInvariantSetoidOrderIso_quotient_baseClass {H K : Subgroup G}
    (hHK : H ≤ K) :
    {x | (stabilizerInvariantSetoidOrderIso G (QuotientGroup.mk (s := H) (1 : G))
      ⟨K, (stabilizer_quotient H).le.trans hHK⟩).1 x (QuotientGroup.mk (1 : G))} =
      (MulActionHom.quotientMapOfLE hHK) ⁻¹' {QuotientGroup.mk (s := K) (1 : G)} := by
  ext x
  simpa only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
    MulActionHom.quotientMapOfLE_apply_mk] using
    (stabilizerInvariantSetoidOrderIso_quotient_rel hHK x (QuotientGroup.mk (1 : G)))

/-- The inverse for the coset action recovers a subgroup from the identity class. -/
theorem mem_stabilizerInvariantSetoidOrderIso_quotient_symm (H : Subgroup G)
    (r : InvariantSetoid G (G ⧸ H)) (g : G) :
    g ∈ ((stabilizerInvariantSetoidOrderIso G (QuotientGroup.mk (s := H) (1 : G))).symm r).1 ↔
      r.1 (QuotientGroup.mk (1 : G)) (QuotientGroup.mk g) := by
  simpa only [Quotient.smul_mk, smul_eq_mul, mul_one] using
    (mem_stabilizerInvariantSetoidOrderIso_symm
      (QuotientGroup.mk (s := H) (1 : G)) r g)

end MulAction
