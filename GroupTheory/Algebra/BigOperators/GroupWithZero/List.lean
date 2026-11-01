/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import GroupTheory.Algebra.GroupWithZero.Nilpotent

/-!
# Nilpotency bounds for list products

A nilpotent entry that commutes with every entry of a list bounds the nilpotency class
of its product. The other entries need not be nilpotent or commute with one another.
-/

@[expose] public section

universe u

namespace List

/-- A nilpotent entry that commutes with every entry of a list bounds the nilpotency
class of the list product. -/
public theorem nilpotencyClass_prod_le_of_mem
    {M : Type u} [MonoidWithZero M] {l : List M} {a : M}
    (hmem : a ∈ l) (hcomm : ∀ b ∈ l, Commute a b) (hnil : IsNilpotent a) :
    nilpotencyClass l.prod ≤ nilpotencyClass a := by
  obtain ⟨i, hi, ha⟩ :=
    (exists_mem_iff_getElem (l := l) (p := fun x => x = a)).mp ⟨a, hmem, rfl⟩
  refine (Commute.list_prod_right l a hcomm).nilpotencyClass_le_of_dvd ?_ hnil
  refine ⟨(l.eraseIdx i).prod, ?_⟩
  have hfactor := mul_prod_eraseIdx (l := l) hi (by
    intro b hb
    rw [ha]
    exact hcomm b (List.mem_of_mem_take hb))
  simpa only [ha] using hfactor.symm

end List
