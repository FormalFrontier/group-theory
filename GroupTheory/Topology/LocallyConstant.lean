/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.End

/-!
# Locally constant families of bijections

For a finite T0 space `A`, a family `F : X → A → A` of bijections is locally
constant whenever every evaluation `fun x => F x a` is continuous. The topology on
`A` need not be discrete, and neither the bijections nor their inverses are
assumed continuous. Local constancy means equality of whole function values on
one open neighborhood, with no additional assumption on `X`.
-/

@[expose] public section

universe u v

-- Pointwise specialization determines bijections on a finite T0 space.
private theorem eq_of_bijective_of_specializes {A : Type v}
    [TopologicalSpace A] [Finite A] [T0Space A]
    (p q : A → A) (hp : Function.Bijective p) (hq : Function.Bijective q)
    (h : ∀ a, Specializes (p a) (q a)) : p = q := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let P : Equiv.Perm A := Equiv.ofBijective p hp
  let Q : Equiv.Perm A := Equiv.ofBijective q hq
  let r : Equiv.Perm A := P.symm.trans Q
  have hr (b : A) : Specializes b (r b) := by
    change Specializes b (Q (P.symm b))
    have hb : Specializes (P (P.symm b)) (Q (P.symm b)) := h (P.symm b)
    simpa only [Equiv.apply_symm_apply] using hb
  -- Each step uses hr at that orbit point, not monotonicity of r.
  have hchain (n : ℕ) (b : A) : Specializes b ((r ^ n) b) := by
    induction n with
    | zero =>
        change Specializes b b
        exact specializes_refl b
    | succ n ih =>
        rw [pow_succ']
        exact ih.trans (hr ((r ^ n) b))
  have hpos : 0 < orderOf r := orderOf_pos r
  obtain ⟨n, hn⟩ : ∃ n : ℕ, orderOf r = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hreturn : r ^ (n + 1) = 1 := by
    simpa only [hn] using (pow_orderOf_eq_one r)
  have hfix (b : A) : r b = b := by
    have hlast : (r ^ n) (r b) = b := by
      change (r ^ n * r) b = b
      rw [← pow_succ, hreturn]
      rfl
    have hback : Specializes (r b) b := by
      simpa only [hlast] using (hchain n (r b))
    exact (hback.antisymm (hr b)).eq
  funext a
  have ha := hfix (P a)
  change Q (P.symm (P a)) = P a at ha
  have hqa : Q a = P a := by
    simpa only [Equiv.symm_apply_apply] using ha
  exact hqa.symm

private theorem exists_open_forall_specializes {X : Type u} {A : Type v}
    [TopologicalSpace X] [TopologicalSpace A] [Finite A]
    (F : X → A → A)
    (heval : ∀ a, Continuous (fun x => F x a)) (x0 : X) :
    ∃ N : Set X, IsOpen N ∧ x0 ∈ N ∧
      ∀ x ∈ N, ∀ a, Specializes (F x a) (F x0 a) := by
  classical
  let U : A → Set A := fun b =>
    ⋂ s : {s : Set A // IsOpen s ∧ b ∈ s}, (s : Set A)
  have hUopen (b : A) : IsOpen (U b) := by
    exact isOpen_iInter_of_finite (fun s => s.property.1)
  have hUmem (b : A) : b ∈ U b := by
    exact Set.mem_iInter.mpr (fun s => s.property.2)
  let N : Set X :=
    ⋂ a : A, (fun x : X => F x a) ⁻¹' U (F x0 a)
  refine ⟨N, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite
      (fun a => (hUopen (F x0 a)).preimage (heval a))
  · exact Set.mem_iInter.mpr (fun a => hUmem (F x0 a))
  · intro x hx a
    refine specializes_iff_forall_open.mpr ?_
    intro s hs hmem
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hx a) ⟨s, hs, hmem⟩

/-- A family of bijections of a finite T0 space is locally constant if every
parameter evaluation is continuous.

No discreteness assumption on `A` or continuity of the individual bijections is
required. Around each point of `X`, one open neighborhood makes the whole
function `F x : A → A` equal to its value at that point. -/
theorem isLocallyConstant_of_continuous_eval_of_bijective (X : Type u) (A : Type v)
    [TopologicalSpace X] [TopologicalSpace A] [Finite A] [T0Space A]
    (F : X → A → A)
    (hbij : ∀ x : X, Function.Bijective (F x))
    (heval : ∀ a : A, Continuous (fun x : X => F x a)) :
    IsLocallyConstant F := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro g
  refine isOpen_iff_mem_nhds.mpr ?_
  intro x0 hx0
  obtain ⟨N, hNopen, hx0N, hN⟩ := exists_open_forall_specializes F heval x0
  refine Filter.mem_of_superset (hNopen.mem_nhds hx0N) ?_
  intro x hxN
  exact (eq_of_bijective_of_specializes (F x) (F x0)
    (hbij x) (hbij x0) (hN x hxN)).trans hx0
