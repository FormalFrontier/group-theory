/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.AddCircle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Continuous endomorphisms of the additive circle

For every nonzero real period `T`, the continuous additive endomorphisms of
`AddCircle T` form an additive group isomorphic to `ℤ`. The inverse sends `n` to
the pointwise integer multiple `n • ContinuousAddMonoidHom.id (AddCircle T)`.
In particular, the group law here is pointwise addition, not composition.

The proof lifts an endomorphism along the quotient map `ℝ → AddCircle T`,
normalizes its lift at zero, and uses uniqueness of covering lifts to prove
additivity. A continuous additive map on the real line is real-linear; the
period relation then makes its slope an integer. No sign restriction on `T`
is needed. The zero period is excluded: its quotient is the real line, which
has nonintegral real-multiplier endomorphisms.

## References

The integer-multiple map reuses Mathlib's `zmultiplesHom`. The proof uses
based covering-map lifting in `Mathlib.Topology.Homotopy.Lifting` and continuous
real-additive linearity in `Mathlib.Topology.Instances.RealVectorSpace`.
The additive-circle identification
with the complex circle is provided by `GroupTheory.Topology.AddCircle`; the
classification below stays on the same canonical additive quotient throughout.
-/

@[expose] public section

open scoped ContinuousMap

namespace AddCircle

variable {T : ℝ}

private theorem zsmul_id_apply (n : ℤ) (x : AddCircle T) :
    (n • ContinuousAddMonoidHom.id (AddCircle T)) x = n • x := by
  let ev : (AddCircle T →ₜ+ AddCircle T) →+ AddCircle T :=
    { toFun := fun F => F x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_zsmul ev n (ContinuousAddMonoidHom.id (AddCircle T))

private theorem zsmul_id_injective :
    Function.Injective (fun n : ℤ => n • ContinuousAddMonoidHom.id (AddCircle T)) := by
  intro n m hnm
  have he (x : ℝ) : n • (x : AddCircle T) = m • (x : AddCircle T) := by
    simpa only [zsmul_id_apply] using
      congrArg (fun F : AddCircle T →ₜ+ AddCircle T => F (x : AddCircle T)) hnm
  have hl : (fun x : ℝ => n • x) = (fun x : ℝ => m • x) :=
    (isCoveringMap_coe T).eq_of_comp_eq (by fun_prop) (by fun_prop)
      (by
        funext x
        change ((n • x : ℝ) : AddCircle T) = ((m • x : ℝ) : AddCircle T)
        rw [coe_zsmul, coe_zsmul]
        exact he x) 0 (by simp)
  have hcast : (n : ℝ) = (m : ℝ) := by
    simpa only [zsmul_eq_mul, mul_one] using congrFun hl 1
  exact_mod_cast hcast

private theorem exists_zsmul_id (hT : T ≠ 0) (F : AddCircle T →ₜ+ AddCircle T) :
    ∃ n : ℤ, ∀ x : AddCircle T, F x = n • x := by
  let q : ℝ → AddCircle T := (↑)
  have hq : Continuous q := AddCircle.continuous_mk' T
  obtain ⟨g, ⟨hg0, hgq⟩, _⟩ :=
    (isCoveringMap_coe T).isCoveringMapOn.existsUnique_continuousMap_lifts
      (⟨fun x => F (q x), F.continuous.comp hq⟩ : C(ℝ, AddCircle T))
      (a₀ := 0) (e₀ := 0) (by simp [q]) (by intro x; trivial)
  have hg (x : ℝ) : q (g x) = F (q x) := congrFun hgq x
  have hadd (x y : ℝ) : g (x + y) = g x + g y := by
    have huv : (fun p : ℝ × ℝ => g (p.1 + p.2)) =
        (fun p : ℝ × ℝ => g p.1 + g p.2) :=
      (isCoveringMap_coe T).eq_of_comp_eq
        (g.continuous.comp (continuous_fst.add continuous_snd))
        ((g.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd))
        (by
          funext p
          change q (g (p.1 + p.2)) = q (g p.1 + g p.2)
          rw [show q (g p.1 + g p.2) = q (g p.1) + q (g p.2) from
            coe_add T _ _, hg, hg, hg]
          exact F.map_add (q p.1) (q p.2))
        (0, 0) (by simp [hg0])
    exact congrFun huv (x, y)
  let G : ℝ →+ ℝ :=
    { toFun := g
      map_zero' := hg0
      map_add' := hadd }
  have hlin (x : ℝ) : g x = x * g 1 := by
    simpa only [smul_eq_mul, mul_one, G, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
      map_real_smul G g.continuous x 1
  have hperiod : (g T : AddCircle T) = 0 := by
    change q (g T) = 0
    rw [hg, show q T = 0 from coe_period T, map_zero]
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff T).mp hperiod
  have hn' : (n : ℝ) * T = T * g 1 := by
    rw [hlin T] at hn
    simpa only [zsmul_eq_mul] using hn
  have hslope : g 1 = (n : ℝ) := by
    apply mul_left_cancel₀ hT
    exact hn'.symm.trans (mul_comm _ _)
  refine ⟨n, ?_⟩
  intro x
  induction x using Quotient.inductionOn with
  | h x =>
    change F (q x) = n • (x : AddCircle T)
    rw [← hg x, hlin x, hslope, mul_comm x, ← zsmul_eq_mul]
    exact coe_zsmul T

/-- The additive equivalence classifying continuous additive endomorphisms of
`AddCircle T` by their integer multiplier, for every nonzero real period `T`.
Its inverse is the pointwise integer multiple of the identity homomorphism. -/
noncomputable def continuousAddMonoidHomEquivInt (hT : T ≠ 0) :
    (AddCircle T →ₜ+ AddCircle T) ≃+ ℤ :=
  (AddEquiv.ofBijective
    (_root_.zmultiplesHom (AddCircle T →ₜ+ AddCircle T)
      (ContinuousAddMonoidHom.id (AddCircle T)))
    (by
      constructor
      · exact zsmul_id_injective
      · intro F
        obtain ⟨n, hn⟩ := exists_zsmul_id hT F
        exact ⟨n, ContinuousAddMonoidHom.ext fun x => (zsmul_id_apply n x).trans (hn x).symm⟩)).symm

@[simp]
theorem continuousAddMonoidHomEquivInt_symm_apply (hT : T ≠ 0) (n : ℤ) :
    (continuousAddMonoidHomEquivInt hT).symm n =
      n • ContinuousAddMonoidHom.id (AddCircle T) := rfl

theorem continuousAddMonoidHomEquivInt_symm_apply_apply (hT : T ≠ 0) (n : ℤ)
    (x : AddCircle T) :
    (continuousAddMonoidHomEquivInt hT).symm n x = n • x :=
  zsmul_id_apply n x

/-- Every endomorphism acts by its classifying integer on the original quotient. -/
theorem continuousAddMonoidHomEquivInt_apply (hT : T ≠ 0)
    (F : AddCircle T →ₜ+ AddCircle T) (x : AddCircle T) :
    F x = continuousAddMonoidHomEquivInt hT F • x := by
  have h := congrArg (fun G : AddCircle T →ₜ+ AddCircle T => G x)
    ((continuousAddMonoidHomEquivInt hT).symm_apply_apply F)
  simpa only [continuousAddMonoidHomEquivInt_symm_apply_apply] using h.symm

theorem continuousAddMonoidHomEquivInt_zsmul_id (hT : T ≠ 0) (n : ℤ) :
    continuousAddMonoidHomEquivInt hT (n • ContinuousAddMonoidHom.id (AddCircle T)) = n := by
  simpa only [continuousAddMonoidHomEquivInt_symm_apply] using
    (continuousAddMonoidHomEquivInt hT).apply_symm_apply n

@[simp]
theorem continuousAddMonoidHomEquivInt_id (hT : T ≠ 0) :
    continuousAddMonoidHomEquivInt hT (ContinuousAddMonoidHom.id (AddCircle T)) = 1 := by
  simpa only [one_zsmul] using continuousAddMonoidHomEquivInt_zsmul_id hT 1

/-- Every continuous additive endomorphism of a real additive circle of nonzero
period is multiplication by a unique integer. Negative periods are included. -/
theorem existsUnique_zsmul_continuousAddMonoidHom (hT : T ≠ 0)
    (F : AddCircle T →ₜ+ AddCircle T) :
    ∃! n : ℤ, ∀ x : AddCircle T, F x = n • x := by
  refine ⟨continuousAddMonoidHomEquivInt hT F,
    continuousAddMonoidHomEquivInt_apply hT F, ?_⟩
  intro n hn
  have h : n • ContinuousAddMonoidHom.id (AddCircle T) = F := by
    ext x
    exact (zsmul_id_apply n x).trans (hn x).symm
  simpa only [continuousAddMonoidHomEquivInt_zsmul_id] using
    congrArg (continuousAddMonoidHomEquivInt hT) h

end AddCircle
