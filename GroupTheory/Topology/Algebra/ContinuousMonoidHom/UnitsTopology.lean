/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Units
public import GroupTheory.Topology.ContinuousMap.Inseparable

/-!
# Unit valuation on spaces of continuous monoid homomorphisms

Postcomposition by unit valuation is continuous for the compact-open topology on
continuous monoid homomorphisms. The argument restricts Mathlib's
`ContinuousMap.continuous_postcomp` along the forgetful maps to continuous maps.
No compatibility of the target topology with multiplication is needed.

For a group with continuous inversion, valuation postcomposition is the two-sided
inverse of `ContinuousMonoidHom.toHomUnits`. Consequently the latter map is open.
This does not assert continuity of the unit-lifting map.

Fixed algebraic unit evaluations also give R₁ separation of the homomorphism
space whenever the canonical units are R₁. No continuity of the source group
operations or of multiplication on the target is needed for this criterion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace ContinuousMonoidHom

section Valuation

variable {A : Type u} {D : Type v}
  [Monoid A] [TopologicalSpace A] [Monoid D] [TopologicalSpace D]

/-- Postcomposition of a continuous unit-valued monoid homomorphism by unit valuation. -/
def compUnitsVal (f : A →ₜ* Dˣ) : A →ₜ* D :=
  ({ toMonoidHom := Units.coeHom D
     continuous_toFun := Units.continuous_val } : Dˣ →ₜ* D).comp f

/-- Valuation postcomposition takes the value of the unit at each argument. -/
@[simp]
theorem compUnitsVal_apply (f : A →ₜ* Dˣ) (a : A) :
    f.compUnitsVal a = (f a : D) := by
  exact Units.coeHom_apply (f a)

/-- Unit valuation induces a continuous map on compact-open homomorphism spaces. -/
theorem continuous_compUnitsVal :
    Continuous (compUnitsVal : (A →ₜ* Dˣ) → (A →ₜ* D)) := by
  let val : C(Dˣ, D) := ⟨(fun z => (z : D)), Units.continuous_val⟩
  have hforget : Continuous
      (toContinuousMap : (A →ₜ* Dˣ) → C(A, Dˣ)) := continuous_induced_dom
  have hpost : Continuous
      (fun f : A →ₜ* Dˣ => val.comp f.toContinuousMap) :=
    (ContinuousMap.continuous_postcomp val).comp hforget
  have heq :
      (fun f : A →ₜ* Dˣ => val.comp f.toContinuousMap) =
        (fun f : A →ₜ* Dˣ => f.compUnitsVal.toContinuousMap) := by
    funext f
    apply ContinuousMap.ext
    intro a
    exact (compUnitsVal_apply f a).symm
  rw [heq] at hpost
  exact continuous_induced_rng.2 hpost

end Valuation

section UnitLifting

variable {G : Type u} {D : Type v}
  [Group G] [TopologicalSpace G] [ContinuousInv G] [Monoid D] [TopologicalSpace D]

/-- Valuation postcomposition is a left inverse of the unit lift. -/
@[simp]
theorem compUnitsVal_toHomUnits (f : G →ₜ* D) :
    f.toHomUnits.compUnitsVal = f := by
  apply ContinuousMonoidHom.ext
  intro g
  simp only [compUnitsVal_apply, toHomUnits_apply]

/-- Valuation postcomposition is a right inverse of the unit lift. -/
@[simp]
theorem toHomUnits_compUnitsVal (h : G →ₜ* Dˣ) :
    h.compUnitsVal.toHomUnits = h := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Units.ext
  simp only [toHomUnits_apply, compUnitsVal_apply]

/-- Unit lifting is open because its inverse is continuous valuation postcomposition. -/
theorem isOpenMap_toHomUnits :
    IsOpenMap (toHomUnits : (G →ₜ* D) → (G →ₜ* Dˣ)) := by
  intro s hs
  have himage :
      (toHomUnits : (G →ₜ* D) → (G →ₜ* Dˣ)) '' s =
        (compUnitsVal : (G →ₜ* Dˣ) → (G →ₜ* D)) ⁻¹' s := by
    apply Set.ext
    intro h
    constructor
    · rintro ⟨f, hf, rfl⟩
      simpa only [Set.mem_preimage, compUnitsVal_toHomUnits] using hf
    · intro hh
      exact ⟨h.compUnitsVal, hh, toHomUnits_compUnitsVal h⟩
  rw [himage]
  exact hs.preimage continuous_compUnitsVal

end UnitLifting

end ContinuousMonoidHom

namespace ContinuousMonoidHom

open Filter Topology

section Separation

variable {G : Type u} {D : Type v}
  [Group G] [TopologicalSpace G] [Monoid D] [TopologicalSpace D]

/-- Evaluation of the algebraic unit lift at a fixed source element is continuous. -/
theorem continuous_unitEval (g : G) :
    Continuous (fun f : G →ₜ* D => f.toMonoidHom.toHomUnits g) := by
  have hforget : Continuous
      (toContinuousMap : (G →ₜ* D) → C(G, D)) := continuous_induced_dom
  have heval (a : G) : Continuous (fun f : G →ₜ* D => f a) :=
    (continuous_eval_const a : Continuous (fun f : C(G, D) => f a)).comp hforget
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simpa only [Function.comp_def, MonoidHom.coe_toHomUnits,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe] using heval g
  · have hinv :
        (fun f : G →ₜ* D => (↑((f.toMonoidHom.toHomUnits g)⁻¹) : D)) =
      (fun f : G →ₜ* D => f (g⁻¹)) := by
      funext f
      calc
        (↑((f.toMonoidHom.toHomUnits g)⁻¹) : D) =
            (↑(f.toMonoidHom.toHomUnits (g⁻¹)) : D) :=
          congrArg (fun z : Dˣ => (z : D))
            (map_inv f.toMonoidHom.toHomUnits g).symm
        _ = f (g⁻¹) := by
          simp only [MonoidHom.coe_toHomUnits,
            ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe]
    rw [hinv]
    exact heval (g⁻¹)

/-- Two continuous monoid homomorphisms are inseparable exactly when all their
algebraic unit evaluations are inseparable. -/
theorem inseparable_iff_forall_unitEval {f h : G →ₜ* D} :
    Inseparable f h ↔ ∀ g : G,
      Inseparable (f.toMonoidHom.toHomUnits g) (h.toMonoidHom.toHomUnits g) := by
  constructor
  · intro hfh g
    exact hfh.map (continuous_unitEval g)
  · intro hfh
    have hforget : Topology.IsInducing
        (toContinuousMap : (G →ₜ* D) → C(G, D)) := ⟨rfl⟩
    apply hforget.inseparable_iff.1
    apply ContinuousMap.inseparable_iff_forall_eval.2
    intro g
    simpa only [MonoidHom.coe_toHomUnits,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe,
      ContinuousMonoidHom.coe_toContinuousMap, ContinuousMap.coe_coe] using
      (hfh g).map Units.continuous_val

/-- R₁ separation of canonical units implies R₁ separation of the compact-open
space of continuous monoid homomorphisms from a group with an arbitrary topology. -/
instance instR1SpaceOfUnits [R1Space Dˣ] : R1Space (G →ₜ* D) := by
  classical
  refine r1Space_iff_inseparable_or_disjoint_nhds.2 ?_
  intro f h
  by_cases hfh : Inseparable f h
  · exact Or.inl hfh
  · right
    have hex : ∃ g : G, ¬ Inseparable
        (f.toMonoidHom.toHomUnits g) (h.toMonoidHom.toHomUnits g) := by
      by_contra hn
      apply hfh
      apply inseparable_iff_forall_unitEval.2
      intro g
      by_contra hg
      exact hn ⟨g, hg⟩
    rcases hex with ⟨g, hg⟩
    have hd : Disjoint (nhds (f.toMonoidHom.toHomUnits g))
        (nhds (h.toMonoidHom.toHomUnits g)) := by
      rcases (r1Space_iff_inseparable_or_disjoint_nhds.1
          (inferInstance : R1Space Dˣ))
          (f.toMonoidHom.toHomUnits g) (h.toMonoidHom.toHomUnits g) with hi | hd
      · exact (hg hi).elim
      · exact hd
    have hmap : Disjoint
        (Filter.map (fun k : G →ₜ* D => k.toMonoidHom.toHomUnits g) (nhds f))
        (Filter.map (fun k : G →ₜ* D => k.toMonoidHom.toHomUnits g) (nhds h)) :=
      hd.mono (continuous_unitEval g).continuousAt
        (continuous_unitEval g).continuousAt
    exact Filter.disjoint_of_map hmap

/-- Continuous multiplication on the target suffices for R₁ separation, without
closedness of its identity and without continuity assumptions on source operations. -/
theorem r1Space_of_continuousMul [ContinuousMul D] : R1Space (G →ₜ* D) := by
  let _ : IsTopologicalGroup Dˣ := inferInstance
  let _ : R1Space Dˣ := inferInstance
  exact instR1SpaceOfUnits

end Separation

end ContinuousMonoidHom
