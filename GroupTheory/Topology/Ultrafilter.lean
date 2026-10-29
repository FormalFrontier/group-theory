/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Ultrafilter limits as homomorphisms

For a compact Hausdorff monoid with continuous multiplication, taking the limit along a
fixed ultrafilter is a surjective monoid homomorphism on the space of families. There is
also an additive construction using the given additive monoid and continuous addition.

If the ultrafilter contains the cofinite filter, every fiber is dense in the product
topology. For a nontrivial target the homomorphism is not continuous, already at the
constant identity family. In contrast, a principal ultrafilter gives continuous evaluation.

The construction uses Mathlib's `Ultrafilter.lim`, its compactness and uniqueness theorems,
and its convergence API for multiplication. The density argument uses Mathlib's
`exists_finset_piecewise_mem_of_mem_nhds` to modify finitely many coordinates.
-/

@[expose] public section

open Filter Set Topology

universe u v

namespace Ultrafilter

variable {ι : Type u} {H : Type v}
variable [Monoid H] [TopologicalSpace H] [CompactSpace H] [T2Space H] [ContinuousMul H]

/-- Taking the limit of a family along a fixed ultrafilter is a monoid homomorphism. -/
@[to_additive /-- Taking the limit of a family along a fixed ultrafilter is an additive
homomorphism. -/]
noncomputable def limMonoidHom (U : Ultrafilter ι) : (ι → H) →* H where
  toFun f := (Ultrafilter.map f U).lim
  map_one' := tendsto_nhds_unique (Ultrafilter.map (1 : ι → H) U).le_nhds_lim
    tendsto_const_nhds
  map_mul' f g := tendsto_nhds_unique (Ultrafilter.map (f * g) U).le_nhds_lim
    ((show Tendsto f (U : Filter ι) (𝓝 (Ultrafilter.map f U).lim) from
      (Ultrafilter.map f U).le_nhds_lim).mul
      (show Tendsto g (U : Filter ι) (𝓝 (Ultrafilter.map g U).lim) from
        (Ultrafilter.map g U).le_nhds_lim))

/-- The underlying map is the stock limit of the image ultrafilter. -/
@[to_additive /-- The underlying map is the stock limit of the image ultrafilter. -/]
theorem limMonoidHom_apply (U : Ultrafilter ι) (f : ι → H) :
    U.limMonoidHom f = (Ultrafilter.map f U).lim := rfl

/-- Every family converges along the ultrafilter to its value under the homomorphism. -/
@[to_additive /-- Every family converges along the ultrafilter to its value under the
additive homomorphism. -/]
theorem tendsto_limMonoidHom (U : Ultrafilter ι) (f : ι → H) :
    Tendsto f (U : Filter ι) (𝓝 (U.limMonoidHom f)) :=
  (Ultrafilter.map f U).le_nhds_lim

/-- Convergence uniquely characterizes the value of the limit homomorphism. -/
@[to_additive /-- Convergence uniquely characterizes the value of the additive limit
homomorphism. -/]
theorem limMonoidHom_eq_of_tendsto (U : Ultrafilter ι) {f : ι → H} {h : H}
    (hf : Tendsto f (U : Filter ι) (𝓝 h)) : U.limMonoidHom f = h :=
  tendsto_nhds_unique (U.tendsto_limMonoidHom f) hf

/-- The convergence property characterizes the bundled homomorphism. -/
@[to_additive /-- The convergence property characterizes the bundled additive
homomorphism. -/]
theorem limMonoidHom_unique (U : Ultrafilter ι) (L : (ι → H) →* H)
    (hL : ∀ f, Tendsto f (U : Filter ι) (𝓝 (L f))) : L = U.limMonoidHom := by
  ext f
  exact (U.limMonoidHom_eq_of_tendsto (hL f)).symm

/-- Constant families have their constant value as ultrafilter limit. -/
@[to_additive (attr := simp) /-- Constant families have their constant value as
ultrafilter limit. -/]
theorem limMonoidHom_const (U : Ultrafilter ι) (h : H) :
    U.limMonoidHom (fun _ => h) = h :=
  U.limMonoidHom_eq_of_tendsto tendsto_const_nhds

/-- The limit homomorphism is surjective, since it preserves constant families. -/
@[to_additive /-- The additive limit homomorphism is surjective, since it preserves
constant families. -/]
theorem limMonoidHom_surjective (U : Ultrafilter ι) :
    Function.Surjective (U.limMonoidHom : (ι → H) →* H) :=
  fun h => ⟨fun _ => h, U.limMonoidHom_const h⟩

/-- Every fiber is dense when the ultrafilter contains every cofinite set. -/
@[to_additive /-- Every fiber of the additive limit homomorphism is dense when the
ultrafilter contains every cofinite set. -/]
theorem dense_fiber_limMonoidHom (U : Ultrafilter ι) (hU : (U : Filter ι) ≤ cofinite)
    (h : H) : Dense {f : ι → H | U.limMonoidHom f = h} := by
  classical
  intro g
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨F, hF⟩ := exists_finset_piecewise_mem_of_mem_nhds hW (fun _ => h)
  refine ⟨F.piecewise g (fun _ => h), hF, ?_⟩
  apply U.limMonoidHom_eq_of_tendsto
  have heq : F.piecewise g (fun _ => h) =ᶠ[(U : Filter ι)] fun _ => h := by
    filter_upwards [hU F.finite_toSet.compl_mem_cofinite] with i hi
    simp only [Finset.piecewise, Set.mem_compl_iff, Finset.mem_coe] at hi ⊢
    simp [hi]
  exact tendsto_const_nhds.congr' heq.symm

/-- For a free ultrafilter and a nontrivial target, the limit homomorphism is not
continuous at the constant identity family. -/
@[to_additive /-- For a free ultrafilter and a nontrivial target, the additive limit
homomorphism is not continuous at the constant zero family. -/]
theorem not_continuousAt_limMonoidHom [Nontrivial H] (U : Ultrafilter ι)
    (hU : (U : Filter ι) ≤ cofinite) :
    ¬ ContinuousAt (U.limMonoidHom : (ι → H) → H) 1 := by
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  intro hc
  have hn : {h}ᶜ ∈ 𝓝 (U.limMonoidHom (1 : ι → H)) := by
    simpa using isClosed_singleton.isOpen_compl.mem_nhds (Ne.symm hh)
  have hp := hc.preimage_mem_nhds hn
  have hd := U.dense_fiber_limMonoidHom hU h (1 : ι → H)
  rw [mem_closure_iff_nhds] at hd
  obtain ⟨f, hf, hfh⟩ := hd _ hp
  exact hf hfh

/-- For a free ultrafilter and a nontrivial target, the limit homomorphism is not
continuous. -/
@[to_additive /-- For a free ultrafilter and a nontrivial target, the additive limit
homomorphism is not continuous. -/]
theorem not_continuous_limMonoidHom [Nontrivial H] (U : Ultrafilter ι)
    (hU : (U : Filter ι) ≤ cofinite) : ¬ Continuous (U.limMonoidHom : (ι → H) → H) :=
  fun hc => U.not_continuousAt_limMonoidHom hU hc.continuousAt

/-- A principal ultrafilter gives evaluation at its distinguished index. -/
@[to_additive (attr := simp) /-- A principal ultrafilter gives evaluation at its
distinguished index. -/]
theorem limMonoidHom_pure (i : ι) (f : ι → H) :
    (pure i : Ultrafilter ι).limMonoidHom f = f i := by
  apply limMonoidHom_eq_of_tendsto
  simpa using (tendsto_pure_nhds f i)

/-- Principal-ultrafilter limit homomorphisms are continuous. -/
@[to_additive /-- Principal-ultrafilter additive limit homomorphisms are continuous. -/]
theorem continuous_limMonoidHom_pure (i : ι) :
    Continuous ((pure i : Ultrafilter ι).limMonoidHom : (ι → H) → H) := by
  have heq : ((pure i : Ultrafilter ι).limMonoidHom : (ι → H) → H) =
      fun f => f i := funext (limMonoidHom_pure i)
  rw [heq]
  exact continuous_apply i

/-- With a subsingleton target, the limit homomorphism is continuous. -/
@[to_additive /-- With a subsingleton target, the additive limit homomorphism is
continuous. -/]
theorem continuous_limMonoidHom_of_subsingleton [Subsingleton H] (U : Ultrafilter ι) :
    Continuous (U.limMonoidHom : (ι → H) → H) := by
  have heq : (U.limMonoidHom : (ι → H) → H) = fun _ => (1 : H) :=
    funext fun _ => Subsingleton.elim _ _
  rw [heq]
  exact continuous_const

/-- Every nontrivial compact Hausdorff monoid with continuous multiplication is the
surjective image of its countable power under a noncontinuous abstract homomorphism. -/
@[to_additive /-- Every nontrivial compact Hausdorff additive monoid with continuous
addition is the surjective image of its countable power under a noncontinuous abstract
additive homomorphism. -/]
theorem exists_surjective_not_continuous_limMonoidHom [Nontrivial H] :
    ∃ L : (ℕ → H) →* H, Function.Surjective L ∧ ¬ Continuous L := by
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (cofinite : Filter ℕ)
  exact ⟨U.limMonoidHom, U.limMonoidHom_surjective, U.not_continuous_limMonoidHom hU⟩

end Ultrafilter
