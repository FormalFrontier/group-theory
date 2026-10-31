/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Order.Filter.Curry
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Constructions.SumProd

/-!
# Separate and joint continuity

A least neighborhood in the right factor turns iterated continuity into joint
continuity. In particular, a separately continuous map is jointly continuous
when its right factor is Alexandrov-discrete.

Finite neighborhoods give a local criterion involving finitely many rows and
one column. The corresponding global criteria also apply to scalar multiplication.
-/

@[expose] public section

universe u v w

open scoped Topology

private theorem continuousAt_of_tendsto_curry_of_isLeast_mem_nhds_right
    {S : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    (f : S × X → Y) (s : S) (x : X) (N : Set X)
    (hN : N ∈ 𝓝 x) (hleast : ∀ U ∈ 𝓝 x, N ⊆ U)
    (hiter : Filter.Tendsto f ((𝓝 s).curry (𝓝 x)) (𝓝 (f (s, x)))) :
    ContinuousAt f (s, x) := by
  have hx : 𝓝 x = Filter.principal N :=
    le_antisymm (Filter.le_principal_iff.2 hN) (Filter.principal_le_iff.2 hleast)
  apply Filter.tendsto_def.2
  intro U hU
  have hU' : ∀ᶠ t in 𝓝 s, ∀ᶠ y in 𝓝 x, f (t, y) ∈ U :=
    Filter.eventually_curry_iff.1 (hiter.eventually hU)
  rw [nhds_prod_eq, hx]
  exact Filter.eventually_prod_principal_iff.2
    (Filter.mem_of_superset hU' (fun t ht y hy => hleast _ ht hy))

private theorem exists_isLeast_mem_nhds_subset_of_finite
    {X : Type v} [TopologicalSpace X] (x : X) (V : Set X)
    (hV : V ∈ 𝓝 x) (hfin : V.Finite) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ V ∧ ∀ U ∈ 𝓝 x, N ⊆ U := by
  classical
  let : Fintype V := hfin.fintype
  have hchoice (z : V) :
      ∃ U : Set X, U ∈ 𝓝 x ∧
        ∀ W : Set X, W ∈ 𝓝 x → (z : X) ∉ W → (z : X) ∉ U := by
    by_cases hz : ∃ W : Set X, W ∈ 𝓝 x ∧ (z : X) ∉ W
    · obtain ⟨W, hW, hzW⟩ := hz
      exact ⟨W, hW, fun _ _ _ => hzW⟩
    · exact ⟨Set.univ, Filter.univ_mem, fun W hW hzW => (hz ⟨W, hW, hzW⟩).elim⟩
  choose U hU havoid using hchoice
  let N : Set X := V ∩ ⋂ z : V, U z
  refine ⟨N, Filter.inter_mem hV (Filter.iInter_mem.2 hU), Set.inter_subset_left, ?_⟩
  intro W hW z hz
  by_contra hzW
  exact (havoid ⟨z, hz.1⟩ W hW hzW) (Set.mem_iInter.1 hz.2 ⟨z, hz.1⟩)

/-- A least neighborhood in the right factor turns continuity of the base row and
of every column at the base point into joint continuity. -/
theorem ContinuousAt.of_isLeast_mem_nhds_right
    {S : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    (f : S × X → Y) (s : S) (x : X) (N : Set X)
    (hN : N ∈ 𝓝 x) (hleast : ∀ U ∈ 𝓝 x, N ⊆ U)
    (hrow : ContinuousAt (fun t => f (t, x)) s)
    (hcols : ∀ t, ContinuousAt (fun y => f (t, y)) x) :
    ContinuousAt f (s, x) := by
  apply continuousAt_of_tendsto_curry_of_isLeast_mem_nhds_right f s x N hN hleast
  apply Filter.tendsto_def.2
  intro U hU
  obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.1 hU
  apply Filter.eventually_curry_iff.2
  apply Filter.mem_of_superset (hrow.eventually (hO.mem_nhds hxO))
  intro t ht
  exact Filter.mem_of_superset ((hcols t).eventually (hO.mem_nhds ht))
    (fun y hy => hOU hy)

/-- A separately continuous map is jointly continuous when its right factor is
Alexandrov-discrete. -/
theorem Continuous.of_alexandrovDiscrete_right
    {S : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    [AlexandrovDiscrete X] (f : S × X → Y)
    (hS : ∀ x, Continuous (fun s => f (s, x)))
    (hX : ∀ s, Continuous (fun x => f (s, x))) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, x⟩
  let N : Set X := ⋂₀ {O : Set X | IsOpen O ∧ x ∈ O}
  have hNopen : IsOpen N := isOpen_sInter (fun O hO => hO.1)
  have hxN : x ∈ N := by
    apply Set.mem_sInter.2
    intro O hO
    exact hO.2
  have hleast : ∀ U ∈ 𝓝 x, N ⊆ U := by
    intro U hU y hy
    obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.1 hU
    exact hOU (Set.mem_sInter.1 hy O ⟨hO, hxO⟩)
  exact ContinuousAt.of_isLeast_mem_nhds_right f s x N (hNopen.mem_nhds hxN) hleast
    (hS x).continuousAt (fun t => (hX t).continuousAt)

/-- A finite neighborhood in the right factor turns continuity of its rows at `s`
and of the column at `x` into joint continuity at `(s, x)`. -/
theorem ContinuousAt.of_finite_mem_nhds_right
    {S : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    (f : S × X → Y) (s : S) (x : X) (V : Set X)
    (hV : V ∈ 𝓝 x) (hfin : V.Finite)
    (hrows : ∀ y ∈ V, ContinuousAt (fun t => f (t, y)) s)
    (hcol : ContinuousAt (fun y => f (s, y)) x) :
    ContinuousAt f (s, x) := by
  classical
  obtain ⟨N, hN, hNV, hleast⟩ :=
    exists_isLeast_mem_nhds_subset_of_finite x V hV hfin
  let : Fintype N := (hfin.subset hNV).fintype
  apply continuousAt_of_tendsto_curry_of_isLeast_mem_nhds_right f s x N hN hleast
  apply Filter.tendsto_def.2
  intro U hU
  obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.1 hU
  have hNO : N ⊆ (fun y => f (s, y)) ⁻¹' O :=
    hleast _ (hcol.eventually (hO.mem_nhds hxO))
  let A : Set S := ⋂ y : N, (fun t => f (t, y)) ⁻¹' O
  have hA : A ∈ 𝓝 s := by
    apply Filter.iInter_mem.2
    intro y
    exact (hrows y (hNV y.property)).eventually (hO.mem_nhds (hNO y.property))
  apply Filter.eventually_curry_iff.2
  apply Filter.mem_of_superset hA
  intro t ht
  apply Filter.mem_of_superset hN
  intro y hy
  exact hOU (Set.mem_iInter.1 ht ⟨y, hy⟩)

/-- A separately continuous map is jointly continuous if every point of its right factor
has a finite neighborhood. -/
theorem Continuous.of_finite_nhds_right
    {S : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    (f : S × X → Y) (hLocalX : ∀ x : X, ∃ V ∈ 𝓝 x, V.Finite)
    (hS : ∀ x, Continuous (fun s => f (s, x)))
    (hX : ∀ s, Continuous (fun x => f (s, x))) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, x⟩
  obtain ⟨V, hV, hfin⟩ := hLocalX x
  exact ContinuousAt.of_finite_mem_nhds_right f s x V hV hfin
    (fun y _ => (hS y).continuousAt) (hX s).continuousAt

/-- A separately continuous map with a finite right factor is jointly continuous. -/
theorem Continuous.of_finite_right
    {S : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    [Finite X] (f : S × X → Y)
    (hS : ∀ x, Continuous (fun s => f (s, x)))
    (hX : ∀ s, Continuous (fun x => f (s, x))) :
    Continuous f :=
  Continuous.of_finite_nhds_right f
    (fun _ => ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩) hS hX

/-- Separately continuous scalar multiplication is jointly continuous if every point
has a finite neighborhood. -/
@[to_additive /-- Separately continuous vector addition is jointly continuous if every point
has a finite neighborhood. -/]
theorem ContinuousSMul.of_finite_nhds_right
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [SMul M X] [ContinuousConstSMul M X]
    (hLocalX : ∀ x : X, ∃ V ∈ 𝓝 x, V.Finite)
    (h : ∀ x : X, Continuous (fun m : M => m • x)) :
    ContinuousSMul M X :=
  ⟨Continuous.of_finite_nhds_right (fun p : M × X => p.1 • p.2)
    hLocalX h (fun m => continuous_const_smul m)⟩

/-- Separately continuous scalar multiplication on a finite space is jointly continuous. -/
@[to_additive /-- Separately continuous vector addition on a finite space is jointly continuous. -/]
theorem ContinuousSMul.of_finite_right
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [SMul M X] [Finite X] [ContinuousConstSMul M X]
    (h : ∀ x : X, Continuous (fun m : M => m • x)) :
    ContinuousSMul M X :=
  ContinuousSMul.of_finite_nhds_right
    (fun _ => ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩) h

