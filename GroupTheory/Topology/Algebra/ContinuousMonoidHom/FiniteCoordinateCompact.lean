/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import GroupTheory.Topology.Algebra.Group.NoSmallSubgroups.UnitsNeighborhood
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.FiniteCoordinateNeighborhood
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.Compact
public import GroupTheory.Topology.Algebra.ContinuousMonoidHom.CompactFamilies
import GroupTheory.Topology.Pi.FiniteDeviations
import GroupTheory.Topology.ValueSubgroups
import Mathlib.Topology.CompactOpen

/-!
# Uniform finite-coordinate factorization on a compact family

An open identity neighborhood which contains the values of no nontrivial
subgroup of the target's units gives one finite set of coordinates through
which every member of a compact family of continuous homomorphisms factors.
The family has the compact-open topology on the original homomorphism space.
No compatibility between multiplication and the given topologies is assumed.
The same conclusion holds when the target's canonical group of units has no small
subgroups.

If each source factor is locally compact, these compact families also have
common identity-neighborhood control. Evaluation is used only on the common
finite stage, and its neighborhood is pulled back by the original restriction.

The proof constructs a sequence of finite-coordinate extensions of tail
points. Every coordinate is eventually the identity, and each fixed
homomorphism is eventually exactly the identity on this sequence. Compact shifted
ranges produce an increasing compact-open cover of the family.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition
  (background on finite-coordinate factorization).
-/

@[expose] public section

open Filter Topology

universe u v w

namespace ContinuousMonoidHom

private theorem exists_nat_forall_mem_of_isCompact_of_tendsto_of_eventually_eq_one
    {A : Type v} {D : Type w} [Monoid A] [TopologicalSpace A]
    [Monoid D] [TopologicalSpace D]
    (K : Set (A →ₜ* D)) (hK : IsCompact K) (x : ℕ → A)
    (hlim : Filter.Tendsto x Filter.atTop (nhds (1 : A)))
    (heq : ∀ f ∈ K, ∀ᶠ n in Filter.atTop, f (x n) = 1)
    (V : Set D) (hV : IsOpen V) (h1 : (1 : D) ∈ V) :
    ∃ N : ℕ, ∀ f ∈ K, ∀ n ≥ N, f (x n) ∈ V := by
  let C (n : ℕ) : Set A := insert 1 (Set.range fun k : ℕ => x (n + k))
  let U (n : ℕ) : Set (A →ₜ* D) := {f | Set.MapsTo f (C n) V}
  have hshift (n : ℕ) :
      Filter.Tendsto (fun k : ℕ => x (n + k)) Filter.atTop (nhds (1 : A)) := by
    rw [Filter.tendsto_def]
    intro s hs
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually hs)
    exact Filter.eventually_atTop.2
      ⟨N, fun k hk => hN (n + k) (le_trans hk (Nat.le_add_left k n))⟩
  have hcompact (n : ℕ) : IsCompact (C n) := by
    change IsCompact (insert (1 : A) (Set.range fun k : ℕ => x (n + k)))
    apply Filter.Tendsto.isCompact_insert_range_of_cofinite
    simpa only [Nat.cofinite_eq_atTop] using hshift n
  have hprojection : Continuous (fun f : A →ₜ* D => f.toContinuousMap) :=
    continuous_induced_dom
  have hopen (n : ℕ) : IsOpen (U n) := by
    exact (ContinuousMap.isOpen_setOfPred_mapsTo (hcompact n) hV).preimage hprojection
  have hmono : Monotone U := by
    intro m n hmn f hf a ha
    apply hf
    rcases ha with rfl | ⟨k, rfl⟩
    · exact Set.mem_insert 1 _
    · apply Set.mem_insert_of_mem
      refine ⟨n - m + k, ?_⟩
      change x (m + (n - m + k)) = x (n + k)
      rw [← Nat.add_assoc, Nat.add_sub_of_le hmn]
  have hdir : Directed (· ⊆ ·) U := by
    intro m n
    exact ⟨max m n, hmono (le_max_left m n), hmono (le_max_right m n)⟩
  have hcover : K ⊆ ⋃ n, U n := by
    intro f hf
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (heq f hf)
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    intro a ha
    rcases ha with rfl | ⟨k, rfl⟩
    · simpa only [map_one] using h1
    · rw [hN (N + k) (Nat.le_add_right N k)]
      exact h1
  obtain ⟨N, hN⟩ := hK.elim_directed_cover U hopen hcover hdir
  refine ⟨N, ?_⟩
  intro f hf n hn
  apply hN hf
  apply Set.mem_insert_of_mem
  refine ⟨n - N, ?_⟩
  change x (N + (n - N)) = x n
  rw [Nat.add_sub_of_le hn]

variable {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [Monoid D] [TopologicalSpace D]

/-- A compact family of continuous homomorphisms from a product of groups has
one common finite-coordinate factorization if an open identity neighborhood
contains the values of no nontrivial subgroup of the target's units. All
factorizations use the given homomorphisms' canonical finite-coordinate
factors and the original coordinate restrictions. For background, see
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*. -/
theorem exists_eq_finiteCoordinateFactor_comp_restrict_of_isCompact_of_subgroup_values
    (K : Set ((∀ i, G i) →ₜ* D)) (hK : IsCompact K)
    (V : Set D) (hV : IsOpen V) (h1 : (1 : D) ∈ V)
    (hsub : ∀ H : Subgroup Dˣ, (∀ z ∈ H, (z : D) ∈ V) → H = ⊥) :
    ∃ s : Finset ι, ∀ f ∈ K, (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  classical
  by_contra h
  push Not at h
  -- If a whole tail mapped into V, its image in the units would be trivial.
  have hbad (s : Finset ι) :
      ∃ (f : (∀ i, G i) →ₜ* D) (y : ∀ i, G i) (t : Finset ι),
        f ∈ K ∧ (∀ i ∈ s, y i = 1) ∧ f y ∉ V ∧
          (f : (∀ i, G i) → D) =
            (f.finiteCoordinateFactor t : (∀ i : {i // i ∈ t}, G i) → D) ∘
              (fun (x : ∀ i, G i) (i : {i // i ∈ t}) => x i) := by
    obtain ⟨f, hf, hfail⟩ := h s
    have hy : ∃ y : ∀ i, G i, (∀ i ∈ s, y i = 1) ∧ f y ∉ V := by
      by_contra hall
      push Not at hall
      let L : Subgroup (∀ i, G i) :=
        Subgroup.pi (s : Set ι) (fun i => (⊥ : Subgroup (G i)))
      have hone : ∀ a ∈ L, f a = 1 :=
        (f.toMonoidHom.mapsTo_iff_eq_one_of_subgroup_values L V h1 hsub).1 (by
          intro a ha
          exact hall a (by
            intro i hi
            exact ha i hi))
      apply hfail
      refine (f.eq_finiteCoordinateFactor_comp_restrict_iff_eq_one s).2 ?_
      intro a ha
      have haL : a ∈ L := by
        intro i hi
        exact ha i hi
      exact hone a haL
    obtain ⟨y, hy, hnot⟩ := hy
    obtain ⟨t, ht⟩ :=
      f.exists_eq_finiteCoordinateFactor_comp_restrict_of_subgroup_values V hV h1 hsub
    exact ⟨f, y, t, hf, hy, hnot, ht⟩
  choose f y T hf hy hnot hT using hbad
  -- Each new block contains the preceding block and the next factor's coordinates.
  let S : ℕ → Finset ι := Nat.rec ∅ (fun _ s => s ∪ T s)
  have hSstep (n : ℕ) : S n ⊆ S (n + 1) :=
    Finset.subset_union_left
  have hSmono : Monotone S := monotone_nat_of_le_succ hSstep
  have hTsub (n : ℕ) : T (S n) ⊆ S (n + 1) :=
    Finset.subset_union_right
  -- The factor of the identity homomorphism is the canonical extension by one.
  let x : ℕ → (∀ i, G i) := fun n =>
    (MonoidHom.id (∀ i, G i)).finiteCoordinateFactor (T (S n))
      (fun i : {i // i ∈ T (S n)} => y (S n) i)
  have hx (n : ℕ) (i : ι) :
      x n i = if i ∈ T (S n) then y (S n) i else 1 := by
    by_cases hi : i ∈ T (S n) <;>
      simp [x, MonoidHom.finiteCoordinateFactor_apply, hi]
  have hxeval (n : ℕ) : f (S n) (x n) = f (S n) (y (S n)) := by
    simpa [x, ContinuousMonoidHom.finiteCoordinateFactor_apply,
      MonoidHom.finiteCoordinateFactor_apply] using
        (congrFun (hT (S n)) (y (S n))).symm
  have hcoord (i : ι) : ∀ᶠ n in atTop, x n i = 1 := by
    rcases Classical.em (∃ N : ℕ, i ∈ S N) with henter | hnever
    · obtain ⟨N, hN⟩ := henter
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [hx n i]
      split_ifs with ht
      · exact hy (S n) i (hSmono hn hN)
      · rfl
    · apply Filter.Eventually.of_forall
      intro n
      rw [hx n i]
      split_ifs with ht
      · exact False.elim (hnever ⟨n + 1, hTsub n ht⟩)
      · rfl
  have hcofinite : Tendsto x cofinite (𝓝 (1 : ∀ i, G i)) := by
    apply Pi.tendsto_cofinite_of_finite_ne
    intro i
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hcoord i)
    apply (Set.finite_Iio N).subset
    intro n hn
    exact lt_of_not_ge (fun hle => hn (hN n hle))
  have hlim : Tendsto x atTop (𝓝 (1 : ∀ i, G i)) := by
    simpa only [Nat.cofinite_eq_atTop] using hcofinite
  have hfinite (t : Finset ι) : ∀ᶠ n in atTop, ∀ i ∈ t, x n i = 1 := by
    induction t using Finset.induction_on with
    | empty =>
        exact Filter.Eventually.of_forall (by simp)
    | @insert i t hi ih =>
        filter_upwards [hcoord i, ih] with n hni hnt
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hni
        · exact hnt j hj
  have heq : ∀ g ∈ K, ∀ᶠ n in atTop, g (x n) = 1 := by
    intro g _
    obtain ⟨t, ht⟩ :=
      g.exists_eq_finiteCoordinateFactor_comp_restrict_of_subgroup_values V hV h1 hsub
    filter_upwards [hfinite t] with n hn
    exact (g.eq_finiteCoordinateFactor_comp_restrict_iff_eq_one t).1 ht (x n) hn
  obtain ⟨N, hN⟩ :=
    exists_nat_forall_mem_of_isCompact_of_tendsto_of_eventually_eq_one
      K hK x hlim heq V hV h1
  apply hnot (S N)
  rw [← hxeval N]
  exact hN (f (S N)) (hf (S N)) N le_rfl

/-- A compact family of continuous homomorphisms from a product of groups has
one common finite-coordinate factorization when the target's canonical group
of units has no small subgroups. The source groups and target monoid retain
their given arbitrary topologies, and all factorizations use the given maps'
canonical finite-coordinate factors and the original restrictions. No operation
continuity or separation is assumed. For background, see
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*. -/
theorem exists_eq_finiteCoordinateFactor_comp_restrict_of_isCompact_of_noSmallSubgroups_units
    [NoSmallSubgroups Dˣ]
    (K : Set ((∀ i, G i) →ₜ* D)) (hK : IsCompact K) :
    ∃ s : Finset ι, ∀ f ∈ K, (f : (∀ i, G i) → D) =
      (f.finiteCoordinateFactor s : (∀ i : {i // i ∈ s}, G i) → D) ∘
        (fun (x : ∀ i, G i) (i : {i // i ∈ s}) => x i) := by
  obtain ⟨V, hV, h1, hsub⟩ :=
    (Units.noSmallSubgroups_iff_exists_open_subgroup_eq_bot).1
      (inferInstance : NoSmallSubgroups Dˣ)
  exact exists_eq_finiteCoordinateFactor_comp_restrict_of_isCompact_of_subgroup_values
    K hK V hV h1 hsub

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, LocallyCompactSpace (G i)] [Monoid D] [TopologicalSpace D]

/-- If each source factor is locally compact and the target's canonical units
have no small subgroups, a compact family of continuous homomorphisms has one
common source identity neighborhood for every target identity neighborhood.
Only the finite-coordinate stage is required to be locally compact; all maps
and topologies are the original ones. -/
theorem exists_mem_nhds_mapsTo_of_isCompact_of_noSmallSubgroups_units
    [NoSmallSubgroups Dˣ]
    (K : Set ((∀ i, G i) →ₜ* D)) (hK : IsCompact K)
    (W : Set D) (hW : W ∈ 𝓝 (1 : D)) :
    ∃ U : Set (∀ i, G i), U ∈ 𝓝 (1 : ∀ i, G i) ∧
      ∀ f ∈ K, Set.MapsTo (f : (∀ i, G i) → D) U W := by
  classical
  obtain ⟨s, hs⟩ :=
    exists_eq_finiteCoordinateFactor_comp_restrict_of_isCompact_of_noSmallSubgroups_units K hK
  let A := ∀ i : {i // i ∈ s}, G i
  let e : A →ₜ* (∀ i, G i) :=
    (ContinuousMonoidHom.id (∀ i, G i)).finiteCoordinateFactor s
  let R : ((∀ i, G i) →ₜ* D) → C(A, D) := fun f => (f.comp e).toContinuousMap
  have hprecomp : Continuous (fun f : (∀ i, G i) →ₜ* D => f.comp e) := by
    exact continuous_comp_left e
  have hprojection : Continuous (fun f : A →ₜ* D => f.toContinuousMap) :=
    continuous_induced_dom
  have hR : Continuous R := hprojection.comp hprecomp
  let L : Set C(A, D) := R '' K
  have hL : IsCompact L := hK.image hR
  have hLone (g : C(A, D)) (hg : g ∈ L) : g 1 = 1 := by
    rcases hg with ⟨f, _, rfl⟩
    exact map_one (f.comp e)
  have heval : Continuous (fun p : C(A, D) × A => p.1 p.2) := continuous_eval
  -- Compactness of the parameter family turns evaluation rectangles into one tube.
  have hrect (g : L) :
      ∃ O : Set C(A, D), IsOpen O ∧ (g : C(A, D)) ∈ O ∧
        ∃ V : Set A, V ∈ 𝓝 (1 : A) ∧
          ∀ q ∈ O, ∀ x ∈ V, q x ∈ W := by
    have hWg : W ∈ 𝓝 ((g : C(A, D)) 1) := by
      simpa only [hLone _ g.property] using hW
    have hpre : (fun p : C(A, D) × A => p.1 p.2) ⁻¹' W ∈
        𝓝 ((g : C(A, D)), (1 : A)) :=
      heval.continuousAt.preimage_mem_nhds hWg
    rw [nhds_prod_eq] at hpre
    obtain ⟨P, hP, V, hV, hPV⟩ := Filter.mem_prod_iff.mp hpre
    obtain ⟨O, hOP, hO, hgO⟩ := mem_nhds_iff.mp hP
    refine ⟨O, hO, hgO, V, hV, ?_⟩
    intro q hq x hx
    exact hPV (show (q, x) ∈ P ×ˢ V from ⟨hOP hq, hx⟩)
  choose O hO hmem V hV hOV using hrect
  have hcover : L ⊆ ⋃ g : L, O g := by
    intro g hg
    exact Set.mem_iUnion.2 ⟨⟨g, hg⟩, hmem ⟨g, hg⟩⟩
  have hU (t : Finset L) : (⋂ g ∈ t, V g) ∈ 𝓝 (1 : A) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert g t hg ih => simpa using inter_mem (hV g) ih
  obtain ⟨t, ht⟩ := hL.elim_finite_subcover O hO hcover
  let r : (∀ i, G i) → A := fun x i => x i
  have hr : Continuous r := continuous_pi fun i => continuous_apply (i : ι)
  refine ⟨r ⁻¹' (⋂ g ∈ t, V g), hr.continuousAt.preimage_mem_nhds (hU t), ?_⟩
  intro f hf x hx
  have hRf : R f ∈ L := ⟨f, hf, rfl⟩
  rcases Set.mem_iUnion.1 (ht hRf) with ⟨g, hg⟩
  rcases Set.mem_iUnion.1 hg with ⟨hgt, hfg⟩
  have hxV : r x ∈ V g := Set.mem_iInter.1 (Set.mem_iInter.1 hx g) hgt
  have hxW := hOV g (R f) hfg (r x) hxV
  change f.finiteCoordinateFactor s (r x) ∈ W at hxW
  change f x ∈ W
  rw [congrFun (hs f hf) x]
  exact hxW

end ContinuousMonoidHom

namespace ContinuousMonoidHom

variable {ι : Type u} {G : ι → Type v} {D : Type w}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [Group D] [TopologicalSpace D] [IsTopologicalGroup D]

/-- A family of continuous homomorphisms from a product of locally compact groups
into a topological group with no small subgroups is compact if and only if it is
closed, has common identity-neighborhood control, and has relatively compact
values at every point. Only the individual source factors, not their product,
are required to be locally compact. -/
theorem isCompact_iff_of_noSmallSubgroups [NoSmallSubgroups D]
  (K : Set ((∀ i, G i) →ₜ* D)) :
  IsCompact K ↔ IsClosed K ∧
    (∀ W : Set D, W ∈ 𝓝 (1 : D) →
      ∃ U : Set (∀ i, G i), U ∈ 𝓝 (1 : ∀ i, G i) ∧
        ∀ f ∈ K, Set.MapsTo (f : (∀ i, G i) → D) U W) ∧
    ∀ x : (∀ i, G i), IsCompact (closure
      ((fun f : ((∀ i, G i) →ₜ* D) => f x) '' K)) := by
  let _ : T2Space D := inferInstance
  constructor
  · intro hK
    have hunits : NoSmallSubgroups Dˣ :=
      NoSmallSubgroups.of_injective (Units.coeHom D)
        Units.continuous_val.continuousAt (fun _ _ h => Units.ext h)
    let _ : NoSmallSubgroups Dˣ := hunits
    refine ⟨hK.isClosed, ?_, ?_⟩
    · intro W hW
      exact exists_mem_nhds_mapsTo_of_isCompact_of_noSmallSubgroups_units K hK W hW
    · intro x
      let _ : UniformSpace D := IsTopologicalGroup.leftUniformSpace (G := D)
      let 𝔖 : Set (Set (∀ i, G i)) := {s | IsCompact s}
      have heval : Continuous
          (fun g : UniformOnFun (∀ i, G i) D 𝔖 => UniformOnFun.toFun 𝔖 g x) := by
        exact (UniformOnFun.uniformContinuous_eval_of_mem
          (β := D) (𝔖 := 𝔖) (s := {x}) (x := x) (by simp) isCompact_singleton).continuous
      have hevalHom : Continuous (fun f : ((∀ i, G i) →ₜ* D) => f x) :=
        heval.comp
          (isInducing_toUniformOnFunIsCompact (M := ∀ i, G i) (D := D)).continuous
      have himage : IsCompact ((fun f : ((∀ i, G i) →ₜ* D) => f x) '' K) :=
        hK.image hevalHom
      rw [himage.isClosed.closure_eq]
      exact himage
  · rintro ⟨hclosed, hcontrol, hpoint⟩
    apply isCompact_of_isClosed_of_leftEquicontinuous K hclosed
    · intro x W hW
      obtain ⟨U, hU, hmaps⟩ := hcontrol W hW
      have htranslate : Continuous (fun y : (∀ i, G i) => x⁻¹ * y) :=
        continuous_const.mul continuous_id
      have hpre : (fun y : (∀ i, G i) => x⁻¹ * y) ⁻¹' U ∈ 𝓝 x := by
        apply htranslate.continuousAt.preimage_mem_nhds
        simpa only [inv_mul_cancel] using hU
      refine ⟨(fun y : (∀ i, G i) => x⁻¹ * y) ⁻¹' U, hpre, ?_⟩
      intro f hf y hy
      have hvalue : f (x⁻¹ * y) ∈ W := hmaps f hf hy
      simpa only [map_mul, map_inv] using hvalue
    · intro x
      refine ⟨closure ((fun f : ((∀ i, G i) →ₜ* D) => f x) '' K), hpoint x, ?_⟩
      intro f hf
      exact subset_closure ⟨f, hf, rfl⟩

end ContinuousMonoidHom
