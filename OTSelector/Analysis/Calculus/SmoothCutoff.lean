import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LipschitzPreservingSmoothApproximation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LipschitzPreservingSmoothApproximation`; the selected original proof blocks follow. -/
section

/-!
Conditions: A compact subset lies inside the interior of the larger compact smooth-test support in finite-dimensional real coordinates.

Objects: A genuine smooth cutoff supported in the larger compact and locally one around the smaller compact.

Proof detail: Use a finite collection of smooth local bumps subordinate to the open neighborhood and normalize/combine them to obtain an exact locally-one cutoff.

Sources: Hassler Whitney, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Smooth finite-dimensional localization from the classical partition construction; only the cutoff lemma is extracted, without the original Lipschitz-smoothing conclusions.
-/

/-!
# Lipschitz-preserving smooth approximation with pointwise gradient control

This file supplies the analytic input `CapturesLipschitzDual` of
`LegalRepairEndpointCoupling`.

* A genuine mollification of a `1`-Lipschitz function: convolution with a smooth
  normalized bump preserves the Lipschitz constant exactly, is smooth, and is
  uniformly close by the first moment of the bump.
* A smooth cutoff which is identically one on an open neighborhood of a compact
  set inside the interior of a larger compact set.

Their product keeps the exact dual value on the compact carrier and keeps the
physical gradient bounded there.
-/
open Set Metric MeasureTheory MeasureTheory.Measure TopologicalSpace Filter Function
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction Convolution ContDiff ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Mollification -/

















/-! ## Smooth cutoff -/

/-- A smooth cutoff which is identically one on an open neighborhood of a compact
set inside the interior of a larger compact set. -/
theorem exists_contDiff_cutoff (K : Compacts (ι → ℝ)) {K₀ : Set (ι → ℝ)}
    (hK₀ : IsCompact K₀) (hK₀K : K₀ ⊆ interior (K : Set (ι → ℝ))) :
    ∃ χ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧
      Function.support χ ⊆ (K : Set (ι → ℝ)) ∧
      ∃ U : Set (ι → ℝ), IsOpen U ∧ K₀ ⊆ U ∧ ∀ x ∈ U, χ x = 1 := by
  have hmem : ∀ x : K₀, ∃ d : ℝ, 0 < d ∧
      closedBall x.1 d ⊆ interior (K : Set (ι → ℝ)) := by
    intro x
    exact Metric.nhds_basis_closedBall.mem_iff.1 (isOpen_interior.mem_nhds (hK₀K x.2))
  choose d hdpos hdsub using hmem
  let U : K₀ → Set (ι → ℝ) := fun x => ball x.1 (d x / 2)
  have hUopen : ∀ x, IsOpen (U x) := fun x => isOpen_ball
  have hcover : K₀ ⊆ ⋃ x : K₀, U x := by
    intro y hy
    exact mem_iUnion_of_mem ⟨y, hy⟩ (mem_ball_self (half_pos (hdpos ⟨y, hy⟩)))
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover U hUopen hcover
  let bump : (x : K₀) → ContDiffBump x.1 := fun x =>
    ⟨d x / 2, 3 * d x / 4, half_pos (hdpos x), by linarith [hdpos x]⟩
  let χ : (ι → ℝ) → ℝ := fun y => 1 - ∏ x ∈ t, (1 - bump x y)
  have hprod_smooth : ContDiff ℝ ∞ (fun y => ∏ x ∈ t, (1 - bump x y)) := by
    classical
    refine Finset.induction_on t ?_ ?_
    · simpa only [Finset.prod_empty] using
        (contDiff_const : ContDiff ℝ ∞ fun _ : ι → ℝ => (1 : ℝ))
    · intro a s ha ih
      have h1 : (fun y : ι → ℝ => ∏ x ∈ insert a s, (1 - bump x y)) =
          (fun y => (1 - bump a y) * ∏ x ∈ s, (1 - bump x y)) := by
        funext y
        rw [Finset.prod_insert ha]
      rw [h1]
      exact (ContDiff.sub contDiff_const (bump a).contDiff).mul ih
  have hχsmooth : ContDiff ℝ ∞ χ := ContDiff.sub contDiff_const hprod_smooth
  have hbumpsupp : ∀ x : K₀, Function.support (bump x) ⊆ (K : Set (ι → ℝ)) := by
    intro x z hz
    have hz' : z ∈ ball x.1 (3 * (d x) / 4) := by
      rw [← (bump x).support_eq]
      exact hz
    have hzc : z ∈ closedBall x.1 (d x) :=
      Metric.closedBall_subset_closedBall (by linarith [hdpos x])
        (ball_subset_closedBall hz')
    exact interior_subset (hdsub x hzc)
  have hχsupp : Function.support χ ⊆ (K : Set (ι → ℝ)) := by
    intro y hy
    have hy' : y ∈ ⋃ x ∈ t, Function.support (bump x) := by
      by_contra h
      have hprod : ∏ x ∈ t, (1 - bump x y) = 1 := by
        refine Finset.prod_eq_one fun x hx => ?_
        have hb : bump x y = 0 := by
          by_contra hb
          exact h (mem_iUnion_of_mem x (mem_iUnion_of_mem hx
            (by simpa only [Function.mem_support] using hb)))
        rw [hb]
        ring
      exact (Function.mem_support.1 hy) (by simp only [χ, hprod, sub_self])
    obtain ⟨x, hx, hyx⟩ := by simpa only [mem_iUnion, exists_prop] using hy'
    exact hbumpsupp x hyx
  refine ⟨χ, hχsmooth, hχsupp, ⋃ x ∈ t, U x, ?_, ht, ?_⟩
  · exact isOpen_iUnion fun x => isOpen_iUnion fun _ => hUopen x
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := by simpa only [mem_iUnion, exists_prop] using hy
    have hb : bump x y = 1 :=
      (bump x).one_of_mem_closedBall (ball_subset_closedBall hyx)
    have hprod : ∏ z ∈ t, (1 - bump z y) = 0 := by
      refine Finset.prod_eq_zero hx ?_
      rw [hb]
      ring
    simp only [χ, hprod, sub_zero]

/-! ## Pointwise gradient control and the capture statement -/







end OTSelector.Reconstruction

end
end
