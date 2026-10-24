import OTSelector.Analysis.Calculus.MetricPotentialContact
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationTaylor.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationTaylor`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C3 scalar family is defined near a compact center set.

Objects: A common actual Hessian bound and a uniform first-order Taylor error bounded by a constant times squared displacement.

Proof detail: Choose a compact neighborhood inside the smooth domain, bound its Hessian and apply Taylor along each short segment.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Uniform compact Taylor localization; it precedes and does not assume a particular path selection.
-/

/-!
# Uniform first-order Taylor bounds on compact phase sets

A smooth scalar evaluated on a compact set has one actual Hessian bound on a
common neighborhood. The resulting quadratic estimate is available before any
particular variation direction or competitor path is chosen.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace OTSelector.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Pointwise C3 regularity on a compact set produces a common quadratic bound
for the linear Taylor remainder in all sufficiently small directions. -/
theorem exists_uniform_linear_remainder_of_contDiffAt
    {f : V → ℝ} {K : Set V} (hK : IsCompact K)
    (hf : ∀ q ∈ K, ContDiffAt ℝ 3 f q) :
    ∃ r > 0, ∃ C : ℝ≥0, ∀ q ∈ K, ∀ v : V, ‖v‖ ≤ r →
      ‖f (q + v) - f q - fderiv ℝ f q v‖ ≤ (C : ℝ) * ‖v‖ ^ 2 := by
  let U := {q | ContDiffAt ℝ 3 f q}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr
    (fun q hq ↦ (show ContDiffAt ℝ 3 f q from hq).eventually (by norm_num))
  have hfU : ContDiffOn ℝ 3 f U := fun q hq ↦
    (show ContDiffAt ℝ 3 f q from hq).contDiffWithinAt
  obtain ⟨r, hr, hsub⟩ := hK.exists_cthickening_subset_open hU hf
  have hQ : IsCompact (cthickening r K) := hK.cthickening
  let _instHessianNorm : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _instHessianSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ f)) U :=
    (hfU.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C₀, hC₀⟩ := hQ.exists_bound_of_continuousOn (hH.mono hsub)
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  refine ⟨r, hr, C, ?_⟩
  intro q hq v hv
  have hball : closedBall q r ⊆ U := fun z hz ↦
    hsub (mem_cthickening_of_dist_le z q r K hq (mem_closedBall.mp hz))
  have hz : q + v ∈ closedBall q r := by simpa [mem_closedBall, dist_eq_norm] using hv
  have hrem := norm_linear_remainder_le_of_hessian_bound
    (convex_closedBall q r)
    (fun z hz ↦ (hfU.contDiffAt (hU.mem_nhds (hball hz))).differentiableAt (by norm_num))
    (fun z hz ↦ ((hfU.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds (hball hz))).differentiableAt one_ne_zero)
    C.coe_nonneg (fun z hz ↦ (hC₀ z
      (mem_cthickening_of_dist_le z q r K hq (mem_closedBall.mp hz))).trans
        (le_max_left _ _)) (mem_closedBall_self hr.le) hz
  simpa only [add_sub_cancel_left] using hrem

end OTSelector.Geometry

end
end
