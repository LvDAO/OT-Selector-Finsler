import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerInverseChartLipschitz.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerInverseChartLipschitz`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Coordinates.InverseChartLipschitz

* **Conditions:** A continuous Finsler norm on a finite-dimensional C1 manifold, with the original length metric.
* **Objects:** An inverse chart Lipschitz on a constructed coordinate ball, and a common all-pairs coordinate upper bound for distance.
* **Proof detail:** Choose a convex ball with uniformly bounded inverse-chart differential, integrate its straight segments, and compare their lengths with the distance infimum.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The continuous-norm and all-pairs formulation is derived locally from the classical length integral.
-/

/-!
# Inverse-chart Lipschitz bounds for the original Finsler distance

A uniform bound on the actual inverse-chart differential controls the Finsler
length of every coordinate segment in a sufficiently small convex ball. Hence
all pairs of points in that ball satisfy a common inverse-chart Lipschitz bound.
The corresponding manifold neighborhood gives an original-distance upper bound
by coordinate distance for any two points, with no fixed-endpoint restriction.
-/

open Bundle Set MeasureTheory Manifold Filter Metric
open scoped NNReal ENNReal ContDiff Topology

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  (F : ContinuousFinslerNorm E M)

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse chart is Lipschitz for the original Finsler metric on a constructed
open coordinate ball around the chart center. -/
theorem exists_lipschitzOnWith_extChartAt_symm (x₀ : M) :
    letI : MetricSpace M := F.metricSpace
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧
      ball (extChartAt 𝓘(ℝ, E) x₀ x₀) r ⊆ (extChartAt 𝓘(ℝ, E) x₀).target ∧
      LipschitzOnWith K (extChartAt 𝓘(ℝ, E) x₀).symm
        (ball (extChartAt 𝓘(ℝ, E) x₀ x₀) r) := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let : ∀ x : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) := F.enormSMulClass
  obtain ⟨C, _, hC⟩ := F.eventually_inverse_chart_bound x₀
  have hC' : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℝ, E) x₀ x₀), ∀ v : E,
      (F.toFun ⟨(extChartAt 𝓘(ℝ, E) x₀).symm y,
        mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm
          (range 𝓘(ℝ, E)) y v⟩ : ℝ≥0∞) ≤ C * ‖v‖ₑ := by
    simpa using hC
  have htarget : (extChartAt 𝓘(ℝ, E) x₀).target ∈ 𝓝 (extChartAt 𝓘(ℝ, E) x₀ x₀) := by
    simpa using extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, E)) x₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hC')
  refine ⟨r, C, hr, fun y hy ↦ (hball hy).1, ?_⟩
  intro y hy z hz
  let η := ContinuousAffineMap.lineMap (R := ℝ) y z
  let γ := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt 𝓘(ℝ, E) x₀).target ∩
      {u | ∀ v : E,
        (F.toFun ⟨(extChartAt 𝓘(ℝ, E) x₀).symm u,
          mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm
            (range 𝓘(ℝ, E)) u v⟩ : ℝ≥0∞) ≤ C * ‖v‖ₑ}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact ((convex_ball _ _).segment_subset hy hz).trans hball
  simp only [preimage_inter, subset_inter_iff] at hη
  have hηsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hlength : edist ((extChartAt 𝓘(ℝ, E) x₀).symm y)
      ((extChartAt 𝓘(ℝ, E) x₀).symm z) ≤ pathELength 𝓘(ℝ, E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x₀).comp hηsmooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  apply hlength.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hd : mfderiv[Icc 0 1] γ t =
      (mfderiv[range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) x₀).symm (η t)) ∘L
        (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact hηsmooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x₀))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hda : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) x₀).symm (η t))
        (mfderiv[Icc 0 1] η t 1) := congr($hd 1)
  rw [hda]
  convert! hη.2 ht (mfderiv[Icc 0 1] η t 1) using 1
  simp only [mfderivWithin_eq_fderivWithin]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On a constructed open manifold neighborhood, every pair of original distances is
bounded by a common constant times the pair's distance in the fixed chart. -/
theorem exists_dist_le_mul_dist_extChartAt (x₀ : M) :
    letI : MetricSpace M := F.metricSpace
    ∃ (W : Set M) (K : ℝ≥0), IsOpen W ∧ x₀ ∈ W ∧
      W ⊆ (extChartAt 𝓘(ℝ, E) x₀).source ∧
      ∀ x ∈ W, ∀ y ∈ W,
        dist x y ≤ (K : ℝ) * dist (extChartAt 𝓘(ℝ, E) x₀ x) (extChartAt 𝓘(ℝ, E) x₀ y) := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨r, K, hr, _, hK⟩ := F.exists_lipschitzOnWith_extChartAt_symm x₀
  let W := (extChartAt 𝓘(ℝ, E) x₀).source ∩
    (extChartAt 𝓘(ℝ, E) x₀) ⁻¹' ball (extChartAt 𝓘(ℝ, E) x₀ x₀) r
  refine ⟨W, K, (continuousOn_extChartAt (I := 𝓘(ℝ, E)) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_source x₀) isOpen_ball,
    ⟨mem_extChartAt_source x₀, mem_ball_self hr⟩, inter_subset_left, ?_⟩
  intro x hx y hy
  have h := hK.dist_le_mul _ hx.2 _ hy.2
  simpa only [(extChartAt 𝓘(ℝ, E) x₀).left_inv hx.1,
    (extChartAt 𝓘(ℝ, E) x₀).left_inv hy.1] using h

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
