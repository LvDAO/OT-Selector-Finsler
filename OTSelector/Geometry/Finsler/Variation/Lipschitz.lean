import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLipschitzVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLipschitzVariation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Variation.Lipschitz

* **Conditions:** A Lipschitz coordinate curve in the inner half of an inverse-chart Lipschitz ball, and a Lipschitz additive direction.
* **Objects:** A positive variation radius, genuine chart-valued Lipschitz competitors and preservation of actual endpoints when the direction vanishes there.
* **Proof detail:** Bound the additive displacement uniformly on the compact time interval, choose a small parameter radius, and compose the coordinate Lipschitz bound with the inverse chart.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): Constructs admissible variations explicitly; no differentiability of the central curve is assumed.
-/

/-!
# Admissible Lipschitz coordinate variations for the original metric

A coordinate curve in the inner half of an inverse-chart Lipschitz ball admits
small additive Lipschitz variations within the chart. Vanishing endpoint variation
fixes the actual manifold endpoints. The parameter radius and every original-metric
Lipschitz bound are constructed, without assuming admissibility of the variations.
-/

open Set Metric Manifold
open scoped NNReal ContDiff

noncomputable section

namespace OTSelector.Geometry

private theorem lipschitzOnWith_add_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x η : ℝ → E} {I : Set ℝ} {Kx Kη : ℝ≥0}
    (hx : LipschitzOnWith Kx x I) (hη : LipschitzOnWith Kη η I) (s : ℝ) :
    LipschitzOnWith (Kx + ‖s‖₊ * Kη) (fun t ↦ x t + s • η t) I := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  calc
    dist (x u + s • η u) (x v + s • η v) ≤
        dist (x u) (x v) + dist (s • η u) (s • η v) := dist_add_add_le _ _ _ _
    _ = dist (x u) (x v) + |s| * dist (η u) (η v) := by
      congr 1
      simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
    _ ≤ (Kx : ℝ) * dist u v + |s| * ((Kη : ℝ) * dist u v) :=
      add_le_add (hx.dist_le_mul _ hu _ hv)
        (mul_le_mul_of_nonneg_left (hη.dist_le_mul _ hu _ hv) (abs_nonneg _))
    _ = ((Kx + ‖s‖₊ * Kη : ℝ≥0) : ℝ) * dist u v := by
      simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
      ring

namespace ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] [FiniteDimensional ℝ E] [T2Space M]
  [PreconnectedSpace M] (F : ContinuousFinslerNorm E M)

/-- A Lipschitz coordinate curve inside a half-radius chart ball has a constructed
neighborhood of additive Lipschitz variations. They remain in the actual chart and
are Lipschitz for the original distance, with the actual endpoints fixed. -/
theorem exists_lipschitz_chart_add_variations (old : M)
    {x η : ℝ → E} {a b r : ℝ} {Kx Kη Kinv : ℝ≥0}
    (hr : 0 < r)
    (hball : ball (extChartAt 𝓘(ℝ, E) old old) r ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hinv : letI : MetricSpace M := F.metricSpace
      LipschitzOnWith Kinv (extChartAt 𝓘(ℝ, E) old).symm
        (ball (extChartAt 𝓘(ℝ, E) old old) r))
    (hxball : MapsTo x (Icc a b) (ball (extChartAt 𝓘(ℝ, E) old old) (r / 2)))
    (hx : LipschitzOnWith Kx x (Icc a b)) (hη : LipschitzOnWith Kη η (Icc a b))
    (hηa : η a = 0) (hηb : η b = 0) :
    ∃ ε > (0 : ℝ), ∀ s : ℝ, |s| < ε →
      MapsTo (fun t ↦ x t + s • η t) (Icc a b) (extChartAt 𝓘(ℝ, E) old).target ∧
      (letI : MetricSpace M := F.metricSpace;
        LipschitzOnWith (Kinv * (Kx + ‖s‖₊ * Kη))
          ((extChartAt 𝓘(ℝ, E) old).symm ∘ (fun t ↦ x t + s • η t)) (Icc a b)) ∧
      (extChartAt 𝓘(ℝ, E) old).symm (x a + s • η a) =
        (extChartAt 𝓘(ℝ, E) old).symm (x a) ∧
      (extChartAt 𝓘(ℝ, E) old).symm (x b + s • η b) =
        (extChartAt 𝓘(ℝ, E) old).symm (x b) := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hη.continuousOn
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let ε := r / (2 * B)
  have hε : 0 < ε := div_pos hr (mul_pos (by norm_num) hB)
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hmap : MapsTo (fun t ↦ x t + s • η t) (Icc a b)
      (ball (extChartAt 𝓘(ℝ, E) old old) r) := by
    intro t ht
    have hnorm : ‖η t‖ ≤ B := (hC t ht).trans (by dsimp [B]; linarith [le_max_left C 0])
    have hsB : |s| * B < r / 2 := by
      have h := mul_lt_mul_of_pos_right hs hB
      have heq : ε * B = r / 2 := by dsimp [ε]; field_simp
      rwa [heq] at h
    have hterm : ‖s • η t‖ < r / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)).trans_lt hsB
    have hbase : dist (x t) (extChartAt 𝓘(ℝ, E) old old) < r / 2 := hxball ht
    change dist (x t + s • η t) (extChartAt 𝓘(ℝ, E) old old) < r
    calc
      _ ≤ dist (x t + s • η t) (x t) + dist (x t) (extChartAt 𝓘(ℝ, E) old old) :=
        dist_triangle _ _ _
      _ = ‖s • η t‖ + dist (x t) (extChartAt 𝓘(ℝ, E) old old) := by
        rw [dist_eq_norm, add_sub_cancel_left]
      _ < r := by linarith
  refine ⟨fun _ ht ↦ hball (hmap ht), hinv.comp (lipschitzOnWith_add_smul hx hη s) hmap, ?_, ?_⟩
  · simp only [hηa, smul_zero, add_zero]
  · simp only [hηb, smul_zero, add_zero]

end ContinuousFinslerNorm
end OTSelector.Geometry

end
end
