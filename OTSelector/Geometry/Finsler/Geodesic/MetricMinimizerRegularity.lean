import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.ChartLipschitz
import OTSelector.Geometry.Finsler.Geodesic.MetricVelocity
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricMinimizerRegularity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricMinimizerRegularity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricMinimizerRegularity

* **Conditions:** A finite-dimensional C1 Finsler manifold and an original-metric Lipschitz curve; completeness is required only for constructing a minimizing interval.
* **Objects:** Local absolutely continuous coordinates, almost-everywhere manifold differentiability, and nonzero velocities inside isometric intervals.
* **Proof detail:** Compose with locally Lipschitz charts, apply Rademacher on countably many time neighborhoods, and use the metric isometry to exclude zero derivatives.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.

Source relation (derived): Rademacher and complete length-space minimizers are combined locally; smoothness and the Euler–Lagrange equation are established in later modules.
-/

/-!
# First-order regularity of original Finsler metric minimizing intervals

Local coordinate Lipschitz estimates for the original length metric turn every metric
Lipschitz curve into locally absolutely continuous coordinates. Rademacher's theorem
and a countable time cover give almost-everywhere manifold differentiability.
On the interior of any original-distance isometric interval, the actual tangent
exists and is nonzero almost everywhere.
These conclusions apply to the actual metric minimizing intervals constructed from
completeness. They do not yet identify their derivatives with the Euler--Lagrange
flow or assert smoothness.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] [FiniteDimensional ℝ E] [T2Space M]
  [PreconnectedSpace M] (F : ContinuousFinslerNorm E M)

/-- An original-metric Lipschitz curve has absolutely continuous coordinates on a
closed interval around every time, with almost-everywhere differentiability there. -/
theorem exists_regular_chartInterval_of_lipschitzWith
    {c : ℝ → M} {K : ℝ≥0}
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzWith K c) (t₀ : ℝ) :
    ∃ δ > (0 : ℝ), ∃ C : ℝ≥0,
      MapsTo c (Icc (t₀ - δ) (t₀ + δ)) (extChartAt 𝓘(ℝ, E) (c t₀)).source ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c) (Icc (t₀ - δ) (t₀ + δ)) ∧
      AbsolutelyContinuousOnInterval (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c)
        (t₀ - δ) (t₀ + δ) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)),
        DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c) t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)),
        MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t) := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨U, L, hU, htU, hsource, hL⟩ := F.exists_lipschitzOnWith_extChartAt (c t₀)
  have hpre : c ⁻¹' U ∈ 𝓝 t₀ := hc.continuous.continuousAt (hU.mem_nhds htU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hmap : MapsTo c (Icc (t₀ - ε / 2) (t₀ + ε / 2)) U := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hcoord := hL.comp hc.lipschitzOnWith hmap
  have hab : t₀ - ε / 2 ≤ t₀ + ε / 2 := by linarith
  have hac : AbsolutelyContinuousOnInterval (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c)
      (t₀ - ε / 2) (t₀ + ε / 2) := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hcoord
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - ε / 2) (t₀ + ε / 2)),
      DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c) t := by
    have hwithin := (hcoord.mono Ioo_subset_Icc_self).ae_differentiableWithinAt
      (μ := volume) measurableSet_Ioo
    filter_upwards [hwithin, ae_restrict_mem measurableSet_Ioo] with t ht htin
    exact ht.differentiableAt (isOpen_Ioo.mem_nhds htin)
  refine ⟨ε / 2, by positivity, L * K, fun t ht ↦ hsource (hmap ht), hcoord, hac,
    hdiff, ?_⟩
  filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with t ht htin
  have hs : c t ∈ (chartAt E (c t₀)).source := by
    simpa only [← extChartAt_source 𝓘(ℝ, E)] using hsource (hmap (Ioo_subset_Icc_self htin))
  exact (mdifferentiableAt_iff_target_of_mem_source hs).mpr
    ⟨hc.continuous.continuousAt, ht.mdifferentiableAt⟩

/-- Every curve Lipschitz for the original Finsler length metric is manifold
 differentiable almost everywhere in its real time parameter. -/
theorem ae_mdifferentiableAt_of_lipschitzWith
    {c : ℝ → M} {K : ℝ≥0}
    (hc : letI : MetricSpace M := F.metricSpace; LipschitzWith K c) :
    ∀ᵐ t ∂volume, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t := by
  classical
  choose δ hδ C hsource hcoord hac hdiff hmdiff using
    F.exists_regular_chartInterval_of_lipschitzWith hc
  let U : ℝ → Set ℝ := fun t ↦ Ioo (t - δ t) (t + δ t)
  have hcover : univ ⊆ ⋃ t, U t := by
    intro t _
    exact mem_iUnion.mpr ⟨t, by dsimp [U]; constructor <;> linarith [hδ t]⟩
  obtain ⟨S, hS, hScov⟩ := isLindelof_univ.elim_countable_subcover U
    (fun _ ↦ isOpen_Ioo) hcover
  have hfull : (⋃ t ∈ S, U t) = univ := univ_subset_iff.mp hScov
  have hae : ∀ᵐ t ∂volume.restrict (⋃ u ∈ S, U u),
      MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t :=
    (ae_restrict_biUnion_iff U hS _).mpr (fun t _ ↦ hmdiff t)
  simpa only [hfull, Measure.restrict_univ] using hae

/-- Completeness supplies a globally Lipschitz extension of an actual distance-realizing
interval, with local absolutely continuous coordinates and almost-everywhere tangent. -/
theorem exists_regular_lengthMetric_minimizer
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (x y : M) :
    letI : MetricSpace M := F.metricSpace
    ∃ c : ℝ → M, c 0 = x ∧ c (dist x y) = y ∧ LipschitzWith 1 c ∧
      (∀ s ∈ Icc (0 : ℝ) (dist x y), ∀ t ∈ Icc (0 : ℝ) (dist x y),
        dist (c s) (c t) = |s - t|) ∧
      (∀ t₀ : ℝ, ∃ δ > (0 : ℝ),
        MapsTo c (Icc (t₀ - δ) (t₀ + δ)) (extChartAt 𝓘(ℝ, E) (c t₀)).source ∧
        AbsolutelyContinuousOnInterval (extChartAt 𝓘(ℝ, E) (c t₀) ∘ c)
          (t₀ - δ) (t₀ + δ)) ∧
      (∀ᵐ t ∂volume, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t) := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := F.exists_lengthMetric_isometric_interval hcomplete x y
  let c : ℝ → M := γ ∘ projIcc 0 (dist x y) dist_nonneg
  have heq : ∀ t (ht : t ∈ Icc (0 : ℝ) (dist x y)), c t = γ ⟨t, ht⟩ := by
    intro t ht
    simp only [c, Function.comp_apply, projIcc_of_mem _ ht]
  have hc : LipschitzWith 1 c := by
    simpa only [mul_one] using hγ.lipschitzWith.comp (LipschitzWith.projIcc dist_nonneg)
  refine ⟨c, (heq 0 ⟨le_rfl, dist_nonneg⟩).trans hγ0,
    (heq (dist x y) ⟨dist_nonneg, le_rfl⟩).trans hγ1, hc, ?_, ?_,
    F.ae_mdifferentiableAt_of_lipschitzWith hc⟩
  · intro s hs t ht
    rw [heq s hs, heq t ht, hγ.dist_eq]
    exact Real.dist_eq s t
  · intro t
    obtain ⟨δ, hδ, C, hmap, hcoord, hac, _⟩ :=
      F.exists_regular_chartInterval_of_lipschitzWith hc t
    exact ⟨δ, hδ, hmap, hac⟩


/-- Any actual original-distance isometric interval has a nonzero manifold tangent
almost everywhere in its interior; no smoothness of the curve is assumed. -/
theorem ae_nonzero_velocity_of_isometric_interval
    {c : ℝ → M} {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace;
      Isometry (fun t : Icc a b ↦ c t)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 ≠ 0 ∧
      0 < F.toFun ⟨c t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1⟩ := by
  let : MetricSpace M := F.metricSpace
  by_cases hab : a ≤ b
  · let d : ℝ → M := (fun t : Icc a b ↦ c t) ∘ projIcc a b hab
    have hd : LipschitzWith 1 d := by
      simpa only [mul_one] using hiso.lipschitzWith.comp (LipschitzWith.projIcc hab)
    have heq : ∀ t ∈ Ioo a b, d =ᶠ[𝓝 t] c := by
      intro t ht
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      simp only [d, Function.comp_apply, projIcc_of_mem _ hs]
    filter_upwards [ae_restrict_of_ae (F.ae_mdifferentiableAt_of_lipschitzWith hd),
      ae_restrict_mem measurableSet_Ioo] with t hdt ht
    have hct := (heq t ht).mdifferentiableAt_iff.mp hdt
    have hvel := F.mfderiv_apply_one_ne_zero_of_isometry ht hct hiso
    exact ⟨hct, hvel, F.pos (c t) _ hvel⟩
  · have hempty : Ioo a b = ∅ := Ioo_eq_empty_of_le (not_le.mp hab).le
    simp [hempty]

end OTSelector.Geometry.ContinuousFinslerNorm

end
