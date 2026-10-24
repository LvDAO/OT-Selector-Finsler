import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Coordinates.InverseChartLipschitz
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Compact
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerRegularity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricDifferential
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMinimizerChartPhase.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMinimizerChartPhase`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MinimizerChartPhase

* **Conditions:** A smooth strongly convex finite-dimensional Finsler metric and an interior time of an original-distance isometric interval.
* **Objects:** A smaller closed time interval, forward/inverse Lipschitz chart ball and an almost-everywhere compact subset of the actual slit phase domain.
* **Proof detail:** Shrink the curve into a genuine chart ball, use unit speed to bound velocities above and away from zero, and compactify the resulting finite-dimensional phase region.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): This is the local compactness preparation for weak variation, derived from the isometry rather than assumed as an external regularity condition.
-/

/-!
# A compact chart phase for an original-metric minimizing interval

At any interior time of an original-distance isometric interval, construct a smaller
closed time interval and a genuine coordinate ball. Both coordinate maps have the
required Lipschitz bounds, and the actual coordinate phase lies almost everywhere in
a constructed compact subset of the slit energy domain. No coordinate regularity or
compact phase containment is an input.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- Every interior point of an original-distance isometric interval has Lipschitz
coordinates in a smaller genuine chart ball and an almost-everywhere compact slit phase. -/
theorem exists_compact_chartPhase_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    letI : MetricSpace M := F.metricSpace
    let χ := extChartAt 𝓘(ℝ, E) (c t₀)
    let x := χ ∘ c
    ∃ δ > (0 : ℝ), ∃ r > (0 : ℝ), ∃ Kx Kinv : ℝ≥0, ∃ P : Set (E × E),
      Icc (t₀ - δ) (t₀ + δ) ⊆ Ioo a b ∧
      MapsTo c (Icc (t₀ - δ) (t₀ + δ)) χ.source ∧
      MapsTo x (Icc (t₀ - δ) (t₀ + δ)) (ball (χ (c t₀)) (r / 2)) ∧
      LipschitzOnWith Kx x (Icc (t₀ - δ) (t₀ + δ)) ∧
      ball (χ (c t₀)) r ⊆ χ.target ∧
      LipschitzOnWith Kinv χ.symm (ball (χ (c t₀)) r) ∧
      IsCompact P ∧ P ⊆ chartEnergyDomain (c t₀) ∧
      ∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)), (x t, deriv x t) ∈ P := by
  let : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) (c t₀)
  let x : ℝ → E := χ ∘ c
  have hab : a ≤ b := le_of_lt (ht₀.1.trans ht₀.2)
  let d : ℝ → M := (fun t : Icc a b ↦ c t) ∘ projIcc a b hab
  have hd : LipschitzWith 1 d := by
    simpa only [mul_one] using hiso.lipschitzWith.comp (LipschitzWith.projIcc hab)
  have heq : EqOn d c (Icc a b) := by
    intro t ht
    simp only [d, Function.comp_apply, projIcc_of_mem _ ht]
  have hd₀ : d t₀ = c t₀ := heq ⟨ht₀.1.le, ht₀.2.le⟩
  obtain ⟨ε, hε, Kx, hsource, hcoord, _, _, _⟩ :=
    F.exists_regular_chartInterval_of_lipschitzWith hd t₀
  rw [hd₀] at hsource hcoord
  change MapsTo d (Icc (t₀ - ε) (t₀ + ε)) χ.source at hsource
  change LipschitzOnWith Kx (χ ∘ d) (Icc (t₀ - ε) (t₀ + ε)) at hcoord
  obtain ⟨r, Kinv, hr, htarget, hinv⟩ := F.exists_lipschitzOnWith_extChartAt_symm (c t₀)
  change ball (χ (c t₀)) r ⊆ χ.target at htarget
  change LipschitzOnWith Kinv χ.symm (ball (χ (c t₀)) r) at hinv
  have hxcont : ContinuousAt (χ ∘ d) t₀ :=
    hcoord.continuousOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hball : {t | (χ ∘ d) t ∈ ball (χ (c t₀)) (r / 2)} ∈ 𝓝 t₀ := by
    apply hxcont.preimage_mem_nhds
    simpa only [Function.comp_apply, hd₀] using
      (ball_mem_nhds (χ (c t₀)) (half_pos hr))
  have hnear : Ioo a b ∩ Ioo (t₀ - ε) (t₀ + ε) ∩
      {t | (χ ∘ d) t ∈ ball (χ (c t₀)) (r / 2)} ∈ 𝓝 t₀ :=
    inter_mem (inter_mem (Ioo_mem_nhds ht₀.1 ht₀.2)
      (Ioo_mem_nhds (by linarith) (by linarith))) hball
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hsmall : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
      t ∈ Ioo a b ∧ t ∈ Ioo (t₀ - ε) (t₀ + ε) ∧
        (χ ∘ d) t ∈ ball (χ (c t₀)) (r / 2) := by
    intro t ht
    have h := hδsub (show t ∈ closedBall t₀ δ by
      simpa only [Real.closedBall_eq_Icc] using ht)
    exact ⟨h.1.1, h.1.2, h.2⟩
  have heqlocal : EqOn (χ ∘ d) x (Icc (t₀ - δ) (t₀ + δ)) := by
    intro t ht
    exact congrArg χ (heq (Ioo_subset_Icc_self (hsmall t ht).1))
  have hmap : MapsTo c (Icc (t₀ - δ) (t₀ + δ)) χ.source := by
    intro t ht
    rw [← heq (Ioo_subset_Icc_self (hsmall t ht).1)]
    exact hsource (Ioo_subset_Icc_self (hsmall t ht).2.1)
  have hxball : MapsTo x (Icc (t₀ - δ) (t₀ + δ)) (ball (χ (c t₀)) (r / 2)) := by
    intro t ht
    rw [← heqlocal ht]
    exact (hsmall t ht).2.2
  have hxLip : LipschitzOnWith Kx x (Icc (t₀ - δ) (t₀ + δ)) := by
    intro u hu v hv
    rw [← heqlocal hu, ← heqlocal hv]
    exact hcoord (Ioo_subset_Icc_self (hsmall u hu).2.1)
      (Ioo_subset_Icc_self (hsmall v hv).2.1)
  have hbase : closedBall (χ (c t₀)) (r / 2) ⊆ χ.target :=
    (closedBall_subset_ball (half_lt_self hr)).trans htarget
  let P : Set (E × E) := {z | z.1 ∈ closedBall (χ (c t₀)) (r / 2) ∧
    (F.chartLength (c t₀) z : ℝ) ∈ Icc 1 1}
  have hPc : IsCompact P := F.isCompact_chartSpeed_range (c t₀)
    (isCompact_closedBall _ _) hbase 1 1
  have hPU : P ⊆ chartEnergyDomain (c t₀) :=
    F.chartSpeed_range_subset_domain (c t₀) hbase (by norm_num)
  refine ⟨δ, hδ, r, hr, Kx, Kinv, P, fun t ht ↦ (hsmall t ht).1,
    hmap, hxball, hxLip, htarget, hinv, hPc, hPU, ?_⟩
  have hisolocal : Isometry (fun t : Icc (t₀ - δ) (t₀ + δ) ↦ c t) := by
    intro u v
    exact hiso.edist_eq
      ⟨u, Ioo_subset_Icc_self (hsmall u u.property).1⟩
      ⟨v, Ioo_subset_Icc_self (hsmall v v.property).1⟩
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - δ) (t₀ + δ)),
      DifferentiableAt ℝ x t := by
    have hwithin := (hxLip.mono Ioo_subset_Icc_self).ae_differentiableWithinAt
      (μ := volume) measurableSet_Ioo
    filter_upwards [hwithin, ae_restrict_mem measurableSet_Ioo] with t ht htin
    exact ht.differentiableAt (isOpen_Ioo.mem_nhds htin)
  filter_upwards [hF.ae_unit_speed_of_isometric_interval hisolocal, hdiff,
    ae_restrict_mem measurableSet_Ioo] with t hunit hxt ht
  have hspeed := F.speed_eq_chartLength (c t₀) isOpen_Ioo ht
    (fun u hu ↦ hmap (Ioo_subset_Icc_self hu)) hxt
  change F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
    F.chartLength (c t₀) (x t, deriv x t) at hspeed
  refine ⟨ball_subset_closedBall (hxball (Ioo_subset_Icc_self ht)), ?_⟩
  rw [← hspeed, hunit.2.2]
  norm_num

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
