import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11ShortTranslation
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.MeasureTheory.HaarLipschitzDistortion
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11VolumeTranslation

* **Conditions:** A C1,1 extension matching the original calibrated core and two-sided actual partners.
* **Objects:** Actual short translations with two-sided Haar volume distortion and exact original potential clock on the core.
* **Proof detail:** Construct the half-Lipschitz displacement map, derive its inverse Lipschitz/image-volume bounds and combine with same-curve calibration.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38): Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11VolumeTranslation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11VolumeTranslation`; the selected original proof blocks follow. -/
section

/-!
# Actual calibrated C1,1 translations with Haar volume bounds

A C1,1 extension of the actual potential covector constructs the same complete original
geodesics on a coordinate ball. Two-sided calibrated partners supply differentiability
and the initial unit covector. Short translations have uniform two-sided Haar distortion,
while on the original core their potential clock and distance calibration are exact.
-/

open Set Filter Metric Manifold Bundle MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Actual calibrated C1,1 covectors generate complete original geodesics with a jointly
Lipschitz short-time coordinate readout, retaining the original clock and Haar bounds. -/
theorem exists_C11_calibrated_volume_translation_lipschitz (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {K : Set E} (hK : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instVolumeTranslationLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instVolumeTranslationPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {x₀ : E} (hx₀ : x₀ ∈ K) :
    let _instVolumeTranslationResult : MetricSpace M := F.metricSpace
    ∃ (r τ : ℝ) (Γ : E → ℝ → M), 0 < r ∧ 0 < τ ∧ τ ≤ δ / 2 ∧
      closedBall x₀ r ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      (∀ x ∈ closedBall x₀ r,
        Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x ∧
        F.IsEulerLagrangeOn (Γ x) univ ∧
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Γ x) ∧
        F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x)) ∧
      ContinuousOn (fun q : ℝ × E ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1))
        (Icc (-τ) τ ×ˢ closedBall x₀ r) ∧
      (∃ C : ℝ≥0, LipschitzOnWith C
        (fun q : ℝ × E ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1))
        (Icc (-τ) τ ×ˢ closedBall x₀ r)) ∧
      (∀ t ∈ Icc (-τ) τ,
        MapsTo (fun x ↦ Γ x t) (closedBall x₀ r) (extChartAt 𝓘(ℝ, E) old).source ∧
        LipschitzOnWith (1 / 2) (fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t) - x)
          (closedBall x₀ r) ∧
        ∀ B ⊆ closedBall x₀ r,
          m ((fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t)) '' B) ≤
            (3 / 2 : ℝ≥0∞) ^ Module.finrank ℝ E * m B ∧
          m B ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E *
            m ((fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t)) '' B)) ∧
      ∀ x ∈ K ∩ closedBall x₀ r,
        (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ x) ⟨t, (1 : ℝ)⟩) = 1) ∧
        Isometry (fun t : Icc (-δ) δ ↦ Γ x t) ∧
        (∀ t ∈ Icc (-δ) δ,
          u (Γ x t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t ∧
          |u (Γ x t) - u ((extChartAt 𝓘(ℝ, E) old).symm x)| =
            dist ((extChartAt 𝓘(ℝ, E) old).symm x) (Γ x t)) ∧
        ∀ t ∈ Icc (-τ) τ,
          Γ x t ∈ OTSelector.Geometry.calibratedInterior u ∧
          Γ x t ∈ F.potentialRegularDomain u := by
  let _instVolumeTranslationMetric : MetricSpace M := F.metricSpace
  have hd : ∀ x ∈ K, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm x) := by
    intro x hx
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners x hx
    apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    refine ⟨⟨a, ?_, ha.trans hax.symm⟩, ⟨b, ?_, hb.trans hxb.symm⟩⟩
    · exact dist_pos.mp (hax.symm ▸ hδ)
    · exact dist_pos.mp (hxb.symm ▸ hδ)
  have hforward : ∀ x ∈ K, ∃ b : M,
      (extChartAt 𝓘(ℝ, E) old).symm x ≠ b ∧
      u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) =
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b := by
    intro x hx
    obtain ⟨a, b, _, _, hxb, hb⟩ := hpartners x hx
    exact ⟨b, dist_pos.mp (hxb.symm ▸ hδ), hb.trans hxb.symm⟩
  obtain ⟨v₀, hv₀, hp₀, _⟩ :=
    hF.chart_unit_legendre_on_of_calibrated_endpoints hcomplete old hK hu hd hforward x₀ hx₀
  obtain ⟨r, τ₀, Γ, hr, hτ₀, hball, hinit, hcont, ⟨C, hjoint⟩, hflow⟩ :=
    hF.exists_C11_short_geodesic_translation_lipschitz hcomplete old hG hLip hv₀
      (hp₀.trans (hmatch hx₀).symm)
  let τ := min τ₀ (δ / 2)
  have hτ : 0 < τ := lt_min hτ₀ (half_pos hδ)
  have htime : Icc (-τ) τ ⊆ Icc (-τ₀) τ₀ := by
    intro t ht
    have hh : τ ≤ τ₀ := min_le_left _ _
    exact ⟨by linarith [ht.1], ht.2.trans hh⟩
  refine ⟨r, τ, Γ, hr, hτ, min_le_right _ _, hball, hinit, ?_, ?_, ?_, ?_⟩
  · exact hcont.mono (fun _ hq ↦ ⟨htime hq.1, hq.2⟩)
  · exact ⟨C, hjoint.mono (fun _ hq ↦ ⟨htime hq.1, hq.2⟩)⟩
  · intro t ht
    obtain ⟨hsource, hres⟩ := hflow t (htime ht)
    refine ⟨hsource, hres, ?_⟩
    exact (haar_image_distortion_of_half_lipschitz_displacement m hres).2.2.2
  · intro x hx
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners x hx.1
    obtain ⟨hzero, hEL, _, hmomentum⟩ := hinit x hx.2
    have hp : F.chartMomentumFamily old Γ (x, 0) =
        (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x) := by
      rw [hmomentum, hmatch hx.1]
    obtain ⟨hunit, _, _, hclock, hiso, hcal⟩ :=
      hF.calibrated_translation_of_chartMomentum hcomplete old hu (hK hx.1) hEL hzero
        hp (hd x hx.1) hδ ⟨hax, ha⟩ ⟨hxb, hb⟩
    refine ⟨hunit, hiso, fun t ht ↦ ⟨hclock t ht, hcal t ht⟩, ?_⟩
    intro t ht
    have htδ : t ∈ Ioo (-δ) δ := by
      have hτhalf : τ ≤ δ / 2 := min_le_right _ _
      constructor <;> linarith [ht.1, ht.2]
    have hinterior : Γ x t ∈ OTSelector.Geometry.calibratedInterior u := by
      have hle : -δ ≤ δ := by linarith
      have htclosed : t ∈ Icc (-δ) δ := ⟨htδ.1.le, htδ.2.le⟩
      have hlo : -δ ∈ Icc (-δ) δ := ⟨le_rfl, hle⟩
      have hhi : δ ∈ Icc (-δ) δ := ⟨hle, le_rfl⟩
      have hdistlo : dist (Γ x (-δ)) (Γ x t) = t + δ := by
        have hh := hiso.dist_eq ⟨-δ, hlo⟩ ⟨t, htclosed⟩
        change dist (Γ x (-δ)) (Γ x t) = dist (-δ) t at hh
        rw [Real.dist_eq, abs_of_nonpos (by linarith [htδ.1])] at hh
        linarith
      have hdisthi : dist (Γ x t) (Γ x δ) = δ - t := by
        have hh := hiso.dist_eq ⟨t, htclosed⟩ ⟨δ, hhi⟩
        change dist (Γ x t) (Γ x δ) = dist t δ at hh
        rw [Real.dist_eq, abs_of_nonpos (by linarith [htδ.2])] at hh
        linarith
      refine ⟨⟨Γ x (-δ), ?_, ?_⟩, ⟨Γ x δ, ?_, ?_⟩⟩
      · apply dist_pos.mp
        rw [hdistlo]
        linarith [htδ.1]
      · rw [hclock t htclosed, hclock (-δ) hlo, hdistlo]
        ring
      · apply dist_pos.mp
        rw [hdisthi]
        linarith [htδ.2]
      · rw [hclock δ hhi, hclock t htclosed, hdisthi]
        ring
    exact ⟨hinterior,
      hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu hinterior⟩

/-- The actual covectors of a two-sided calibrated C1,1 core generate complete original
geodesics with jointly continuous short translations and uniform Haar image bounds.
The same curves retain the original potential clock and distance throughout the trimmed
calibrated interval. Initial unit states and potential differentiability are constructed. -/
theorem exists_C11_calibrated_volume_translation (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {K : Set E} (hK : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instVolumeTranslationLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instVolumeTranslationPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {x₀ : E} (hx₀ : x₀ ∈ K) :
    let _instVolumeTranslationResult : MetricSpace M := F.metricSpace
    ∃ (r τ : ℝ) (Γ : E → ℝ → M), 0 < r ∧ 0 < τ ∧ τ ≤ δ / 2 ∧
      closedBall x₀ r ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      (∀ x ∈ closedBall x₀ r,
        Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x ∧
        F.IsEulerLagrangeOn (Γ x) univ ∧
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Γ x) ∧
        F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x)) ∧
      ContinuousOn (fun q : ℝ × E ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1))
        (Icc (-τ) τ ×ˢ closedBall x₀ r) ∧
      (∀ t ∈ Icc (-τ) τ,
        MapsTo (fun x ↦ Γ x t) (closedBall x₀ r) (extChartAt 𝓘(ℝ, E) old).source ∧
        LipschitzOnWith (1 / 2) (fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t) - x)
          (closedBall x₀ r) ∧
        ∀ B ⊆ closedBall x₀ r,
          m ((fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t)) '' B) ≤
            (3 / 2 : ℝ≥0∞) ^ Module.finrank ℝ E * m B ∧
          m B ≤ (2 : ℝ≥0∞) ^ Module.finrank ℝ E *
            m ((fun x ↦ extChartAt 𝓘(ℝ, E) old (Γ x t)) '' B)) ∧
      ∀ x ∈ K ∩ closedBall x₀ r,
        (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ x) ⟨t, (1 : ℝ)⟩) = 1) ∧
        Isometry (fun t : Icc (-δ) δ ↦ Γ x t) ∧
        (∀ t ∈ Icc (-δ) δ,
          u (Γ x t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t ∧
          |u (Γ x t) - u ((extChartAt 𝓘(ℝ, E) old).symm x)| =
            dist ((extChartAt 𝓘(ℝ, E) old).symm x) (Γ x t)) ∧
        ∀ t ∈ Icc (-τ) τ,
          Γ x t ∈ OTSelector.Geometry.calibratedInterior u ∧
          Γ x t ∈ F.potentialRegularDomain u := by
  obtain ⟨r, τ, Γ, hr, hτ, hτδ, hball, hinit, hcont, _, hflow, hcalibrated⟩ :=
    hF.exists_C11_calibrated_volume_translation_lipschitz hcomplete old m hK hu
      hG hLip hmatch hδ hpartners hx₀
  exact ⟨r, τ, Γ, hr, hτ, hτδ, hball, hinit, hcont, hflow, hcalibrated⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
