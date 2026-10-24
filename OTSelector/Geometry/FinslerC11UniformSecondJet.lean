import OTSelector.Geometry.Finsler.Calibration.PrescribedReach
import OTSelector.MeasureTheory.LusinCompactProperty
import OTSelector.Analysis.Calculus.UniformAmbientSecondJet

/-!
# Uniform actual second jets on prescribed Finsler contact cores

The same original prescribed-reach core supplies both good-point properties.
Lusin and uniform ambient jet estimates retain them on a compact set with
arbitrarily small loss of the original coordinate law, without changing the
contact core used by either property or replacing its extension and curve family.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Retain arbitrarily large original mass in the same prescribed calibrated core,
with both original good-point properties and uniform ambient second jets of the
same C1,1 extension. The good-point predicates retain the original trimmed core. -/
theorem exists_compact_uniform_secondJet_on_prescribed_reach_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ}
    (hu : let _instUniformSecondJetLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ x ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x)
    {A : E → ℝ → M} (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (A x) univ)
    (hinit : ∀ x ∈ U, A x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily old A (x, 0) = (x, fderiv ℝ G x))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    let _instUniformSecondJetMetric : MetricSpace M := F.metricSpace
    let S := OTSelector.Geometry.calibratedReachLevel u Δ ∩
      OTSelector.Geometry.calibratedReachLevel (-u) Δ
    let C := K ∩ (extChartAt 𝓘(ℝ, E) old).symm ⁻¹' S
    IsCompact C ∧
      (∀ x ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm x) = Δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u l = Δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) r = Δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm x) = Δ) ∧
      ∀ ν : Measure E, ν ≪ m → ν C ≠ ⊤ →
        ∀ ε : ℝ≥0∞, ε ≠ 0 →
          ∃ K' ⊆ C, IsCompact K' ∧ ν (C \ K') < ε ∧
            ContinuousOn (fderiv ℝ (fderiv ℝ G)) K' ∧
            (∀ x ∈ K', F.HasC11PotentialFamilyAt m old 0 u G C x ∧
              F.HasC11LevelPositionComparisonAt old G A Δ x) ∧
            ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
              ∀ x ∈ K', ∀ h : E, ‖h‖ < r →
                ‖fderiv ℝ G (x + h) - fderiv ℝ G x -
                  fderiv ℝ (fderiv ℝ G) x h‖ ≤ η * ‖h‖ ∧
                ‖G (x + h) - G x - fderiv ℝ G x h -
                  (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ G) x h h‖ ≤ η * ‖h‖ ^ 2 := by
  let _instUniformSecondJetMetric : MetricSpace M := F.metricSpace
  let S := OTSelector.Geometry.calibratedReachLevel u Δ ∩
    OTSelector.Geometry.calibratedReachLevel (-u) Δ
  let C := K ∩ (extChartAt 𝓘(ℝ, E) old).symm ⁻¹' S
  obtain ⟨hC, hpartners, hgood⟩ :=
    hF.ae_good_on_prescribed_calibrated_reach_core hcomplete old m
      hK hU hKU hUt hu hG hLip hval hactual hEL hinit hp hΔ
  refine ⟨hC, hpartners, ?_⟩
  intro ν hν hνC ε hε
  obtain ⟨H, hHC, hH, hsmallH, hHessH, hGoodH⟩ :=
    OTSelector.Geometry.exists_lusin_compact_core_with_ae_property
      hC.measurableSet hνC (measurable_fderiv ℝ (fderiv ℝ G))
      (hgood ν hν) (ENNReal.half_pos hε).ne'
  have hdiffH : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x :=
    fun x hx ↦ (hGoodH x hx).1.2.2.2.1.differentiableAt
  obtain ⟨K', hK'H, hK', hsmallK', hHessK', hrem⟩ :=
    OTSelector.Geometry.exists_compact_uniform_ambient_secondJet hH
      (ne_top_of_le_ne_top hνC (measure_mono hHC)) hG hdiffH hHessH
      (ENNReal.half_pos hε).ne'
  refine ⟨K', hK'H.trans hHC, hK', ?_, hHessK',
    fun x hx ↦ hGoodH x (hK'H hx), hrem⟩
  calc
    ν (C \ K') ≤ ν (C \ H ∪ (H \ K')) := measure_mono (by
      intro x hx
      by_cases hxH : x ∈ H
      · exact Or.inr ⟨hxH, hx.2⟩
      · exact Or.inl ⟨hx.1, hxH⟩)
    _ ≤ ν (C \ H) + ν (H \ K') := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hsmallH hsmallK'
    _ = ε := ENNReal.add_halves ε

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
