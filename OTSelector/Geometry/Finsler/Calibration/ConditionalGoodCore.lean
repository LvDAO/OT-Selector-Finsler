import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.Calibration.CountableC11Cover
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Probability.ConditionalInverseCoordinates
import OTSelector.Probability.ConditionalInverseGoodPredicate
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerConditionalGoodCore.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerConditionalGoodCore`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.ConditionalGoodCore

* **Conditions:** Two chartwise absolutely continuous finite populations have a common label law, an almost-everywhere inverse label–clock map and full calibrated-interior mass.
* **Objects:** One countable compact C1,1 contact cover and actual good geometric witnesses under both original conditional clock laws, including true inverse coordinates.
* **Proof detail:** Construct the contact cover and its full-measure differentiability comparisons, transfer those events through the supplied inverse and disintegration, then intersect the two AE label sets.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=20): 452E, p. 20: consistency and strong consistency; 452G(a)–(c), p. 21: probability kernels and concentration on fibers.

Source relation (derived): A conditional-law transport of actual contact witnesses; existence of a good clock is only concluded where the normalized conditional law supplies it.
-/

/-!
# Actual original good cores on the common conditional label law

One calibrated contact cover supplies actual good points for both original laws.
The same measurable inverse then preserves the derived geometric witnesses and
both original label-clock coordinates under the scalar conditional laws. Good
times are obtained after intersecting these events, without a measurable choice.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle ProbabilityTheory
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
universe uE uM
namespace OTSelector.Reconstruction

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}
  {Z : Type*} [MeasurableSpace Z] [MeasurableEq Z]

/-- One original calibrated cover supplies actual good core witnesses under both
original conditional clock laws, with their true label and potential time. -/
theorem exists_original_conditional_good_C11_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} {b : Z × ℝ → M} (ha : Measurable a) (hb : Measurable b)
    (hbalance : μ.map a = ν.map a)
    (hμinv : ∀ᵐ y ∂μ, b (a y, u y) = y)
    (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hμI : letI : MetricSpace M := F.metricSpace
      ∀ᵐ y ∂μ, y ∈ calibratedInterior u)
    (hνI : letI : MetricSpace M := F.metricSpace
      ∀ᵐ y ∂ν, y ∈ calibratedInterior u) :
    letI : MetricSpace M := F.metricSpace
    ∃ ι : Type (max uE uM), Countable ι ∧
      ∃ (old : ι → M) (K : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (δ : ι → ℝ) (A : ι → E → ℝ → M),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) =
          OTSelector.Geometry.calibratedInterior u ∧
        (∀ i, 0 < δ i ∧
          (∀ x ∈ K i, ∃ l r : M,
            dist l ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i ∧
            u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - u l = δ i ∧
            dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) r = δ i ∧
            u r - u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i) ∧
          ∀ x ∈ K i,
            A i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
            F.IsEulerLagrangeOn (A i x) univ ∧
            F.chartMomentumFamily (old i) (A i) (x, 0) = (x, fderiv ℝ (G i) x)) ∧
        let GoodClock : Z → ℝ → Prop := fun z t ↦
          ∃ (i : ι) (x : E), x ∈ K i ∧
            (extChartAt 𝓘(ℝ, E) (old i)).symm x = b (z, t) ∧
            F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (K i) x ∧
            F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (δ i) x ∧
            a (b (z, t)) = z ∧ u (b (z, t)) = t
        ∀ᵐ z ∂μ.map a,
          ((∀ᵐ s ∂condDistrib u a μ z, GoodClock z s) ∧ ∃ s, GoodClock z s) ∧
          ((∀ᵐ t ∂condDistrib u a ν z, GoodClock z t) ∧ ∃ t, GoodClock z t) := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨ι, hι, old, K, G, L, δ, A, hdata, hcover, hreach, hgood⟩ :=
    hF.exists_countable_original_good_C11_cover hcomplete m hu
  let Good : M → Prop := fun y ↦ ∃ (i : ι) (x : E), x ∈ K i ∧
    (extChartAt 𝓘(ℝ, E) (old i)).symm x = y ∧
    F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (K i) x ∧
    F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (δ i) x
  let GoodClock : Z → ℝ → Prop := fun z t ↦ ∃ (i : ι) (x : E), x ∈ K i ∧
    (extChartAt 𝓘(ℝ, E) (old i)).symm x = b (z, t) ∧
    F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (K i) x ∧
    F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (δ i) x ∧
    a (b (z, t)) = z ∧ u (b (z, t)) = t
  have huMeas : Measurable u := hu.continuous.measurable
  have hμgood : ∀ᵐ y ∂μ, Good y := hgood μ hμchart hμI
  have hνgood : ∀ᵐ y ∂ν, Good y := hgood ν hνchart hνI
  have hμg := ae_condDistrib_good_of_ae_leftInverse μ ha huMeas hb hμinv hμgood
  have hνg := ae_condDistrib_good_of_ae_leftInverse ν ha huMeas hb hνinv hνgood
  have hμc := ae_condDistrib_coordinates_of_ae_leftInverse μ ha huMeas hb hμinv
  have hνc := ae_condDistrib_coordinates_of_ae_leftInverse ν ha huMeas hb hνinv
  rw [← hbalance] at hνg hνc
  have hclock (η : Measure M) [IsFiniteMeasure η] (z : Z)
      (hg : ∀ᵐ t ∂condDistrib u a η z, Good (b (z, t)))
      (hc : ∀ᵐ t ∂condDistrib u a η z,
        a (b (z, t)) = z ∧ u (b (z, t)) = t) :
      ∀ᵐ t ∂condDistrib u a η z, GoodClock z t := by
    filter_upwards [hg, hc] with t ht hct
    obtain ⟨i, x, hx, hxy, hpotential, hcomparison⟩ := ht
    exact ⟨i, x, hx, hxy, hpotential, hcomparison, hct⟩
  refine ⟨ι, hι, old, K, G, L, δ, A, hdata, hcover, hreach, ?_⟩
  filter_upwards [hμg, hνg, hμc, hνc] with z hzgμ hzgν hzcμ hzcν
  have hμpoint := hclock μ z hzgμ.1 hzcμ
  have hνpoint := hclock ν z hzgν.1 hzcν
  exact ⟨⟨hμpoint, hμpoint.exists⟩, ⟨hνpoint, hνpoint.exists⟩⟩

end OTSelector.Reconstruction

end
end
