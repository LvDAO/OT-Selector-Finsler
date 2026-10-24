import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.Calibration.CountablePrescribedReachCover
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Probability.ConditionalInverseCoordinates
import OTSelector.Probability.ConditionalInverseGoodPredicate
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerConditionalPrescribedReach.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerConditionalPrescribedReach`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.ConditionalPrescribedReach

* **Conditions:** The same common-label/inverse and chart-density hypotheses as the contact construction, with positive rational reach levels tested explicitly.
* **Objects:** A single C1,1 core family and simultaneous conditional good-witness implications for every positive rational prescribed reach.
* **Proof detail:** Intersect each compact contact core with closed two-sided reach sets, construct matching complete families, and use countability of rational reaches before transferring AE events to both conditionals.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Lemmas 4.9–4.10, p. 33 (Borel strain/end times and closed trimmed strain sets).
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=20): 452E, p. 20: consistency and strong consistency; 452G(a)–(c), p. 21: probability kernels and concentration on fibers.

Source relation (derived): A countable prescribed-reach refinement. It supplies an implication on each reach event and does not assert positive mass on a requested reach interval.
-/

/-!
# Prescribed calibrated reaches under the original conditional clock laws

One original C1,1 cover supplies actual good core witnesses at every positive rational
reach for both original laws. The same label-clock inverse retains the whole reach
implication and both true coordinates on one full set of common labels. No positive
mass on a specified reach set or time interval is needed or concluded.
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

/-- The same original cover has good prescribed-reach cores under both conditional
clock laws, with their true labels and times on one full set of common labels. -/
theorem exists_original_conditional_prescribed_reach_good_cover
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
      (extChartAt 𝓘(ℝ, E) old) ≪ m) :
    letI : MetricSpace M := F.metricSpace
    ∃ ι : Type (max uE uM), Countable ι ∧
      ∃ (old : ι → M) (K U : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (A : ι → E → ℝ → M),
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
        (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧
          U i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ∀ x ∈ U i,
            A i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
            F.IsEulerLagrangeOn (A i x) univ ∧
            ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (A i x) ∧
            F.chartMomentumFamily (old i) (A i) (x, 0) = (x, fderiv ℝ (G i) x)) ∧
        let S : ℚ → Set M := fun q ↦
          OTSelector.Geometry.calibratedReachLevel u (q : ℝ) ∩
            OTSelector.Geometry.calibratedReachLevel (-u) (q : ℝ)
        let C : ι → ℚ → Set E := fun i q ↦
          K i ∩ (extChartAt 𝓘(ℝ, E) (old i)).symm ⁻¹' S q
        (∀ q : ℚ, 0 < q →
          (∀ i, IsCompact (C i q) ∧ ∀ x ∈ C i q, ∃ l r : M,
            dist l ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ) ∧
            u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - u l = (q : ℝ) ∧
            dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) r = (q : ℝ) ∧
            u r - u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ)) ∧
          (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' C i q) = S q) ∧
        let GoodClock : Z → ℝ → Prop := fun z t ↦
          a (b (z, t)) = z ∧ u (b (z, t)) = t ∧
            ∀ q : ℚ, 0 < q → b (z, t) ∈ S q →
              ∃ (i : ι) (x : E), x ∈ C i q ∧
                (extChartAt 𝓘(ℝ, E) (old i)).symm x = b (z, t) ∧
                F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (C i q) x ∧
                F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (q : ℝ) x
        ∀ᵐ z ∂μ.map a,
          (∀ᵐ s ∂condDistrib u a μ z, GoodClock z s) ∧
          (∀ᵐ t ∂condDistrib u a ν z, GoodClock z t) := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨ι, hι, old, K, U, G, L, A, hdata, hcover, hUA, htrim, hgood⟩ :=
    hF.exists_countable_original_prescribed_reach_good_cover hcomplete m hu
  let S : ℚ → Set M := fun q ↦
    calibratedReachLevel u (q : ℝ) ∩ calibratedReachLevel (-u) (q : ℝ)
  let C : ι → ℚ → Set E := fun i q ↦
    K i ∩ (extChartAt 𝓘(ℝ, E) (old i)).symm ⁻¹' S q
  let GoodAll : M → Prop := fun y ↦ ∀ q : ℚ, 0 < q → y ∈ S q →
    ∃ (i : ι) (x : E), x ∈ C i q ∧
      (extChartAt 𝓘(ℝ, E) (old i)).symm x = y ∧
      F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (C i q) x ∧
      F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (q : ℝ) x
  have huMeas : Measurable u := hu.continuous.measurable
  have hμgood : ∀ᵐ y ∂μ, GoodAll y := hgood μ hμchart
  have hνgood : ∀ᵐ y ∂ν, GoodAll y := hgood ν hνchart
  have hμg := ae_condDistrib_good_of_ae_leftInverse μ ha huMeas hb hμinv hμgood
  have hνg := ae_condDistrib_good_of_ae_leftInverse ν ha huMeas hb hνinv hνgood
  have hμc := ae_condDistrib_coordinates_of_ae_leftInverse μ ha huMeas hb hμinv
  have hνc := ae_condDistrib_coordinates_of_ae_leftInverse ν ha huMeas hb hνinv
  rw [← hbalance] at hνg hνc
  refine ⟨ι, hι, old, K, U, G, L, A, hdata, hcover, hUA, htrim, ?_⟩
  filter_upwards [hμg, hνg, hμc, hνc] with z hzgμ hzgν hzcμ hzcν
  constructor
  · filter_upwards [hzgμ.1, hzcμ] with t ht hct
    exact ⟨hct.1, hct.2, ht⟩
  · filter_upwards [hzgν.1, hzcν] with t ht hct
    exact ⟨hct.1, hct.2, ht⟩

end OTSelector.Reconstruction

end
end
