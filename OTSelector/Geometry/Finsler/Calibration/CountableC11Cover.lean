import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.C11PotentialTube
import OTSelector.Geometry.Finsler.C11SmoothTubeCover
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11OriginalGoodCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11OriginalGoodCover`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.CountableC11Cover

* **Conditions:** Smooth strong convexity, complete original Finsler metric and a 1-Lipschitz potential; each population is only assumed chartwise absolutely continuous and carried by the calibrated interior.
* **Objects:** One countable compact C1,1 contact cover, fixed before the population, with actual potential-family and position-comparison witnesses almost everywhere for every such population.
* **Proof detail:** Construct the geometric cover first, derive its coordinate AE comparisons, then transfer their null exceptions through restricted chart pushforwards.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).

Source relation (derived): A law-independent contact-cover and AE-transfer construction; no finite population mass or measurable choice of existential witnesses is required.
-/

/-!
# Original-law good points on one calibrated C1,1 cover

The original countable core cover is fixed before any chart-absolutely-continuous
physical law. Restricted chart pushforwards transfer its actual potential-family
and position-comparison conclusions to almost every original physical point.
No measurability of the existential good-point predicate or finite law is needed.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
universe uE uM
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- One original calibrated C1,1 cover supplies actual good core points for every
chart-absolutely-continuous law concentrated on the original calibrated interior.
The core data are chosen before the law; the good-point predicate is derived. -/
theorem exists_countable_original_good_C11_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
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
        ∀ η : Measure M,
          (∀ old : M, (η.restrict (extChartAt 𝓘(ℝ, E) old).source).map
            (extChartAt 𝓘(ℝ, E) old) ≪ m) →
          (∀ᵐ y ∂η, y ∈ OTSelector.Geometry.calibratedInterior u) →
          ∀ᵐ y ∂η, ∃ (i : ι) (x : E), x ∈ K i ∧
            (extChartAt 𝓘(ℝ, E) (old i)).symm x = y ∧
            F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (K i) x ∧
            F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (δ i) x := by
  classical
  let : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, δ, B, A, hdata, hcover, hreach, hUA, hgood⟩ :=
    hF.exists_countable_calibrated_C11_family_cover_with_smooth_tubes hcomplete m hu
  let : Countable ι := hcount
  refine ⟨ι, hcount, old, K, G, L, δ, A, hdata, hcover, ?_, ?_⟩
  · intro i
    refine ⟨(hreach i).1, ?_, ?_⟩
    · intro x hx
      obtain ⟨l, _, r, _, hl, hul, hr, hur⟩ := (hreach i).2.2 x hx
      exact ⟨l, r, hl, hul, hr, hur⟩
    · intro x hx
      obtain ⟨hinit, hEL, _, hm⟩ := (hUA i).2.2.2 x ((hUA i).2.1 hx)
      exact ⟨hinit, hEL, hm⟩
  · intro η hηchart hηInterior
    let χ (i : ι) := extChartAt 𝓘(ℝ, E) (old i)
    let ξ (i : ι) := (η.restrict (χ i).source).map (χ i)
    let Q (i : ι) (x : E) :=
      F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (K i) x ∧
        F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (δ i) x
    have hphysical (i : ι) : ∀ᵐ y ∂η,
        y ∈ (χ i).source → χ i y ∈ K i → Q i (χ i y) := by
      have hcore : ∀ᵐ x ∂(ξ i).restrict (K i), Q i x :=
        (hgood i (ξ i) (hηchart (old i))).mono fun _ hx ↦ ⟨hx.2.1, hx.2.2.1⟩
      have hχ : AEMeasurable (χ i) (η.restrict (χ i).source) :=
        (continuousOn_extChartAt (old i)).aemeasurable
          (isOpen_extChartAt_source (old i)).measurableSet
      exact ae_imp_of_ae_restrict (ae_of_ae_map hχ (ae_imp_of_ae_restrict hcore))
    filter_upwards [ae_all_iff.mpr hphysical, hηInterior] with y hy hyInterior
    rw [← hcover] at hyInterior
    obtain ⟨i, x, hxK, hxy⟩ := mem_iUnion.mp hyInterior
    have hxT : x ∈ (χ i).target := (hdata i).2.1 hxK
    have hxQ : Q i x := by
      have h := hy i (hxy ▸ (χ i).map_target hxT)
      rw [← hxy, (χ i).right_inv hxT] at h
      exact h hxK
    exact ⟨i, x, hxK, hxy, hxQ.1, hxQ.2⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
