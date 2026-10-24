import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11LevelPositionRankCover
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.C11PotentialTube
import OTSelector.Geometry.Finsler.C11SmoothTubeCore
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11SmoothTubeCover

* **Conditions:** The original contact cover and complete ambient families with their AE rank and potential-family data.
* **Objects:** The same countable cover with exact central clock/isometry and selected smooth calibrated tubes at every good point.
* **Proof detail:** Combine original partner calibration with the retained ordinary position comparison and apply the core tube producer.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11SmoothTubeCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11SmoothTubeCover`; the selected original proof blocks follow. -/
section

/-!
# One calibrated C1,1 cover with actual smooth potential-level tubes

The same countable cover and complete ambient families retain their position rank
and potential-level comparison on one full-measure set for each source law. The
original calibrated partners give the exact central potential clock and isometry.
At each good point one selected smooth potential-level family has smooth calibrated
tubes around every compact time set strictly inside the original calibrated reach.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The original calibrated interior has one countable C1,1 family cover whose
same good points carry ambient and level position rank, the original potential
clock and central isometry, and one selected smooth potential-level family with
smooth calibrated tubes around every compact interior time set. -/
theorem exists_countable_calibrated_C11_family_cover_with_smooth_tubes
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {f : M → ℝ} (hf : let _instSmoothTubeCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) :
    let _instSmoothTubeCoverMetric : MetricSpace M := F.metricSpace
    ∃ ι : Type (max u v), Countable ι ∧
      ∃ (old : ι → M) (K U : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (δ : ι → ℝ) (B : ι → Set M) (A : ι → E → ℝ → M),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) =
          OTSelector.Geometry.calibratedInterior f ∧
        (∀ i, 0 < δ i ∧ IsCompact (B i) ∧
          ∀ x ∈ K i, ∃ a ∈ B i, ∃ b ∈ B i,
            dist a ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i ∧
            f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - f a = δ i ∧
            dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) b = δ i ∧
            f b - f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i) ∧
        (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧
          U i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ∀ x ∈ U i,
            A i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
            F.IsEulerLagrangeOn (A i x) univ ∧
            ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (A i x) ∧
            F.chartMomentumFamily (old i) (A i) (x, 0) = (x, fderiv ℝ (G i) x)) ∧
        ∀ i (ν : Measure E), ν ≪ m →
          ∀ᵐ x₀ ∂ν.restrict (K i), (x₀ ∈ K i ∧
            Tendsto (fun r ↦ m (K i ∩ closedBall x₀ r) / m (closedBall x₀ r))
              (𝓝[>] 0) (𝓝 1) ∧ DifferentiableAt ℝ (fderiv ℝ (G i)) x₀ ∧
            ∀ (terminal : M) (t : ℝ), |t| < δ i →
              A i x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
              DifferentiableAt ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A i x t)) x₀ ∧
                ∃ c : ℝ, 0 < c ∧
                  (∀ v : E, c * ‖v‖ ≤
                    ‖fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A i x t)) x₀ v‖) ∧
                  Function.Injective
                    (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (A i x t)) x₀)) ∧
            F.HasC11PotentialFamilyAt m (old i) 0 f (G i) (K i) x₀ ∧
            F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (δ i) x₀ ∧
            (∀ t ∈ Icc (-(δ i)) (δ i),
              f (A i x₀ t) = f ((extChartAt 𝓘(ℝ, E) (old i)).symm x₀) + t) ∧
            Isometry (fun t : Icc (-(δ i)) (δ i) ↦ A i x₀ t) ∧
            F.HasC11SmoothTubeFamilyAt (old i) f (G i) (A i) (δ i) x₀ := by
  let _instSmoothTubeCoverMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, δ, B, A, hdata, hcover, hreach, hUA, hgood⟩ :=
    hF.exists_countable_calibrated_C11_family_cover_with_level_position_rank hcomplete m hf
  refine ⟨ι, hcount, old, K, U, G, L, δ, B, A, hdata, hcover, hreach, hUA, ?_⟩
  intro i ν hν
  filter_upwards [hgood i ν hν] with x₀ hx
  obtain ⟨hrank, hpotential, hcmp⟩ := hx
  obtain ⟨hU, hKU, hUt, hfamily⟩ := hUA i
  obtain ⟨a, _, b, _, ha, hfa, hb, hfb⟩ := (hreach i).2.2 x₀ hrank.1
  have hA := hfamily x₀ (hKU hrank.1)
  obtain ⟨hclock, hiso, htube⟩ :=
    hF.smoothTubeFamily_of_calibrated_initial_data hcomplete (old i) hf
      (hUt (hKU hrank.1)) hA.2.1 hA.1 hA.2.2.2 (hreach i).1
      ⟨ha, hfa⟩ ⟨hb, hfb⟩ hpotential hcmp
  exact ⟨hrank, hpotential, hcmp, hclock, hiso, htube⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
