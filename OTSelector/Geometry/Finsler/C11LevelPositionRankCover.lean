import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11PositionRankCover
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11LevelPositionRankCover

* **Conditions:** The original countable contact cores, extensions, complete ambient families and actual calibrated reach data.
* **Objects:** One exact cover with both ambient all-time rank and ordinary potential-level position comparison.
* **Proof detail:** Intersect the already proved AE ambient rank and actual potential-family events on each unchanged core.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11LevelPositionRankCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11LevelPositionRankCover`; the selected original proof blocks follow. -/
section

/-!
# One calibrated C1,1 cover with ambient and potential-level position rank

Retain the same countable compact cores, C1,1 extensions, positive calibrated reach,
compact partner carriers and actual complete ambient families. On each core, one
full-measure set carries the ordinary ambient position lower bound and constructed
smooth potential-level data. Every complete family with the normalized initial phase
jet has the actual ambient derivative restricted to the covector kernel and inherits
its lower bound. No additional cover or rank premise is supplied.
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

/-- One exact countable cover of the original calibrated interior carries both actual
ambient position rank and smooth potential-level data with ordinary position comparison.
The same ambient families and cores are retained. A single full-measure set in each core
works for all matching complete level families, legal output charts and calibrated times. -/
theorem exists_countable_calibrated_C11_family_cover_with_level_position_rank
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {f : M → ℝ} (hf : let _instLevelRankCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) :
    let _instLevelRankCoverMetric : MetricSpace M := F.metricSpace
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
            F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (δ i) x₀ := by
  let _instLevelRankCoverMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, δ, B, A, hdata, hcover, hreach, hUA, hrank⟩ :=
    hF.exists_countable_calibrated_C11_family_cover_with_alltime_position_rank hcomplete m hf
  refine ⟨ι, hcount, old, K, U, G, L, δ, B, A, hdata, hcover, hreach, hUA, ?_⟩
  intro i ν hν
  obtain ⟨hK, _, hG, _, hLip, hval, _, hactual⟩ := hdata i
  obtain ⟨hU, hKU, hUt, hfamily⟩ := hUA i
  have hEL := fun x hx ↦ (hfamily x hx).2.1
  have hinit := fun x hx ↦ (hfamily x hx).1
  have hp := fun x hx ↦ (hfamily x hx).2.2.2
  have hpartners : ∀ x ∈ K i, ∃ a b : M,
      dist a ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i ∧
      f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - f a = δ i ∧
      dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) b = δ i ∧
      f b - f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i := by
    intro x hx
    obtain ⟨a, _, b, _, ha, hfa, hb, hfb⟩ := (hreach i).2.2 x hx
    exact ⟨a, b, ha, hfa, hb, hfb⟩
  have hinterior : MapsTo (extChartAt 𝓘(ℝ, E) (old i)).symm (K i)
      (OTSelector.Geometry.calibratedInterior f) := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  exact (hrank i ν hν).and
    (hF.ae_levelPositionComparison_of_calibrated_C11_core hcomplete (old i)
      hν hK hU hKU hUt hf hinterior hG hLip hval hactual hEL hinit hp
      (hreach i).1 hpartners)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
