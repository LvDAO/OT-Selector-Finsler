import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.C11PositionRank
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11PositionRankCover

* **Conditions:** The same countable compact calibrated cores and actual complete ambient families.
* **Objects:** One full-measure set on each core with actual ambient position derivative lower bounds at every legal translated time.
* **Proof detail:** Retain the existing cover and apply the all-time rank theorem separately to each original coordinate law.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11PositionRankCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11PositionRankCover`; the selected original proof blocks follow. -/
section

/-!
# Countable calibrated C1,1 cover with actual position-derivative rank

The existing countable compact calibrated cover and its complete geodesic families
are retained exactly. On every core, each measure absolutely continuous with respect
to ambient Haar measure has one full-measure set of density-one points where the
extension covector is differentiable and every legal position readout within the
calibrated reach has an actual ambient derivative bounded below by a positive constant.
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

/-- The full calibrated interior has an exact countable compact C1,1 family cover
whose source cores support actual ambient position derivatives bounded below and
injective at almost every point for every absolutely continuous source measure.
Each core uses one full-measure source set simultaneously for every target chart and
every legal time strictly inside its positive two-sided calibrated reach. -/
theorem exists_countable_calibrated_C11_family_cover_with_alltime_position_rank
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {f : M → ℝ} (hf : let _instRankCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) :
    let _instRankCoverMetric : MetricSpace M := F.metricSpace
    ∃ ι : Type (max u v), Countable ι ∧
      ∃ (old : ι → M) (K U : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (δ : ι → ℝ) (B : ι → Set M) (Γ : ι → E → ℝ → M),
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
            Γ i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
            F.IsEulerLagrangeOn (Γ i x) univ ∧
            ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Γ i x) ∧
            F.chartMomentumFamily (old i) (Γ i) (x, 0) = (x, fderiv ℝ (G i) x)) ∧
        ∀ i (ν : Measure E), ν ≪ m →
          ∀ᵐ x₀ ∂ν.restrict (K i), x₀ ∈ K i ∧
            Tendsto (fun r ↦ m (K i ∩ closedBall x₀ r) / m (closedBall x₀ r))
              (𝓝[>] 0) (𝓝 1) ∧ DifferentiableAt ℝ (fderiv ℝ (G i)) x₀ ∧
            ∀ (terminal : M) (t : ℝ), |t| < δ i →
              Γ i x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
              DifferentiableAt ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ i x t)) x₀ ∧
                ∃ c : ℝ, 0 < c ∧
                  (∀ v : E, c * ‖v‖ ≤
                    ‖fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ i x t)) x₀ v‖) ∧
                  Function.Injective
                    (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ i x t)) x₀) := by
  let _instRankCoverMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, δ, B, Γ, hdata, hcover, hreach, hUΓ⟩ :=
    hF.exists_countable_calibrated_C11_family_cover hcomplete hf
  refine ⟨ι, hcount, old, K, U, G, L, δ, B, Γ, hdata, hcover, hreach, hUΓ, ?_⟩
  intro i ν hν
  obtain ⟨hK, _, hG, _, hLip, _, hmatch, _⟩ := hdata i
  obtain ⟨hU, hKU, hUt, hfamily⟩ := hUΓ i
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
  exact hF.ae_alltime_position_rank_of_calibrated_C11_translation hcomplete (old i)
    hν hK hU hKU hUt hf hG hLip hmatch hEL hinit hp (hreach i).1 hpartners

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
