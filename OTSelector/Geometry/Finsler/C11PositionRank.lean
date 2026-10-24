import OTSelector.Analysis.Calculus.DensityOneLowerDerivative
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11ReadoutDerivative
import OTSelector.Geometry.Finsler.CalibratedLowerBound
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricPotentialEikonal

/-!
# Geometry.Finsler.C11PositionRank

* **Conditions:** A density-one point of the actual calibrated core where the C1,1 extension covector is differentiable; a coordinate-AC law for the AE theorem.
* **Objects:** Positive lower derivative bounds and injective actual translated position derivatives, simultaneously at all legal charts/times within reach.
* **Proof detail:** Combine the constructed centered lower bound with genuine ambient differentiability, pass from density-one core directions to all directions and use density/Rademacher once.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11PositionRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11PositionRank`; the selected original proof blocks follow. -/
section

/-!
# Actual position-derivative rank on calibrated C1,1 cores

At a density-one point of an original calibrated core where its extension covector
is differentiable, every legal translated position has an actual ambient derivative
with a positive lower norm bound. Density and Rademacher select one full-measure set
of source points supporting all target charts and all times within the common reach.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The actual position derivative of a calibrated C1,1 family is bounded below and
injective at every ambient density-one point where the initial covector is differentiable. -/
theorem exists_pos_fderiv_lower_bound_of_calibrated_C11_translation
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial terminal : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {u : M → ℝ} (hu : let _instPositionRankLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) initial).symm)) K)
    {Γ : E → ℝ → M} (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instPositionRankPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) initial).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) initial).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ)
    {x₀ : E} (hx₀ : x₀ ∈ K)
    (hdensity : Tendsto (fun r ↦ m (K ∩ closedBall x₀ r) / m (closedBall x₀ r))
      (𝓝[>] 0) (𝓝 1)) (hD : DifferentiableAt ℝ (fderiv ℝ G) x₀)
    {t : ℝ} (ht : |t| < δ)
    (hlegal : Γ x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    DifferentiableAt ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)) x₀ ∧
      ∃ c : ℝ, 0 < c ∧
        (∀ v : E, c * ‖v‖ ≤
          ‖fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)) x₀ v‖) ∧
        Function.Injective
          (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)) x₀) := by
  have hread := hF.differentiableAt_chart_readout_of_initial_covector hcomplete initial
    hU hUt hEL hinit hp (hKU hx₀) hD terminal t hlegal
  obtain ⟨c, hc, hlower⟩ :=
    hF.exists_centered_lower_bound_of_calibrated_C11_translation hcomplete initial terminal
      hK hU hKU hUt hu hG hLip hmatch hEL hinit hp hδ hpartners hx₀ ht hlegal
  have hbound := hlower.mono fun _ hx ↦ hx.2
  exact ⟨hread, c, hc,
    norm_apply_ge_of_density_one m hdensity hread.hasFDerivAt.hasFDerivWithinAt hc.le hbound,
    injective_of_density_one_lower_bound m hdensity
      hread.hasFDerivAt.hasFDerivWithinAt hc hbound⟩

/-- One full-measure subset of the original calibrated core supports the actual
injective position derivative for every target chart and every time within the reach.
The exceptional source set is chosen by ambient density and covector differentiability
before the target chart and time are quantified. -/
theorem ae_alltime_position_rank_of_calibrated_C11_translation
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {u : M → ℝ} (hu : let _instAEPositionRankLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) initial).symm)) K)
    {Γ : E → ℝ → M} (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instAEPositionRankPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) initial).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) initial).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ) :
    ∀ᵐ x₀ ∂ν.restrict K, x₀ ∈ K ∧
      Tendsto (fun r ↦ m (K ∩ closedBall x₀ r) / m (closedBall x₀ r))
        (𝓝[>] 0) (𝓝 1) ∧ DifferentiableAt ℝ (fderiv ℝ G) x₀ ∧
      ∀ (terminal : M) (t : ℝ), |t| < δ →
        Γ x₀ t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
        DifferentiableAt ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)) x₀ ∧
          ∃ c : ℝ, 0 < c ∧
            (∀ v : E, c * ‖v‖ ≤
              ‖fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)) x₀ v‖) ∧
            Function.Injective
              (fderiv ℝ (fun x ↦ extChartAt 𝓘(ℝ, E) terminal (Γ x t)) x₀) := by
  have hdG : ∀ᵐ x ∂ν.restrict K, DifferentiableAt ℝ (fderiv ℝ G) x :=
    ae_restrict_of_ae (hν.ae_le hLip.ae_differentiableAt)
  filter_upwards [ae_density_one_of_absolutelyContinuous hν K, hdG,
    ae_restrict_mem hK.measurableSet] with x₀ hdensity hD hx₀
  refine ⟨hx₀, hdensity, hD, fun terminal t ht hlegal ↦ ?_⟩
  exact hF.exists_pos_fderiv_lower_bound_of_calibrated_C11_translation hcomplete
    initial terminal m hK hU hKU hUt hu hG hLip hmatch hEL hinit hp hδ hpartners
    hx₀ hdensity hD ht hlegal

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
