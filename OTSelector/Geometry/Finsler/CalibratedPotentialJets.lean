import OTSelector.Analysis.Calculus.MetricPotentialContact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricPotentialEikonal

/-!
# Geometry.Finsler.CalibratedPotentialJets

* **Conditions:** Two-sided actual calibrated contact data on a compact coordinate core, with an absolutely continuous original law.
* **Objects:** True potential differentials, a C1,1 extension and almost-everywhere normalized second jets with small-loss compact continuity cores.
* **Proof detail:** Construct touching distance supports, derive the actual first covector and contact extension, then use density, Rademacher and normalized eikonal jet construction.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedPotentialJets.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedPotentialJets`; the selected original proof blocks follow. -/
section

/-!
# Normalized jets of the original Finsler potential from calibrated contacts

In a genuine original chart, two-sided calibrated endpoint-distance data constructs
both the actual first differential of the original potential and its C1,1 extension.
A nontrivial calibrated partner then constructs the unit-energy Legendre covector.
The resulting normalized second jets and small-loss compact cores therefore require
neither a differentiability premise nor a unit-covector premise.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Original compact calibrated contacts and their actual endpoint-distance Hessians
construct the C1,1 extension, almost-everywhere normalized second jets, and arbitrarily
small-loss compact cores in a legal original chart. Actual differentiability and unit
energy of the original covector are conclusions derived inside the proof. -/
theorem exists_calibrated_potential_eikonal_cores (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {μ ν : Measure E} [IsAddHaarMeasure μ] (hν : ν ≪ μ) :
    let _instCalibratedPotentialJetsStatementMetric : MetricSpace M := F.metricSpace
    let Y : E → M := (extChartAt 𝓘(ℝ, E) old).symm
    ∀ {φ : M → ℝ} (_hφ : LipschitzWith 1 φ)
      {K : Set E} (_hK : IsCompact K) (_hνK : ν K ≠ ⊤)
      {c : E} {R : ℝ} (_hR : 0 < R) (_hKball : K ⊆ closedBall c R)
      (_hKchart : K ⊆ (extChartAt 𝓘(ℝ, E) old).target) (a b : E → M)
      {A B : Set M} (_hA : IsCompact A) (_hB : IsCompact B)
      (_haA : MapsTo a K A) (_hbB : MapsTo b K B)
      (_ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
      (_hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
      (_hneq : ∀ x ∈ K, Y x ≠ b x)
      (_hleft : ∀ a ∈ A, ∀ z ∈ closedBall c (3 * R),
        ContDiffAt ℝ 2 (fun y ↦ dist a (Y y)) z)
      (_hright : ∀ b ∈ B, ∀ z ∈ closedBall c (3 * R),
        ContDiffAt ℝ 2 (fun y ↦ dist (Y y) b) z)
      (_hcontLeft : ContinuousOn
        (fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist q.1 (Y y))) q.2)
        (A ×ˢ closedBall c (3 * R)))
      (_hcontRight : ContinuousOn
        (fun q : M × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist (Y y) q.1)) q.2)
        (B ×ˢ closedBall c (3 * R))),
      ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        ContDiffOn ℝ ∞ G Kᶜ ∧ LipschitzWith L (fderiv ℝ G) ∧
        EqOn G (φ ∘ Y) K ∧ EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) K ∧
        (∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x) ∧
        let J : E → Prop := fun x ↦
          Tendsto (fun r ↦ μ (K ∩ closedBall x r) / μ (closedBall x r))
            (𝓝[>] 0) (𝓝 1) ∧
          HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
          HasFDerivWithinAt (fderiv ℝ (φ ∘ Y)) (fderiv ℝ (fderiv ℝ G) x) K x ∧
          HasNormalizedPotentialJet (F := F) old (φ ∘ Y) G x
        (∀ᵐ x ∂ν.restrict K, J x) ∧
          ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ K' ⊆ K, IsCompact K' ∧ ν (K \ K') < ε ∧
            ContinuousOn (fderiv ℝ (fderiv ℝ G)) K' ∧ ∀ x ∈ K', J x := by
  let _instCalibratedPotentialJetsProofMetric : MetricSpace M := F.metricSpace
  let Y : E → M := (extChartAt 𝓘(ℝ, E) old).symm
  dsimp only
  intro φ hφ K hK hνK c R hR hKball hKchart a b A B hA hB haA hbB ha hb hneq
    hleft hright hcontLeft hcontRight
  obtain ⟨_, hactual, _, _⟩ := metric_potential_contactJet_of_compact_distance_hessians
    hφ Y hR hKball a b hA hB haA hbB ha hb hleft hright hcontLeft hcontRight
  have hd : ∀ z ∈ K, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ (Y z) := by
    intro z hz
    have hx : Y z ∈ (chartAt E old).source := by
      simpa only [extChartAt_source] using
        (extChartAt 𝓘(ℝ, E) old).map_target (hKchart hz)
    apply (mdifferentiableAt_iff_source_of_mem_source
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) hx).2
    simpa only [Y, (extChartAt 𝓘(ℝ, E) old).right_inv (hKchart hz),
      modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      (hactual z hz).1.differentiableAt.mdifferentiableAt
  have hunit := hF.chart_unit_legendre_on_of_calibrated_endpoints hcomplete old
    hKchart hφ hd (fun z hz ↦ ⟨b z, hneq z hz, hb z hz⟩)
  exact hF.exists_metric_potential_eikonal_cores old hν hφ Y hK hνK hR hKball a b
    hA hB haA hbB ha hb hleft hright hcontLeft hcontRight hunit

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
