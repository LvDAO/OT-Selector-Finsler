import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11JetPropagation
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.CalibratedC11ReachCover
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11SecondJetCover

* **Conditions:** The original countable compact calibrated contact cover with fixed extensions, reach and partner carriers.
* **Objects:** One exact cover retaining actual Hessians, within-core potential-covector derivatives and complete second-jet family data for every coordinate-AC law.
* **Proof detail:** Apply the core AE jet and propagation statements on each retained core, keeping parameter-space quantification inside the good-point conclusion.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): Potential-level and phase-indexed propagation families remain separate existential constructions until the explicit matching theorem.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11SecondJetCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11SecondJetCover`; the selected original proof blocks follow. -/
section

/-!
# Actual second jets and complete families on the same calibrated contact cover

The countable compact contact cover is constructed once from the original complete
Finsler geometry and one-Lipschitz potential. Its exact values, derivatives, positive
calibrated reach and compact partner carriers are retained. Every coordinate core
then carries the actual extension Hessian, the within-core derivative of the original
potential covector, and complete potential-level family data almost everywhere for
every law absolutely continuous with respect to coordinate Haar. On the same good
points, rough and normalized smooth seed jets propagate within one complete family
for every parameter space. This family and the potential-level family remain separate
existential constructions. No additional cover, density oracle or flow input is used.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
universe u v w
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The same exact contact cover carries actual second jets, complete potential-level
families and propagation of rough and smooth normalized seed jets in one complete flow. The normed
parameter spaces are quantified inside the almost-everywhere conclusion. -/
theorem exists_countable_calibrated_C11_secondJet_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {f : M → ℝ} (hf : let _instSecondJetCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) :
    let _instSecondJetCoverStatementMetric : MetricSpace M := F.metricSpace
    ∃ ι : Type (max u v), Countable ι ∧
      ∃ (old : ι → M) (K : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (δ : ι → ℝ) (B : ι → Set M),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) =
          calibratedInterior f ∧
        (∀ i, 0 < δ i ∧ IsCompact (B i) ∧
          ∀ x ∈ K i, ∃ a ∈ B i, ∃ b ∈ B i,
            dist a ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i ∧
            f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - f a = δ i ∧
            dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) b = δ i ∧
            f b - f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i) ∧
        ∀ i (t₀ : ℝ) (ν : Measure E), ν ≪ m →
          ∀ᵐ x ∂ν.restrict (K i),
            F.HasC11PotentialFamilyAt m (old i) t₀ f (G i) (K i) x ∧
            ∀ (V : Type w) (_instSecondJetCoverNorm : NormedAddCommGroup V)
              (_instSecondJetCoverSpace : NormedSpace ℝ V),
              F.HasC11PropagatedJetAt (V := V) m (old i) t₀ f (G i) (K i) x := by
  let _instSecondJetCoverProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, G, L, δ, B, hdata, hcover, hreach⟩ :=
    hF.exists_countable_trimmed_calibrated_C11_cover hcomplete hf
  refine ⟨ι, hcount, old, K, G, L, δ, B, hdata, hcover, hreach, ?_⟩
  intro i t₀ ν hν
  obtain ⟨hKi, hKti, hGi, _, hLipi, hvali, _, hactuali⟩ := hdata i
  have hinside : MapsTo (extChartAt 𝓘(ℝ, E) (old i)).symm (K i)
      (calibratedInterior f) := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  exact (hF.ae_complete_potentialFamily_of_calibrated_C11_core hcomplete (old i) t₀
    hν hKi hKti hf hinside hGi hLipi hvali hactuali).and
    (hF.ae_complete_jetPropagation_of_calibrated_C11_core hcomplete (old i) t₀
      hν hKi hKti hf hinside hGi hLipi hvali hactuali)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
