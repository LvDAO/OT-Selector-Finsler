import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11JetPropagation
import OTSelector.Geometry.Finsler.C11MatchedFamily
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.C11SecondJetCover
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11MatchedCover

* **Conditions:** The original countable second-jet contact cover.
* **Objects:** The same cover retaining potential-level witnesses, all-parameter propagation and actual matched smooth/rough families.
* **Proof detail:** Apply the matching construction to each existing good-point family without changing cores, original potential or calibrated reaches.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11MatchedCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11MatchedCover`; the selected original proof blocks follow. -/
section

/-!
# Matched smooth and rough families on the original calibrated contact cover

The existing countable second-jet cover is used once. All coordinates, compact cores,
C1,1 extensions, exact matching, positive reach and compact partner carriers are retained.
For every absolutely continuous coordinate law, its same good points retain both the
potential-level family and all-parameter-space jet propagation. They also carry a
matched family whose central curve agrees and whose rough within-core momentum
variation is the derivative of the smooth potential-level family.
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

/-- The original contact cover carries the existing family and propagation conclusions,
together with matched smooth and rough families at the same almost-everywhere points. -/
theorem exists_countable_calibrated_C11_matched_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {f : M → ℝ} (hf : let _instMatchedCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) :
    let _instMatchedCoverStatementMetric : MetricSpace M := F.metricSpace
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
            (∀ (V : Type w) (_instMatchedCoverNorm : NormedAddCommGroup V)
              (_instMatchedCoverSpace : NormedSpace ℝ V),
              F.HasC11PropagatedJetAt (V := V) m (old i) t₀ f (G i) (K i) x) ∧
            F.HasC11MatchedFamilyAt (old i) t₀ f (G i) (K i) x := by
  let _instMatchedCoverProofMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, G, L, δ, B, hdata, hcover, hreach, hgood⟩ :=
    hF.exists_countable_calibrated_C11_secondJet_cover hcomplete m hf
  refine ⟨ι, hcount, old, K, G, L, δ, B, hdata, hcover, hreach, ?_⟩
  intro i t₀ ν hν
  filter_upwards [hgood i t₀ ν hν] with x hx
  exact ⟨hx.1, hx.2, hF.matchedFamily_of_C11PotentialFamily hcomplete hx.1⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
