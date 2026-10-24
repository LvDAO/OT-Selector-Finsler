import OTSelector.Reconstruction.FinslerPopulationSeedDensity
import OTSelector.Reconstruction.FinslerPopulationJacobiDensity

/-!
# Whole active-chart conditional density in the actual comparison frame

The original two-color atlas supplies the whole active seed-chart law. Matching
actual phase jets now identify its Jacobian with the same comparison position
matrix on an arbitrary endpoint neighborhood, without rational endpoint screens.
-/

open Set MeasureTheory ProbabilityTheory Manifold Metric Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M V ι Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [T2Space M] [PreconnectedSpace M] in
/-- Whole active-chart density in the actual comparison Jacobi frame. The window
record only selects the seed and chart; its screened rational endpoints impose
no restriction on the measurable interval `K` in this conclusion. -/
theorem PopulationSeedChartDensityLaw.restrict_eq_comparisonGraphPhase
    (P : F.CalibratedSeedWindow u) {a : M → Z}
    {κ : Measure P.seed.covector.ker} {lambda : Measure Z}
    {η : Measure M} [IsFiniteMeasure η] {ρ : M → ℝ} {v : M → E → ℝ} {u₀ : ℝ}
    (hlaw : PopulationSeedChartDensityLaw P.seed a κ lambda η ρ v u₀) :
    ∀ᵐ z ∂lambda, (populationSeedLabelReference P.seed a κ).rnDeriv lambda z < (∞ : ℝ≥0∞) ∧
      ∀ w ∈ P.seed.labels, a (P.seed.curve w 0) = z →
        w ∈ ball P.center.2 (P.seed.radius P.center) →
        ∀ (K : Set ℝ), MeasurableSet K →
          (∀ q ∈ K, q + u₀ - P.seed.level ∈
            interior (P.seed.calibrationTimes w) ∩ ball P.center.1 (P.seed.radius P.center)) →
          ∀ (bW : Basis ι ℝ P.seed.covector.ker) (bV : Basis ι ℝ V)
            (A : E ≃L[ℝ] (ℝ × V)) (Γ : P.seed.covector.ker → ℝ → M),
            P.seed.curve w = Γ w →
            ∀ (e : OpenPartialHomeomorph (P.seed.covector.ker × ℝ) (P.seed.covector.ker × ℝ)),
              (e : P.seed.covector.ker × ℝ → P.seed.covector.ker × ℝ) =
                curveGraphCoordinateMap (A ∘ P.comparisonReadout Γ) →
              (∀ q ∈ K, ∃ D : (P.seed.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ),
                HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) P.seed.curve)
                  D (w, q + u₀ - P.seed.level) ∧
                HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) Γ)
                  D (w, q + u₀ - P.seed.level)) →
              (∀ q ∈ K, (w, q + u₀ - P.seed.level) ∈ e.source) →
              (∀ q ∈ K, (fderiv ℝ (A ∘ P.comparisonReadout Γ)
                (w, q + u₀ - P.seed.level) (0, 1)).1 ≠ 0) →
              (∀ q ∈ K, DifferentiableAt ℝ
                (fun y ↦ F.adaptedGraphPhase (P.toManifold P.center) A
                  (A ∘ P.comparisonReadout Γ) e
                    (y, (A (P.comparisonReadout Γ (w, q + u₀ - P.seed.level))).1)) w) →
              ((condDistrib u a η z).map (fun s : ℝ ↦ s - u₀)).restrict K =
                (volume.restrict K).withDensity (fun q ↦
                  let t := q + u₀ - P.seed.level
                  ENNReal.ofReal
                    ((ρ (P.seed.curve w t) *
                        (((populationSeedLabelReference P.seed a κ).rnDeriv lambda z).toReal *
                          v (P.toManifold P.center) (P.readout (t, w)))) *
                      (|populationWindowGraphSpeed P A w t| *
                        |(populationWindowGraphPositionMatrix P bW bV A Γ e w
                          (populationWindowGraphClock P A w t)).det| *
                        populationWindowGraphNormalization P bW bV A))) := by
  filter_upwards [hlaw.restrict] with z hz
  refine ⟨hz.1, ?_⟩
  intro w hw hwz hwball K hK hKU bW bV A Γ hcurve e he hjets hsource hspeed hphase
  rw [hz.2 ⟨P.center, P.center_mem⟩ w hw hwz hwball K hK hKU]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hK] with q hq
  obtain ⟨D, h₁, h₂⟩ := hjets q hq
  have hphysical := populationWindowPhysicalDensity_eq_comparisonGraphPhase
    (fun _ ↦ P) ρ (fun _ ↦ v (P.toManifold P.center)) 0 bW bV A
      hcurve h₁ h₂ he (hsource q hq) (hspeed q hq) (hphase q hq)
  change populationSeedChartDensity P.seed ρ v ⟨P.center, P.center_mem⟩ w
    (q + u₀ - P.seed.level) = _ at hphysical
  dsimp only
  rw [hphysical]
  congr 1
  ring

end OTSelector.Reconstruction
