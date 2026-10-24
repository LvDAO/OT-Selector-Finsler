import OTSelector.Reconstruction.EndpointGraphMomentWindow
import OTSelector.Reconstruction.PopulationComparisonClockIdentity
import OTSelector.Reconstruction.FinslerPopulationSeedDensity
import OTSelector.Geometry.FinslerSeedEndpointCharts

/-!
# The original seed density in its selected endpoint frame

The actual seed and comparison have the same central curve and phase derivative.
Their original physical Jacobian consequently factors in the endpoint's selected
Jacobi frame. A positive original Jacobian supplies interior regularity there.
-/

open Set Matrix Module Manifold MeasureTheory Metric
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart

open OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
  {C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q} {endpoint : ℝ}

/-- The original countable manifold-chart center retained at this endpoint. -/
def old (G : SeedEndpointChart S C endpoint) : M :=
  S.curve G.center.val.2 G.center.val.1

/-- The comparison's actual adapted position in the selected endpoint chart. -/
def graphReadout (G : SeedEndpointChart S C endpoint) (q : S.covector.ker × ℝ) :=
  G.A (extChartAt 𝓘(ℝ, E) G.old (C.curve q.1 q.2))

/-- The same physical time read by the endpoint's positive graph clock. -/
def clock (G : SeedEndpointChart S C endpoint) (t : ℝ) : ℝ :=
  (G.graphReadout (w, t)).1

/-- The actual derivative of the endpoint clock with respect to original time. -/
def speed (G : SeedEndpointChart S C endpoint) (t : ℝ) : ℝ :=
  (fderiv ℝ G.graphReadout (w, t) (0, 1)).1

/-- The position derivative of the same endpoint phase in the fixed label indexing. -/
def jacobiPositionMatrix (G : SeedEndpointChart S C endpoint)
    (bW : Basis ι ℝ S.covector.ker) (s : ℝ) : Matrix ι ι ℝ :=
  vectorFamilyMatrix (G.spatialBasis bW) (fun j ↦
    (fderiv ℝ (fun z ↦ F.adaptedGraphPhase G.old G.A G.graphReadout G.geometry.e (z, s))
      w (bW j)).1)

/-- The fixed physical parameter-volume factor of the selected endpoint frame. -/
def parameterNormalization (G : SeedEndpointChart S C endpoint)
    (bW : Basis ι ℝ S.covector.ker) : ℝ :=
  |(LinearMap.toMatrix (timeLabelBasis (G.spatialBasis bW)) (timeLabelBasis bW)
    (S.normalization.trans G.A).symm.toLinearEquiv.toLinearMap).det|

omit [BorelSpace E] in
/-- The original Jacobian has the exact selected endpoint factorization, retaining
the actual speed, phase matrix, and fixed original volume normalization. -/
theorem parameterizedJacobian_eq (G : SeedEndpointChart S C endpoint)
    (bW : Basis ι ℝ S.covector.ker) (hcurve : S.curve w = C.curve w)
    {t : ℝ} (ht : (w, t) ∈ G.geometry.U)
    {D : (S.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily G.old S.curve) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily G.old C.curve) D (w, t)) :
    parameterizedJacobian (populationSeedChartReadout S G.center) S.normalization (t, w) =
      |G.speed t| * |(G.jacobiPositionMatrix bW (G.clock t)).det| *
        G.parameterNormalization bW := by
  let P := S.rationalWindow ((⟨-1, by norm_num⟩, ⟨1, by norm_num⟩), G.center)
  have hdata := (P.parameterizedJacobian_comparisonGraphPhase_data bW (G.spatialBasis bW)
    G.A hcurve h₁ h₂ G.geometry.raw.1 (G.geometry.source_U ht)
    (G.geometry.regular _ ht).1.ne'
    (G.geometry.phase_label_differentiable (G.geometry.clock_mem_phase ht))).2
  have hs := populationWindowGraphClock_eq_comparison P G.A hcurve t
  have hv := populationWindowGraphSpeed_eq_comparison P G.A h₁ h₂
  change populationWindowGraphClock P G.A w t = G.clock t at hs
  change populationWindowGraphSpeed P G.A w t = G.speed t at hv
  change parameterizedJacobian (populationSeedChartReadout S G.center)
    S.normalization (t, w) = |populationWindowGraphSpeed P G.A w t| *
      |(G.jacobiPositionMatrix bW (populationWindowGraphClock P G.A w t)).det| *
        G.parameterNormalization bW at hdata
  rwa [hs, hv] at hdata

omit [BorelSpace E] in
/-- Original positive volume density forces the same endpoint phase-position matrix
to be nonsingular at the corresponding interior time. -/
theorem jacobiPositionMatrix_det_ne_zero (G : SeedEndpointChart S C endpoint)
    (bW : Basis ι ℝ S.covector.ker) (hcurve : S.curve w = C.curve w)
    {t : ℝ} (ht : (w, t) ∈ G.geometry.U)
    {D : (S.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily G.old S.curve) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily G.old C.curve) D (w, t))
    (hpos : 0 < parameterizedJacobian (populationSeedChartReadout S G.center)
      S.normalization (t, w)) :
    (G.jacobiPositionMatrix bW (G.clock t)).det ≠ 0 := by
  have heq := G.parameterizedJacobian_eq bW hcurve ht h₁ h₂
  intro hz
  rw [hz, abs_zero, mul_zero, zero_mul] at heq
  exact hpos.ne' heq

omit [BorelSpace E] in
/-- The full original seed density has the same actual endpoint determinant factor. -/
theorem physicalDensity_eq (G : SeedEndpointChart S C endpoint)
    (bW : Basis ι ℝ S.covector.ker) (ρ : M → ℝ) (v : M → E → ℝ)
    (hcurve : S.curve w = C.curve w) {t : ℝ} (ht : (w, t) ∈ G.geometry.U)
    {D : (S.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily G.old S.curve) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily G.old C.curve) D (w, t)) :
    populationSeedChartDensity S ρ v G.center w t =
      (ρ (S.curve w t) * v G.old (populationSeedChartReadout S G.center (t, w))) *
        (|G.speed t| * |(G.jacobiPositionMatrix bW (G.clock t)).det| *
          G.parameterNormalization bW) := by
  change parameterizedJacobian _ _ _ * _ = _
  rw [G.parameterizedJacobian_eq bW hcurve ht h₁ h₂]
  exact mul_comm _ _

end OTSelector.Geometry.ContinuousFinslerNorm.SeedEndpointChart
