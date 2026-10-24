import OTSelector.Reconstruction.SeedEndpointMomentWindow
import OTSelector.Reconstruction.FinslerPopulationDensityBounds
import OTSelector.Reconstruction.OriginalConditionalMomentTransfer
import OTSelector.Geometry.FinslerIntrinsicKernelOriginal

/-!
# Full original conditional moments from actual seed geometry

A single actual comparison and its original physical density suffice on a finite
calibrated support span. Both endpoint charts are constructed from the original
countable cover. Their true density bounds and clocks give endpoint cancellation,
and the same intrinsic kernel controls the compact middle and the global primitive.
-/

open Set Matrix Module Manifold MeasureTheory Metric
open scoped Topology ContDiff Matrix.Norms.Operator MatrixOrder ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {initial : M} {t₀ : ℝ} {w : S.covector.ker} {z₀ : E × (E →L[ℝ] ℝ)}
  {R : S.covector.ker →L[ℝ] E} {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}

omit [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- The actual original conditional law has both required full-span moments. The
endpoint charts, determinant regularity, kernel regularity and density bounds are
all produced from original seed data and physical density/volume regularity. -/
theorem seed_comparison_compliance_moments
    (C : F.SmoothPhaseJetComparison initial t₀ w z₀ R Q)
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ S.covector.ker)
    (hw : w ∈ S.labels) (hcurve : S.curve w = C.curve w)
    (hjet : ∀ old t, S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      HasFDerivAt (F.chartMomentumFamily old S.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t) ∧
      HasFDerivAt (F.chartMomentumFamily old C.curve)
        (fderiv ℝ (F.chartMomentumFamily old C.curve) (w, t)) (w, t))
    (hpos : ∀ old t, t ∈ interior (S.calibrationTimes w) →
      S.curve w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      0 < parameterizedJacobian
        (fun q : ℝ × S.covector.ker ↦ extChartAt 𝓘(ℝ, E) old (S.curve q.2 q.1))
        S.normalization (t, w))
    {lo hi root : ℝ} (hlt : lo < hi) (hcal : Icc lo hi ⊆ S.calibrationTimes w)
    (hroot : root ∈ Ioo lo hi)
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ.map (fun x : ℝ ↦ x - S.level), t ∈ Ioo lo hi)
    {ρ : M → ℝ} {v : M → E → ℝ} (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ x ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old x)
    (c : ℝ≥0∞)
    (hdensity : ∀ center : S.centers, w ∈ ball center.val.2 (S.radius center) →
      ∀ K : Set ℝ, MeasurableSet K →
        (∀ t ∈ K, t ∈ interior (S.calibrationTimes w) ∩
          ball center.val.1 (S.radius center)) →
        (μ.map (fun x : ℝ ↦ x - S.level)).restrict K =
          (volume.restrict K).withDensity (fun t ↦ ENNReal.ofReal
            (c.toReal * populationSeedChartDensity S ρ v center w t))) :
    Integrable (fun x ↦ (1 + CFC.abs
      (∫ t in root..(x - S.level), C.intrinsicKernel bW t)).det) μ ∧
      ∀ r : ℝ, 0 < r → r < 2 →
        Integrable (fun x ↦ ‖∫ t in root..(x - S.level), C.intrinsicKernel bW t‖ ^ r) μ := by
  have hactive : Ioo lo hi ⊆ interior (S.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono hcal
  obtain ⟨hK, hKpos⟩ := C.continuousOn_posDef_intrinsicKernel_of_original hF bW
    S.normalization hcurve (fun old t _ hx ↦ hjet old t hx)
    (fun old t ht hx ↦ hpos old t (hactive ht) hx)
  obtain ⟨L, H, l, h, hlo, hlhi, hloh, hhi, hL, hH⟩ :=
    S.exists_seedEndpointCharts C hF hw hcurve hlt
  have makeWindow {endpoint l h : ℝ} (G : SeedEndpointChart S C endpoint)
      (hlh : l < h) (hI : ∀ t ∈ Icc l h, (w, t) ∈ G.geometry.U)
      (hsub : Ioo l h ⊆ Ioo lo hi) :
      Nonempty (PhysicalJacobiMomentWindow (C.intrinsicKernel bW)
        (μ.map (fun x : ℝ ↦ x - S.level)) l h) := by
    obtain ⟨hm, Rρ, _, hρnonneg, hρbound, hweight, hweight0⟩ :=
      G.population_density_weight_data hF hw hρ hρ0 (hv G.old) (hv0 G.old) hI c
    refine ⟨G.physicalMomentWindowOfDensity hF bW hcurve hlh hI ?_ ?_
      hm hρnonneg hρbound hweight hweight0 ?_⟩
    · intro t ht
      have hx := G.geometry.curve_source (w, t) (hI t (Ioo_subset_Icc_self ht))
      rw [← hcurve] at hx
      exact ⟨_, hjet G.old t hx⟩
    · intro t ht
      have hx := G.geometry.curve_source (w, t) (hI t (Ioo_subset_Icc_self ht))
      rw [← hcurve] at hx
      exact hpos G.old t (hactive (hsub ht)) hx
    · exact hdensity G.center G.label_mem (Ioo l h) measurableSet_Ioo
        (fun t ht ↦ ⟨hactive (hsub ht),
          G.time_mem_ball_of_mem_source (hI t (Ioo_subset_Icc_self ht))⟩)
  obtain ⟨WL⟩ := makeWindow L hlo hL (fun _ ht ↦ ⟨ht.1, ht.2.trans hlhi⟩)
  obtain ⟨WR⟩ := makeWindow H hhi hH (fun _ ht ↦ ⟨hloh.trans ht.1, ht.2⟩)
  exact originalClock_compliance_moments_of_endpoint_windows WL WR hlhi hloh hK
    (fun t ht ↦ (hKpos t ht).posSemidef) hroot hμ

end OTSelector.Reconstruction
