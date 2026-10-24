import OTSelector.Reconstruction.OriginalRetainedSlabResidualBoundaryCurrent
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedKernel

/-! Actual retained endpoints have exactly equal raw and reflected smoothing in the cube. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Every occupied original retained endpoint lies deeply enough that the literal reflected
kernel equals the raw kernel, simultaneously for both colors and every cube observation. -/
theorem ae_all_originalRetainedEndpoints_reflectedKernel_eq_raw
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ e ∈ (originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support,
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        (∀ y, 1 ≤ ‖y‖ → η y = 0) →
      ∀ z ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R,
        originalCubeReflectedKernel η R z e.1.1 = η (z - e.1.1) ∧
        originalCubeReflectedKernel η R z e.2.1 = η (z - e.2.1) := by
  filter_upwards [D.ae_originalPathRetainedPlan_legal_inner_paths hF hw Q
    (show 0 ≤ ell by linarith) hR] with scene hscene
  intro e he η hη z hz
  have hsource := (hscene e he).2.2.2.1
  have htarget := (hscene e he).2.2.2.2.1
  have hinner (x : Fin (finrank ℝ S.covector.ker) → ℝ)
      (hx : x ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell)) :
      x ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - 1) := by
    constructor
    · intro i
      have hi := hx.1 i
      dsimp at hi ⊢
      linarith
    · intro i
      have hi := hx.2 i
      dsimp at hi ⊢
      linarith
  exact ⟨originalCubeReflectedKernel_eq_kernel_of_inner hη hz (hinner _ hsource),
    originalCubeReflectedKernel_eq_kernel_of_inner hη hz (hinner _ htarget)⟩

/-- Raw and reflected smoothing of the actual retained source and target measures agree.
Any further restriction of the unchanged retained edges, including a true clock class, is allowed. -/
theorem ae_all_originalRetainedEndpoints_reflectedSmoothing_eq_raw
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        (∀ y, 1 ≤ ‖y‖ → η y = 0) →
      ∀ (B : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        (z : Fin (finrank ℝ S.covector.ker) → ℝ),
        z ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) R →
        (∫ e in B, originalCubeReflectedKernel η R z e.1.1
          ∂(originalPathRetainedPlan S w R ell scene : Measure
            (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) =
          (∫ e in B, η (z - e.1.1)
            ∂(originalPathRetainedPlan S w R ell scene : Measure
              (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) ∧
        (∫ e in B, originalCubeReflectedKernel η R z e.2.1
          ∂(originalPathRetainedPlan S w R ell scene : Measure
            (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) =
          (∫ e in B, η (z - e.2.1)
            ∂(originalPathRetainedPlan S w R ell scene : Measure
              (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))) := by
  filter_upwards [D.ae_all_originalRetainedEndpoints_reflectedKernel_eq_raw hF hw Q hell hR]
    with scene hscene
  intro η hη B z hz
  have hsupport : ∀ᵐ e ∂(originalPathRetainedPlan S w R ell scene : Measure
      (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))),
      e ∈ (originalPathRetainedPlan S w R ell scene : Measure
        (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support :=
    Measure.support_mem_ae
  constructor
  · apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hsupport] with e he
    exact (hscene e he η hη z hz).1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hsupport] with e he
    exact (hscene e he η hη z hz).2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
