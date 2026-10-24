import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeMeasurability
import OTSelector.Reconstruction.OriginalStageResidualNeumannBudgetBulkEnergy

/-! The actual omitted-current Euclidean energy is a genuine measurable random readout. -/
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

/-- The literal original Euclidean bulk energy of the same canonical full-minus-retained
clock current, with spatial integration on the original physical cube. -/
def originalCanonicalOmittedCurrentLtwoEnergy (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell : ℝ) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  originalStageCurrentLtwoEnergy (fun z ↦
    originalSeedPathClockSetCurrent S w (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene -
    originalRetainedSeedPathClockSetCurrent S w R ell
      (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene) R

/-- Joint measurability of the true original current produces measurable actual energy. -/
theorem measurable_originalCanonicalOmittedCurrentLtwoEnergy
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ) (A : Set ℝ) :
    Measurable (originalCanonicalOmittedCurrentLtwoEnergy S w R ell A) := by
  have hm := measurable_originalOmittedCurrent_joint_spatial S hF hw R ell
    (contDiff_originalEuclideanMollifier _).continuous.measurable A
  have hv := ((EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm.continuous.measurable.comp hm).norm.pow_const 2
  exact hv.stronglyMeasurable.integral_prod_right'.measurable

/-- Finite genuine nonnegative square mean produces the corresponding integrable real
random energy, and its expectation is exactly the same nonnegative integral. -/
theorem integral_originalCanonicalOmittedCurrentLtwoEnergy_eq_of_finite
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (R ell : ℝ) (A : Set ℝ)
    (P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (hfinite : (∫⁻ scene, ∫⁻ z in haarRootCube (Fin (finrank ℝ S.covector.ker)) R,
      ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm
        (originalSeedPathClockSetCurrent S w (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene -
          originalRetainedSeedPathClockSetCurrent S w R ell
            (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene)‖^2) ∂volume ∂P) ≠ (∞ : ℝ≥0∞)) :
    Integrable (originalCanonicalOmittedCurrentLtwoEnergy S w R ell A) P ∧
    (∫ scene, originalCanonicalOmittedCurrentLtwoEnergy S w R ell A scene ∂P) =
      (∫⁻ scene, ∫⁻ z in haarRootCube (Fin (finrank ℝ S.covector.ker)) R,
      ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ).symm
        (originalSeedPathClockSetCurrent S w (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene -
          originalRetainedSeedPathClockSetCurrent S w R ell
            (fun x ↦ originalEuclideanMollifier _ (x-z)) A scene)‖^2) ∂volume ∂P).toReal := by
  let q := finrank ℝ S.covector.ker
  let f := fun p : LegalMarkedOptimalInputScene q × (Fin q → ℝ) ↦
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm
      (originalSeedPathClockSetCurrent S w (fun x ↦ originalEuclideanMollifier q (x-p.2)) A p.1 -
        originalRetainedSeedPathClockSetCurrent S w R ell
          (fun x ↦ originalEuclideanMollifier q (x-p.2)) A p.1)‖^2
  have hm : Measurable f :=
    ((EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.comp
      (measurable_originalOmittedCurrent_joint_spatial S hF hw R ell
        (contDiff_originalEuclideanMollifier q).continuous.measurable A)).norm.pow_const 2
  let μ := volume.restrict (haarRootCube (Fin q) R)
  have hs : ∀ᵐ scene ∂P, (∫⁻ z, ENNReal.ofReal (f (scene,z)) ∂μ) ≠ (∞ : ℝ≥0∞) :=
    (ae_lt_top (hm.ennreal_ofReal.lintegral_prod_right' (ν := μ)) hfinite).mono fun _ h ↦ h.ne
  have he : (fun scene ↦ ENNReal.ofReal (originalCanonicalOmittedCurrentLtwoEnergy S w R ell A scene)) =ᵐ[P]
      fun scene ↦ ∫⁻ z, ENNReal.ofReal (f (scene,z)) ∂μ := by
    filter_upwards [hs] with scene hscene
    have hf := (lintegral_ofReal_ne_top_iff_integrable
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ sq_nonneg _)).mp hscene
    exact ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall fun z ↦ sq_nonneg _)
  have hE := measurable_originalCanonicalOmittedCurrentLtwoEnergy S hF hw R ell A
  have hnonneg : 0 ≤ᵐ[P] originalCanonicalOmittedCurrentLtwoEnergy S w R ell A :=
    Eventually.of_forall (fun scene ↦ originalStageCurrentLtwoEnergy_nonneg _ _)
  have hmean := lintegral_congr_ae he
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hE.aestronglyMeasurable hnonneg).mp
    (by rw [hmean]; exact hfinite), ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hE.aestronglyMeasurable, hmean]

end OTSelector.Reconstruction
