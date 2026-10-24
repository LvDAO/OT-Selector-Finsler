import OTSelector.Reconstruction.OriginalStageResidualDensityUniformReserves
import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationNeumannEndpoint

/-! Actual background, port and surviving-reserve laws split the original stage
marginals in physical Euclidean space. True empty endpoint cuts give zero backgrounds. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

private theorem realDensity_add_of_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : AEMeasurable f μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    μ.withDensity (fun x ↦ ENNReal.ofReal (f x+g x)) =
      μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) +
        μ.withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.add_apply,
    withDensity_apply _ hs, withDensity_apply _ hs]
  calc
    _ = ∫⁻ x in s, (ENNReal.ofReal (f x)+ENNReal.ofReal (g x)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hf0, ae_restrict_of_ae hg0] with x hx hy
      exact ENNReal.ofReal_add hx hy
    _ = _ := lintegral_add_left' hf.ennreal_ofReal.restrict _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {R ell : ℝ}
  {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}

/-- The literal positive omitted occupation plus the actual gamma at this cut,
read in physical Euclidean coordinates on the original cube. -/
def backgroundLaw (A : OriginalStageResidualDensityData S w R ell η) (c : ℝ) :=
  ((volume.restrict (haarRootCube _ R)).withDensity (fun z ↦ ENNReal.ofReal
    (originalOmittedCutDensity S w R ell c η z A.scene+A.gamma c))).map
      (EuclideanSpace.equiv _ ℝ).symm

/-- True smoothed source ports and the actual surviving source class count density. -/
def sourceArrivalLaw (A : OriginalStageResidualDensityData S w R ell η) (s t : ℝ) :=
  (((volume.restrict (haarRootCube _ R)).withDensity (fun z ↦ ENNReal.ofReal
      (originalStageSourcePortDensity S w R ell η (Ico s t) A.scene z))).map
        (EuclideanSpace.equiv _ ℝ).symm) +
    ENNReal.ofReal ((originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept
      (Ico s t) : ℝ)/A.cubeVolume) •
        (volume.restrict (haarRootCube _ R)).map (EuclideanSpace.equiv _ ℝ).symm

/-- True smoothed target ports and the actual surviving target class count density. -/
def targetDepartureLaw (A : OriginalStageResidualDensityData S w R ell η) (s t : ℝ) :=
  (((volume.restrict (haarRootCube _ R)).withDensity (fun z ↦ ENNReal.ofReal
      (originalStageTargetPortDensity S w R ell η (Ioc s t) A.scene z))).map
        (EuclideanSpace.equiv _ ℝ).symm) +
    ENNReal.ofReal ((originalStageRemainingReserveClassCount A.targetReserve A.targetKept
      (Ioc s t) : ℝ)/A.cubeVolume) •
        (volume.restrict (haarRootCube _ R)).map (EuclideanSpace.equiv _ ℝ).symm

/-- A true empty full cut has no omitted occupation. Together with the actual zero
gamma this makes the very same background law zero, without a replacement law. -/
theorem backgroundLaw_eq_zero_of_empty_cut
    (A : OriginalStageResidualDensityData S w R ell η)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (c : ℝ)
    (hcut : originalSceneActiveCutMeasure S w c A.scene = 0) (hγ : A.gamma c = 0) :
    A.backgroundLaw c = 0 := by
  have hsplit := originalSceneActiveCut_eq_retained_add_omitted S hF hw R ell c A.scene
  have hle : originalOmittedSceneActiveCutMeasure S w R ell c A.scene ≤
      originalSceneActiveCutMeasure S w c A.scene := by
    rw [hsplit]
    exact Measure.le_add_left le_rfl
  have hom : originalOmittedSceneActiveCutMeasure S w R ell c A.scene = 0 :=
    le_antisymm (hcut ▸ hle) bot_le
  simp only [backgroundLaw, originalOmittedCutDensity, hom, integral_zero_measure,
    hγ, add_zero, ENNReal.ofReal_zero]
  change (((volume.restrict (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)).withDensity
    (0 : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞)).map _) = 0
  rw [withDensity_zero, Measure.map_zero]
end OriginalStageResidualDensityData

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- On one original-scene event both actual stage density laws split into the
same finite background and literal port/reserve class laws whenever the actual
gammas are nonnegative. All local integrability is produced from the original scene. -/
theorem ae_all_originalCanonicalStageLaws_eq_background_add_class
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*ell ≤ R) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier _),
      A.scene = scene → 0 ≤ A.gamma s → 0 ≤ A.gamma t →
      IsFiniteMeasure (A.backgroundLaw s) ∧ IsFiniteMeasure (A.backgroundLaw t) ∧
      (((volume.restrict (haarRootCube _ R)).withDensity
        (fun z ↦ ENNReal.ofReal (A.sourceDensity s t z))).map (EuclideanSpace.equiv _ ℝ).symm) =
          A.backgroundLaw s + A.sourceArrivalLaw s t ∧
      (((volume.restrict (haarRootCube _ R)).withDensity
        (fun z ↦ ENNReal.ofReal (A.targetDensity s t z))).map (EuclideanSpace.equiv _ ℝ).symm) =
          A.backgroundLaw t + A.targetDepartureLaw s t := by
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  let σ := volume.restrict (haarRootCube (Fin q) R)
  have he := (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable
  have : IsFiniteMeasure σ := ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  have hRpos : 0 < R := by linarith
  have hη := (contDiff_originalEuclideanMollifier q).continuous.measurable
  have hηM := abs_originalEuclideanMollifier_le q
  have hsupport := raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)
  have heven := coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q)
  filter_upwards [D.ae_all_originalStagePortDensities_integrable_mass hF hw Q (by linarith) hR
      (by linarith) hη (integrable_originalEuclideanMollifier q)
      (integral_originalEuclideanMollifier_eq_one q) hsupport heven hηM,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q hRpos.le ell s hη hηM hsupport,
    ae_originalOmittedCutDensity_integrableOn_cube S hF hw Q hRpos.le ell t hη hηM hsupport]
      with scene hports hνs hνt
  intro A hA hgs hgt
  rw [← hA] at hνs hνt hports
  have hnb (c : ℝ) : ∀ z, 0 ≤ originalOmittedCutDensity S w R ell c η z A.scene :=
    fun z ↦ originalOmittedCutDensity_nonneg S w R ell c (originalEuclideanMollifier_nonneg q) z A.scene
  have hnp (C : Set ℝ) : ∀ z, 0 ≤ originalStageSourcePortDensity S w R ell η C A.scene z :=
    fun z ↦ originalStageReflectedClassDensity_nonneg (originalEuclideanMollifier_nonneg q) R _ _ z
  have hnt (C : Set ℝ) : ∀ z, 0 ≤ originalStageTargetPortDensity S w R ell η C A.scene z :=
    fun z ↦ originalStageReflectedClassDensity_nonneg (originalEuclideanMollifier_nonneg q) R _ _ z
  have hsI := hνs.add (integrable_const (A.gamma s))
  have htI := hνt.add (integrable_const (A.gamma t))
  have hs0 : ∀ᵐ z ∂σ, 0 ≤ originalOmittedCutDensity S w R ell s η z A.scene+A.gamma s :=
    Eventually.of_forall (fun z ↦ add_nonneg (hnb s z) hgs)
  have ht0 : ∀ᵐ z ∂σ, 0 ≤ originalOmittedCutDensity S w R ell t η z A.scene+A.gamma t :=
    Eventually.of_forall (fun z ↦ add_nonneg (hnb t z) hgt)
  have : IsFiniteMeasure (σ.withDensity (fun z ↦ ENNReal.ofReal
      (originalOmittedCutDensity S w R ell s η z A.scene+A.gamma s))) :=
    originalDensityWithDensity_isFiniteMeasure σ _ hsI hs0
  have : IsFiniteMeasure (σ.withDensity (fun z ↦ ENNReal.ofReal
      (originalOmittedCutDensity S w R ell t η z A.scene+A.gamma t))) :=
    originalDensityWithDensity_isFiniteMeasure σ _ htI ht0
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold OriginalStageResidualDensityData.backgroundLaw
    exact Measure.isFiniteMeasure_map _ _
  · unfold OriginalStageResidualDensityData.backgroundLaw
    exact Measure.isFiniteMeasure_map _ _
  · have hpI := (hports (Ico s t)).1.1
    have hc0 : 0 ≤ (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ)/A.cubeVolume :=
      div_nonneg (Nat.cast_nonneg _) (A.cubeVolume_pos hRpos).le
    have h1 := realDensity_add_of_nonneg σ _ _ hsI.aemeasurable hs0
      (Eventually.of_forall (hnp (Ico s t)))
    have h2 := realDensity_add_of_nonneg σ _ _ (hsI.add hpI).aemeasurable
      (hs0.mono (fun z hz ↦ add_nonneg hz (hnp (Ico s t) z)))
      (Eventually.of_forall (fun _ ↦ hc0))
    simp only [Pi.add_apply] at h1 h2
    simp only [OriginalStageResidualDensityData.sourceDensity]
    change (σ.withDensity _).map _ = _
    rw [h2, h1, Measure.map_add _ _ he, Measure.map_add _ _ he, withDensity_const, Measure.map_smul]
    simp only [OriginalStageResidualDensityData.backgroundLaw,
      OriginalStageResidualDensityData.sourceArrivalLaw, add_assoc, σ, η, q]
  · have hpI := (hports (Ioc s t)).2.1
    have hc0 : 0 ≤ (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ)/A.cubeVolume :=
      div_nonneg (Nat.cast_nonneg _) (A.cubeVolume_pos hRpos).le
    have h1 := realDensity_add_of_nonneg σ _ _ htI.aemeasurable ht0
      (Eventually.of_forall (hnt (Ioc s t)))
    have h2 := realDensity_add_of_nonneg σ _ _ (htI.add hpI).aemeasurable
      (ht0.mono (fun z hz ↦ add_nonneg hz (hnt (Ioc s t) z)))
      (Eventually.of_forall (fun _ ↦ hc0))
    simp only [Pi.add_apply] at h1 h2
    simp only [OriginalStageResidualDensityData.targetDensity]
    change (σ.withDensity _).map _ = _
    rw [h2, h1, Measure.map_add _ _ he, Measure.map_add _ _ he, withDensity_const, Measure.map_smul]
    simp only [OriginalStageResidualDensityData.backgroundLaw,
      OriginalStageResidualDensityData.targetDepartureLaw, add_assoc, σ, η, q]
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
