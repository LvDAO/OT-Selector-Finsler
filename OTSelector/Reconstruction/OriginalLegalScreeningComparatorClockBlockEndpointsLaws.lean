import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedEqualMass
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedGoodCut
import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationNeumannEndpoint

/-! Literal same-frame background and actual port/reserve arrival laws split each stage law. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal BigOperators ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Real nonnegative summands split their actual density measures, using only AE
measurability; this supports actual locally integrable scene densities. -/
theorem withDensity_ofReal_add_of_ae_nonneg {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : AEMeasurable f μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    μ.withDensity (fun x ↦ ENNReal.ofReal (f x+g x)) =
      μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) + μ.withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
  ext s hs
  rw [withDensity_apply _ hs,Measure.add_apply,withDensity_apply _ hs,withDensity_apply _ hs]
  calc
    _ = ∫⁻ x in s, (ENNReal.ofReal (f x)+ENNReal.ofReal (g x)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hf0,ae_restrict_of_ae hg0] with x hx hy
      exact ENNReal.ofReal_add hx hy
    _ = _ := lintegral_add_left' hf.ennreal_ofReal.restrict _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalOrientedStageResidualDensityData
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
    (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell : ℝ}

/-- The literal omitted occupation plus the same actual gamma on the original physical cube. -/
def orientedBackgroundLaw (A : OriginalOrientedStageResidualDensityData S w b R ell) (c : ℝ) :=
  (A.cubeMeasure.withDensity (fun z ↦ ENNReal.ofReal
    (originalOrientedOmittedCutDensity S w b R ell c A.scene z+A.gamma c))).map
      (EuclideanSpace.equiv _ ℝ).symm

/-- The genuine same-frame source port class and exactly the surviving reserve class. -/
def orientedSourceArrivalLaw (A : OriginalOrientedStageResidualDensityData S w b R ell) (s t : ℝ) :=
  ((A.cubeMeasure.withDensity (fun z ↦ ENNReal.ofReal
      (originalOrientedStageReflectedClassDensity b R (Ico s t) A.sourcePortMeasure z))).map
        (EuclideanSpace.equiv _ ℝ).symm) +
    ENNReal.ofReal ((originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ)/A.cubeVolume) •
      A.cubeMeasure.map (EuclideanSpace.equiv _ ℝ).symm

/-- The target class keeps its actual closed-end Ioc clock convention. -/
def orientedTargetDepartureLaw (A : OriginalOrientedStageResidualDensityData S w b R ell) (s t : ℝ) :=
  ((A.cubeMeasure.withDensity (fun z ↦ ENNReal.ofReal
      (originalOrientedStageReflectedClassDensity b R (Ioc s t) A.targetPortMeasure z))).map
        (EuclideanSpace.equiv _ ℝ).symm) +
    ENNReal.ofReal ((originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ)/A.cubeVolume) •
      A.cubeMeasure.map (EuclideanSpace.equiv _ ℝ).symm
end OriginalOrientedStageResidualDensityData

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The actual source and target density laws split into their own finite background
and their actual port/reserve class law, in the same physical Euclidean space. Local
nonnegative gammas suffice; no full-grid common positive floor is imposed. -/
theorem ae_all_originalOrientedStageLaws_eq_background_add_class
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R) (s t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalOrientedStageResidualDensityData S w b R ell,
        A.scene = scene → 0 ≤ A.gamma s → 0 ≤ A.gamma t →
      IsFiniteMeasure (A.orientedBackgroundLaw s) ∧ IsFiniteMeasure (A.orientedBackgroundLaw t) ∧
      ((A.cubeMeasure.withDensity (fun z ↦ ENNReal.ofReal (A.sourceDensity s t z))).map
        (EuclideanSpace.equiv _ ℝ).symm) = A.orientedBackgroundLaw s + A.orientedSourceArrivalLaw s t ∧
      ((A.cubeMeasure.withDensity (fun z ↦ ENNReal.ofReal (A.targetDensity s t z))).map
        (EuclideanSpace.equiv _ ℝ).symm) = A.orientedBackgroundLaw t + A.orientedTargetDepartureLaw s t := by
  let q := finrank ℝ S.covector.ker
  let σ := volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))
  have he := (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable
  have : IsFiniteMeasure σ := ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_originalStagePhysicalCube b (2*R)).measure_lt_top⟩
  have hRone : 1 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hRpos : 0 < R := by linarith
  filter_upwards [D.ae_all_originalOrientedStagePortDensities_integrable_mass hF hw Q b (by linarith) hR hRone,
    ae_originalOrientedOmittedCutDensity_integrable S hF hw Q b R ell s,
    ae_originalOrientedOmittedCutDensity_integrable S hF hw Q b R ell t] with scene hports hνs hνt
  intro A hA hgs hgt
  rw [← hA] at hνs hνt hports
  have hnb (c : ℝ) (z : Fin q → ℝ) : 0 ≤ originalOrientedOmittedCutDensity S w b R ell c A.scene z :=
    originalOrientedOmittedCutDensity_nonneg S w b R ell c A.scene z
  have hnp (C : Set ℝ) (z : Fin q → ℝ) :
      0 ≤ originalOrientedStageReflectedClassDensity b R C A.sourcePortMeasure z :=
    originalOrientedStageReflectedClassDensity_nonneg b R C A.sourcePortMeasure z
  have hnt (C : Set ℝ) (z : Fin q → ℝ) :
      0 ≤ originalOrientedStageReflectedClassDensity b R C A.targetPortMeasure z :=
    originalOrientedStageReflectedClassDensity_nonneg b R C A.targetPortMeasure z
  have hsI := hνs.add (integrable_const (A.gamma s))
  have htI := hνt.add (integrable_const (A.gamma t))
  have hs0 : ∀ᵐ z ∂σ, 0 ≤ originalOrientedOmittedCutDensity S w b R ell s A.scene z+A.gamma s :=
    Eventually.of_forall (fun z ↦ add_nonneg (hnb s z) hgs)
  have ht0 : ∀ᵐ z ∂σ, 0 ≤ originalOrientedOmittedCutDensity S w b R ell t A.scene z+A.gamma t :=
    Eventually.of_forall (fun z ↦ add_nonneg (hnb t z) hgt)
  have : IsFiniteMeasure (σ.withDensity (fun z ↦ ENNReal.ofReal
      (originalOrientedOmittedCutDensity S w b R ell s A.scene z+A.gamma s))) :=
    originalDensityWithDensity_isFiniteMeasure σ _ hsI hs0
  have : IsFiniteMeasure (σ.withDensity (fun z ↦ ENNReal.ofReal
      (originalOrientedOmittedCutDensity S w b R ell t A.scene z+A.gamma t))) :=
    originalDensityWithDensity_isFiniteMeasure σ _ htI ht0
  refine ⟨?_,?_,?_,?_⟩
  · change IsFiniteMeasure ((σ.withDensity (fun z ↦ ENNReal.ofReal
        (originalOrientedOmittedCutDensity S w b R ell s A.scene z+A.gamma s))).map
          (EuclideanSpace.equiv _ ℝ).symm)
    exact Measure.isFiniteMeasure_map _ _
  · change IsFiniteMeasure ((σ.withDensity (fun z ↦ ENNReal.ofReal
        (originalOrientedOmittedCutDensity S w b R ell t A.scene z+A.gamma t))).map
          (EuclideanSpace.equiv _ ℝ).symm)
    exact Measure.isFiniteMeasure_map _ _
  · have hpI := (hports (Ico s t)).1.1
    change Integrable (originalOrientedStageReflectedClassDensity b R (Ico s t) A.sourcePortMeasure) σ at hpI
    have hc0 : 0 ≤ (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (Ico s t) : ℝ)/A.cubeVolume :=
      div_nonneg (Nat.cast_nonneg _) (A.cubeVolume_pos hRpos).le
    have h1 := withDensity_ofReal_add_of_ae_nonneg σ _ _ hsI.aemeasurable hs0 (Eventually.of_forall (hnp (Ico s t)))
    have h2 := withDensity_ofReal_add_of_ae_nonneg σ _ _ (hsI.add hpI).aemeasurable
      (hs0.mono fun z hz ↦ add_nonneg hz (hnp (Ico s t) z)) (Eventually.of_forall (fun _ ↦ hc0))
    simp only [Pi.add_apply] at h1 h2
    simp only [OriginalOrientedStageResidualDensityData.sourceDensity]
    change (σ.withDensity _).map _ = _
    rw [h2,h1,Measure.map_add _ _ he,Measure.map_add _ _ he,withDensity_const,Measure.map_smul]
    simp only [OriginalOrientedStageResidualDensityData.orientedBackgroundLaw,
      OriginalOrientedStageResidualDensityData.orientedSourceArrivalLaw,
      OriginalOrientedStageResidualDensityData.cubeMeasure,add_assoc,σ,q]
  · have hpI := (hports (Ioc s t)).2.1
    change Integrable (originalOrientedStageReflectedClassDensity b R (Ioc s t) A.targetPortMeasure) σ at hpI
    have hc0 : 0 ≤ (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (Ioc s t) : ℝ)/A.cubeVolume :=
      div_nonneg (Nat.cast_nonneg _) (A.cubeVolume_pos hRpos).le
    have h1 := withDensity_ofReal_add_of_ae_nonneg σ _ _ htI.aemeasurable ht0 (Eventually.of_forall (hnt (Ioc s t)))
    have h2 := withDensity_ofReal_add_of_ae_nonneg σ _ _ (htI.add hpI).aemeasurable
      (ht0.mono fun z hz ↦ add_nonneg hz (hnt (Ioc s t) z)) (Eventually.of_forall (fun _ ↦ hc0))
    simp only [Pi.add_apply] at h1 h2
    simp only [OriginalOrientedStageResidualDensityData.targetDensity]
    change (σ.withDensity _).map _ = _
    rw [h2,h1,Measure.map_add _ _ he,Measure.map_add _ _ he,withDensity_const,Measure.map_smul]
    simp only [OriginalOrientedStageResidualDensityData.orientedBackgroundLaw,
      OriginalOrientedStageResidualDensityData.orientedTargetDepartureLaw,
      OriginalOrientedStageResidualDensityData.cubeMeasure,add_assoc,σ,q]
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
