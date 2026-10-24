import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedFullCutIdentity
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetPhysicalFlux
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedInputLimit
import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeMeasurability

/-! The same original full-main cut error is negligible at true surface flux scale. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

private theorem integral_three_signed_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f g h : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) (hh : MemLp h 2 P) :
    (∫ sample, (f sample + g sample - h sample)^2 ∂P) ≤
      3*((∫ sample, (f sample)^2 ∂P)+(∫ sample, (g sample)^2 ∂P)+(∫ sample, (h sample)^2 ∂P)) := by
  calc
    _ ≤ ∫ sample, 3*((f sample)^2+(g sample)^2+(h sample)^2) ∂P := by
      apply integral_mono ((hf.add hg).sub hh).integrable_sq
        (((hf.integrable_sq.add hg.integrable_sq).add hh.integrable_sq).const_mul 3)
      intro sample
      change (f sample + g sample - h sample)^2 ≤ 3*((f sample)^2+(g sample)^2+(h sample)^2)
      nlinarith [sq_nonneg (f sample-g sample), sq_nonneg (f sample+h sample), sq_nonneg (g sample+h sample)]
    _ = _ := by
      rw [integral_const_mul, integral_add (f := fun sample ↦ (f sample)^2+(g sample)^2)
        (g := fun sample ↦ (h sample)^2) (hf.integrable_sq.add hg.integrable_sq) hh.integrable_sq,
        integral_add (f := fun sample ↦ (f sample)^2) (g := fun sample ↦ (g sample)^2)
          hf.integrable_sq hg.integrable_sq]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The unchanged actual full-main delta has finite second moment and vanishing normalized
surface-scale second moment in the same selected physical frame. Actual positive FTC,
Gauss-Green, full-input Poisson moments and the true normal projections supply all three terms. -/
theorem OriginalSeedConditionalMoments.originalOrientedStageFullCutError_surface_ltwo_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 1 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {c : ℝ} (hc : D.lo + (S.level : ℝ) ≤ c)
    (hj : ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (D.lo + (S.level : ℝ)) c) scene k) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (hproj : ∀ i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _) (Ioc (D.lo + (S.level : ℝ)) c)) hj
        (originalEuclideanNormalReadout (b i))) = 0) :
    (∀ R, 1 ≤ R → MemLp (originalOrientedStageFullCutError S w b R c) 2 (Q.law : Measure _)) ∧
    Tendsto (fun R : ℝ ↦ ∫ scene,
      ((R^(finrank ℝ S.covector.ker-1))⁻¹ * originalOrientedStageFullCutError S w b R c scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  let lo := D.lo + (S.level : ℝ)
  let j := originalSeedPathClockSetCurrent S w η (Ioc lo c)
  let flux := fun R scene ↦ originalScreeningPhysicalCurrentBoundaryPairing b
    (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) (2*R) (fun _ ↦ 1)
  let src := fun R ↦ originalScreeningOrientedReflectedInputMass b R (Ico lo c) 0
  let tgt := fun R ↦ originalScreeningOrientedReflectedInputMass b R (Ioc lo c) 1
  have hmη : Measurable η := (contDiff_originalEuclideanMollifier q).continuous.measurable
  have hmj : Measurable j := by
    have h := (stronglyMeasurable_originalFullCurrent_joint_spatial S hF hw hmη (Ioc lo c)).measurable.comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : LegalMarkedOptimalInputScene q ↦ (0 : Fin q → ℝ))))
    simpa only [Function.comp_def, id_eq, sub_zero] using h
  have he (R : ℝ) (hR : 1 ≤ R) : originalOrientedStageFullCutError S w b R c =ᵐ[(Q.law : Measure _)]
      fun scene ↦ flux R scene + src R scene - tgt R scene := by
    filter_upwards [D.ae_originalOrientedStageFullCutError_eq_flux_add_inputMasses
      hF hw hbounds Q b hR hc] with scene hs
    have hfun : (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) =
        fun z ↦ originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (Ioc lo c) scene := by
      funext z
      exact originalSeedPathClockSetCurrent_reroot S hF hw hmη (Ioc lo c) z scene
    change originalOrientedStageFullCutError S w b R c scene =
      originalScreeningPhysicalCurrentBoundaryPairing b
        (fun z ↦ j (legalMarkedInputSceneReroot q z scene)) (2*R) (fun _ ↦ 1) + src R scene - tgt R scene
    rw [hfun]
    exact hs
  have hLp (R : ℝ) (hR : 1 ≤ R) : MemLp (flux R) 2 (Q.law : Measure _) ∧
      MemLp (src R) 2 (Q.law : Measure _) ∧ MemLp (tgt R) 2 (Q.law : Measure _) := by
    have hRp : 0 < R := by linarith
    let x := fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
      (originalEuclideanNormalReadout (b i))
    have hr := (memLp_two_iff_integrable_sq
      (Q.measurable_sceneRawCenteredCubeFlux b x hRp).aestronglyMeasurable).mpr
      (Q.integrable_sq_sceneRawCenteredCubeFlux b x hRp)
    have hrp : Q.sceneRawCenteredCubeFlux b x R =ᵐ[(Q.law : Measure _)] flux R := by
      filter_upwards [Q.ae_originalScreening_physicalFlux_eq_raw b j hj hmj R] with scene hs
      exact hs.symm
    refine ⟨hr.ae_eq hrp, ?_, ?_⟩
    · exact (Q.originalScreening_orientedInputMass_moments b hR measurableSet_Ico 0).1
    · exact (Q.originalScreening_orientedInputMass_moments b hR measurableSet_Ioc 1).1
  refine ⟨fun R hR ↦ (((hLp R hR).1.add (hLp R hR).2.1).sub (hLp R hR).2.2).ae_eq (he R hR).symm, ?_⟩
  have hf := Q.tendsto_originalScreening_physicalFlux_normalized_sq_zero b j hj hmj hproj
  have hs := Q.tendsto_originalScreening_orientedInputMass_normalized_sq_zero (C := Ico lo c) b hq measurableSet_Ico (0 : Fin 2)
  have ht := Q.tendsto_originalScreening_orientedInputMass_normalized_sq_zero (C := Ioc lo c) b hq measurableSet_Ioc (1 : Fin 2)
  have hlim := ((hf.add hs).add ht).const_mul 3
  simp only [add_zero, mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))) ?_ hlim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
  have hb := integral_three_signed_sq_le ((hLp R hR).1.const_mul ((R^(q-1))⁻¹))
    ((hLp R hR).2.1.const_mul ((R^(q-1))⁻¹)) ((hLp R hR).2.2.const_mul ((R^(q-1))⁻¹))
  calc
    _ = ∫ scene, ((R^(q-1))⁻¹ * flux R scene + (R^(q-1))⁻¹ * src R scene -
        (R^(q-1))⁻¹ * tgt R scene)^2 ∂(Q.law : Measure _) := by
      apply integral_congr_ae
      filter_upwards [he R hR] with scene hscene
      rw [hscene]
      ring
    _ ≤ _ := hb

end OTSelector.Reconstruction
