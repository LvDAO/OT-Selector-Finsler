import OTSelector.Reconstruction.OriginalStageResidualDensityReflectedMass
import OTSelector.Reconstruction.OriginalCubeReflectedInputFubini
import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutEndpoints

/-! Literal full-input reflected class densities split into raw smoothing and response. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

private theorem full_reflected_class_eq_raw_add_response_finite {q : ℕ}
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) {M R : ℝ}
    (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure (LegalMarkedPhysicalPoint q)) [IsFiniteMeasure σ] (z : Fin q → ℝ) :
    originalStageReflectedClassDensity η R C
      (σ.restrict {p | p.1 ∈ haarRootCube (Fin q) R}) z =
      (∫ p in {p | p.2 ∈ C}, η (z-p.1) ∂σ) +
        originalClassReflectedInputScalarField η R C σ z := by
  let W := {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R}
  let B := {p : LegalMarkedPhysicalPoint q | p.2 ∈ C}
  let f := W.indicator (B.indicator (fun p ↦ originalCubeReflectedKernel η R z p.1))
  let g := B.indicator (fun p ↦ η (z-p.1))
  have hW : MeasurableSet W := measurableSet_Icc.preimage measurable_fst
  have hB : MeasurableSet B := hC.preimage measurable_snd
  have hbound0 : 0 ≤ (3:ℝ)^q*M := mul_nonneg (by positivity) hM
  have hf : Integrable f σ := by
    apply Integrable.of_bound (f := f)
      (((measurable_originalCubeReflectedKernel hη R).comp
        (measurable_const.prodMk measurable_fst)).indicator hB |>.indicator hW).aestronglyMeasurable
      ((3:ℝ)^q*M)
    apply Eventually.of_forall
    intro p
    by_cases hw : p ∈ W <;> by_cases hb : p ∈ B
    · simpa only [f, indicator_of_mem hw, indicator_of_mem hb, Real.norm_eq_abs, Fintype.card_fin]
        using abs_originalCubeReflectedKernel_le hηM R z p.1
    all_goals simp [f, hw, hb, hbound0]
  have hg : Integrable g σ := by
    apply Integrable.of_bound (f := g) ((hη.comp (measurable_const.sub measurable_fst)).indicator hB).aestronglyMeasurable M
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ B
    · simpa only [g, indicator_of_mem hp, Real.norm_eq_abs] using hηM (z-p.1)
    · simp [g, hp, hM]
  have he : (fun p ↦ f p - g p) =
      fun p ↦ C.indicator (fun _ ↦ (1:ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1 := by
    funext p
    by_cases hc : p.2 ∈ C <;> by_cases hw : p.1 ∈ haarRootCube (Fin q) R <;>
      simp [f, g, W, B, originalCubeReflectedInputResponse, hc, hw]
  have h := integral_sub hf hg
  rw [he] at h
  have hfi : (∫ p, f p ∂σ) = originalStageReflectedClassDensity η R C (σ.restrict W) z := by
    rw [show f = W.indicator (B.indicator (fun p ↦ originalCubeReflectedKernel η R z p.1)) from rfl,
      integral_indicator hW, integral_indicator hB]
    rfl
  rw [hfi, show (∫ p, g p ∂σ) = ∫ p in B, η (z-p.1) ∂σ from integral_indicator hB] at h
  change originalClassReflectedInputScalarField η R C σ z =
    originalStageReflectedClassDensity η R C (σ.restrict W) z -
      (∫ p in B, η (z-p.1) ∂σ) at h
  linarith

/-- On the unchanged original full input measure, the genuine finite spatial window and
unit-range kernel give reflected smoothing = raw smoothing + literal full-input response.
This is valid with infinite total mass and preserves every original clock-class mark. -/
theorem originalFullInputReflectedClassDensity_eq_raw_add_response {q : ℕ}
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) {M R : ℝ}
    (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C) (σ : Measure (LegalMarkedPhysicalPoint q))
    (hσ : σ (haarRootCube (Fin q) (R+1) ×ˢ (univ : Set ℝ)) < ∞)
    {z : Fin q → ℝ} (hz : z ∈ haarRootCube (Fin q) R) :
    originalStageReflectedClassDensity η R C
      (σ.restrict {p | p.1 ∈ haarRootCube (Fin q) R}) z =
      (∫ p in {p | p.2 ∈ C}, η (z-p.1) ∂σ) +
        originalClassReflectedInputScalarField η R C σ z := by
  let W := haarRootCube (Fin q) (R+1) ×ˢ (univ : Set ℝ)
  let : IsFiniteMeasure (σ.restrict W) := ⟨by simpa only [Measure.restrict_apply_univ] using hσ⟩
  have h := full_reflected_class_eq_raw_add_response_finite (R := R) hη hM hηM hC (σ.restrict W) z
  have hsub : {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} ⊆ W := by
    intro p hp
    refine ⟨?_, mem_univ _⟩
    exact ⟨fun i ↦ by linarith [hp.1 i], fun i ↦ by linarith [hp.2 i]⟩
  have hWin : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} :=
    measurableSet_Icc.preimage measurable_fst
  rw [Measure.restrict_restrict hWin,
    inter_eq_left.mpr hsub] at h
  rw [← originalClassReflectedInputScalarField_eq_restrict_outer hsupport hR C σ hz] at h
  have hraw : (∫ p in {p | p.2 ∈ C}, η (z-p.1) ∂σ.restrict W) =
      ∫ p in {p | p.2 ∈ C}, η (z-p.1) ∂σ := by
    have hCB : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ C} := hC.preimage measurable_snd
    have hWW : MeasurableSet W := measurableSet_Icc.prod MeasurableSet.univ
    rw [Measure.restrict_restrict hCB, inter_comm, ← Measure.restrict_restrict hWW]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    apply hsupport
    by_contra! hn
    apply hp
    refine ⟨?_, mem_univ _⟩
    apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R+1) p.1).mpr
    have hzn := (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R) z).mp hz
    have hnorm := norm_sub_le z (z-p.1)
    rw [sub_sub_cancel] at hnorm
    linarith
  rw [hraw] at h
  exact h

/-- The full actual source endpoint slab is precisely the source color input restricted
by its original source clock, retaining the half-open convention [s,t). -/
theorem originalSceneSlabSourceMeasure_eq_fullInput {q : ℕ}
    {scene : LegalMarkedOptimalInputScene q} (hfull : IsFullOriginalInputMatching q scene)
    (s t : ℝ) :
    originalSceneSlabSourceMeasure s t scene =
      ((legalInputColorMeasure q scene.2 0).restrict {p | p.2 ∈ Ico s t}).map Prod.fst := by
  have h := originalRestrictedSceneSlabSourceMeasure_eq_edgeSource (A := univ) MeasurableSet.univ s t scene
  simpa only [Set.preimage_univ, Measure.restrict_univ, hfull.source_marginal,
    originalRestrictedSceneSlabSourceMeasure, originalRestrictedSceneMarkedPositionMeasure,
    originalSceneSlabSourceMeasure, originalSceneMarkedPositionMeasure] using h

/-- The full actual target endpoint slab is precisely the target color input restricted
by its unchanged target clock, retaining (s,t] at the two endpoints. -/
theorem originalSceneSlabTargetMeasure_eq_fullInput {q : ℕ}
    {scene : LegalMarkedOptimalInputScene q} (hfull : IsFullOriginalInputMatching q scene)
    (s t : ℝ) :
    originalSceneSlabTargetMeasure s t scene =
      ((legalInputColorMeasure q scene.2 1).restrict {p | p.2 ∈ Ioc s t}).map Prod.fst := by
  have h := originalRestrictedSceneSlabTargetMeasure_eq_edgeTarget (A := univ) MeasurableSet.univ s t scene
  simpa only [Set.preimage_univ, Measure.restrict_univ, hfull.target_marginal,
    originalRestrictedSceneSlabTargetMeasure, originalRestrictedSceneMarkedPositionMeasure,
    originalSceneSlabTargetMeasure, originalSceneMarkedPositionMeasure] using h

end OTSelector.Reconstruction
