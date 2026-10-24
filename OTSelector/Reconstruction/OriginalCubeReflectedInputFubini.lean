import OTSelector.Reconstruction.OriginalCubeReflectedHilbertIntensity

/-! Genuine Fubini representation of the literal reflected input scalar field. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

/-- The literal class-marked reflected field of the same original finite input measure. -/
def originalClassReflectedInputScalarField (η : (Fin q → ℝ) → ℝ) (R : ℝ)
    (C : Set ℝ) (σ : Measure ((Fin q → ℝ) × ℝ)) (z : Fin q → ℝ) : ℝ :=
  ∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1 ∂σ

private theorem measurable_originalClassReflectedInputScalarIntegrand
    (hη : Measurable η) (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C) :
    Measurable (fun p : ((Fin q → ℝ) × ℝ) × (Fin q → ℝ) ↦
      C.indicator (fun _ ↦ (1 : ℝ)) p.1.2 * originalCubeReflectedInputResponse η R p.2 p.1.1) :=
  ((measurable_const.indicator hC).comp measurable_fst.snd).mul
    ((measurable_originalCubeReflectedInputResponse hη R).comp (measurable_snd.prodMk measurable_fst.fst))

/-- The literal scalar input field is measurable, directly from the actual joint kernel. -/
theorem measurable_originalClassReflectedInputScalarField
    (hη : Measurable η) (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ)) [SFinite σ] :
    Measurable (originalClassReflectedInputScalarField η R C σ) := by
  change Measurable (fun z ↦ ∫ p,
    C.indicator (fun _ ↦ (1 : ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1 ∂σ)
  exact (measurable_originalClassReflectedInputScalarIntegrand hη R hC).stronglyMeasurable.integral_prod_left'.measurable

/-- The actual bounded reflected kernel against a continuous original test is product
integrable for every finite original input measure, before any interchange of integrals. -/
theorem integrable_originalClassReflectedInputScalarField_test_prod
    (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ)) [IsFiniteMeasure σ]
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    Integrable (fun p : ((Fin q → ℝ) × ℝ) × (Fin q → ℝ) ↦
      (C.indicator (fun _ ↦ (1 : ℝ)) p.1.2 * originalCubeReflectedInputResponse η R p.2 p.1.1) * u p.2)
      (σ.prod (volume.restrict (haarRootCube (Fin q) R))) := by
  let D : ℝ := ((3 : ℝ)^q + 1) * M
  have hD : 0 ≤ D := mul_nonneg (by positivity) hM
  have hi : Integrable (fun _ : (Fin q → ℝ) × ℝ ↦ D) σ := integrable_const _
  have huI : Integrable u (volume.restrict (haarRootCube (Fin q) R)) :=
    hu.continuousOn.integrableOn_Icc
  have hm : Measurable (fun p : ((Fin q → ℝ) × ℝ) × (Fin q → ℝ) ↦
      (C.indicator (fun _ ↦ (1 : ℝ)) p.1.2 * originalCubeReflectedInputResponse η R p.2 p.1.1) * u p.2) :=
    (measurable_originalClassReflectedInputScalarIntegrand hη R hC).mul (hu.measurable.comp measurable_snd)
  apply (hi.mul_prod huI.norm).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro p
  change ‖(C.indicator (fun _ ↦ (1 : ℝ)) p.1.2 * originalCubeReflectedInputResponse η R p.2 p.1.1) * u p.2‖ ≤ D * ‖u p.2‖
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Real.norm_eq_abs]
  by_cases ha : p.1.2 ∈ C
  · simpa only [indicator_of_mem ha, one_mul, Fintype.card_fin] using
      abs_originalCubeReflectedInputResponse_le hM hηM R p.2 p.1.1
  · rw [indicator_of_notMem ha, zero_mul, abs_zero]
    exact hD

/-- The literal scalar field times every continuous original test is genuinely integrable. -/
theorem integrable_originalClassReflectedInputScalarField_mul
    (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ)) [IsFiniteMeasure σ]
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    Integrable (fun z ↦ originalClassReflectedInputScalarField η R C σ z * u z)
      (volume.restrict (haarRootCube (Fin q) R)) := by
  have hi := (integrable_originalClassReflectedInputScalarField_test_prod hη hM hηM R hC σ hu).integral_prod_right
  apply hi.congr
  exact ae_of_all _ (fun z ↦ integral_mul_const (μ := σ) (u z)
    (fun p : (Fin q → ℝ) × ℝ ↦ C.indicator (fun _ ↦ (1 : ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1))

/-- The literal scalar field itself is integrable on the original observation cube. -/
theorem integrable_originalClassReflectedInputScalarField
    (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ)) [IsFiniteMeasure σ] :
    Integrable (originalClassReflectedInputScalarField η R C σ)
      (volume.restrict (haarRootCube (Fin q) R)) := by
  simpa only [mul_one] using integrable_originalClassReflectedInputScalarField_mul hη hM hηM R hC σ
    (u := fun _ ↦ (1 : ℝ)) continuous_const

/-- Genuine bounded-product Fubini identifies the literal scalar-field test pairing with
the original class-marked input integral of its actual reflected-kernel test responses. -/
theorem integral_originalClassReflectedInputScalarField_mul_eq
    (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C)
    (σ : Measure ((Fin q → ℝ) × ℝ)) [IsFiniteMeasure σ]
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    (∫ z in haarRootCube (Fin q) R, originalClassReflectedInputScalarField η R C σ z * u z) =
      ∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
        (∫ z in haarRootCube (Fin q) R, originalCubeReflectedInputResponse η R z p.1 * u z) ∂σ := by
  calc
    _ = ∫ z in haarRootCube (Fin q) R, ∫ p,
        (C.indicator (fun _ ↦ (1 : ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1) * u z ∂σ := by
      exact integral_congr_ae (ae_of_all _ (fun z ↦ (integral_mul_const (μ := σ) (u z)
        (fun p : (Fin q → ℝ) × ℝ ↦ C.indicator (fun _ ↦ (1 : ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1)).symm))
    _ = ∫ p, (∫ z in haarRootCube (Fin q) R,
        (C.indicator (fun _ ↦ (1 : ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1) * u z) ∂σ :=
      (integral_integral_swap (integrable_originalClassReflectedInputScalarField_test_prod hη hM hηM R hC σ hu)).symm
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro p
      change (∫ z in haarRootCube (Fin q) R,
        (C.indicator (fun _ ↦ (1 : ℝ)) p.2 * originalCubeReflectedInputResponse η R z p.1) * u z) =
        C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
          ∫ z in haarRootCube (Fin q) R, originalCubeReflectedInputResponse η R z p.1 * u z
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun _ ↦ mul_assoc _ _ _)

/-- Actual unit-range geometry removes every original input outside the expanded cube,
even when the full original input measure has infinite total mass. -/
theorem originalClassReflectedInputScalarField_eq_restrict_outer
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    (C : Set ℝ) (σ : Measure ((Fin q → ℝ) × ℝ))
    {z : Fin q → ℝ} (hz : z ∈ haarRootCube (Fin q) R) :
    originalClassReflectedInputScalarField η R C σ z =
      originalClassReflectedInputScalarField η R C
        (σ.restrict (haarRootCube (Fin q) (R + 1) ×ˢ (Set.univ : Set ℝ))) z := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hx : p.1 ∉ haarRootCube (Fin q) (R + 1) := fun h ↦ hp ⟨h, Set.mem_univ _⟩
  rw [originalCubeReflectedInputResponse_eq_zero_off_shell hηsupport hR hz (fun hs ↦ hx hs.1), mul_zero]

/-- The literal field times a continuous test is integrable under only the actual finite
expanded input-window mass; no global finite-input assumption is required. -/
theorem integrable_originalClassReflectedInputScalarField_mul_of_finite_outer
    (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C) (σ : Measure ((Fin q → ℝ) × ℝ))
    (hσ : σ (haarRootCube (Fin q) (R + 1) ×ˢ (Set.univ : Set ℝ)) < ∞)
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    Integrable (fun z ↦ originalClassReflectedInputScalarField η R C σ z * u z)
      (volume.restrict (haarRootCube (Fin q) R)) := by
  let A := haarRootCube (Fin q) (R + 1) ×ˢ (Set.univ : Set ℝ)
  let : IsFiniteMeasure (σ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hσ⟩
  apply (integrable_originalClassReflectedInputScalarField_mul hη hM hηM R hC (σ.restrict A) hu).congr
  filter_upwards [ae_restrict_mem (show MeasurableSet (haarRootCube (Fin q) R) from measurableSet_Icc)] with z hz
  rw [originalClassReflectedInputScalarField_eq_restrict_outer hηsupport hR C σ hz]

/-- Genuine Fubini for the unchanged full original input measure follows from actual
finite local input-window mass and proved reflected-kernel support geometry. -/
theorem integral_originalClassReflectedInputScalarField_mul_eq_of_finite_outer
    (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ v, |η v| ≤ M)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C) (σ : Measure ((Fin q → ℝ) × ℝ))
    (hσ : σ (haarRootCube (Fin q) (R + 1) ×ˢ (Set.univ : Set ℝ)) < ∞)
    {u : (Fin q → ℝ) → ℝ} (hu : Continuous u) :
    (∫ z in haarRootCube (Fin q) R, originalClassReflectedInputScalarField η R C σ z * u z) =
      ∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
        (∫ z in haarRootCube (Fin q) R, originalCubeReflectedInputResponse η R z p.1 * u z) ∂σ := by
  let A := haarRootCube (Fin q) (R + 1) ×ˢ (Set.univ : Set ℝ)
  let : IsFiniteMeasure (σ.restrict A) := ⟨by simpa only [Measure.restrict_apply_univ] using hσ⟩
  calc
    _ = ∫ z in haarRootCube (Fin q) R,
        originalClassReflectedInputScalarField η R C (σ.restrict A) z * u z := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (show MeasurableSet (haarRootCube (Fin q) R) from measurableSet_Icc)] with z hz
      rw [originalClassReflectedInputScalarField_eq_restrict_outer hηsupport hR C σ hz]
    _ = ∫ p, C.indicator (fun _ ↦ (1 : ℝ)) p.2 *
        (∫ z in haarRootCube (Fin q) R, originalCubeReflectedInputResponse η R z p.1 * u z) ∂σ.restrict A :=
      integral_originalClassReflectedInputScalarField_mul_eq hη hM hηM R hC (σ.restrict A) hu
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hx : p.1 ∉ haarRootCube (Fin q) (R + 1) := fun h ↦ hp ⟨h, Set.mem_univ _⟩
      have hz0 : (∫ z in haarRootCube (Fin q) R,
          originalCubeReflectedInputResponse η R z p.1 * u z) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem (show MeasurableSet (haarRootCube (Fin q) R) from measurableSet_Icc)] with z hz
        rw [originalCubeReflectedInputResponse_eq_zero_off_shell hηsupport hR hz (fun hs ↦ hx hs.1), zero_mul]
        rfl
      rw [hz0, mul_zero]

end OTSelector.Reconstruction
