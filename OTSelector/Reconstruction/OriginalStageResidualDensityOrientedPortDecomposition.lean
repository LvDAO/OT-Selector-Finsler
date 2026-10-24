import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedFullInputs
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedReflectedEndpoints

/-! Shared actual-window algebra for reflected original ports and full-input response. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- A bounded original-point readout supported in a finite actual spatial window is L1. -/
theorem originalWindowSupportedReadout_integrable {q : ℕ}
    {σ : Measure (LegalMarkedPhysicalPoint q)} {W : Set (Fin q → ℝ)}
    (hW : MeasurableSet W) (hσ : σ {p | p.1 ∈ W} < ∞)
    {f : LegalMarkedPhysicalPoint q → ℝ} (hf : Measurable f)
    (B : ℝ) (hB : ∀ p, ‖f p‖ ≤ B) (hzero : ∀ p, p.1 ∉ W → f p = 0) : Integrable f σ := by
  have hWin : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ W} := hW.preimage measurable_fst
  let : IsFiniteMeasure (σ.restrict {p | p.1 ∈ W}) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hσ⟩
  have hi : Integrable f (σ.restrict {p | p.1 ∈ W}) :=
    Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)
  apply ((integrable_indicator_iff hWin).mpr hi).congr
  apply Eventually.of_forall
  intro p
  by_cases hp : p ∈ {p : LegalMarkedPhysicalPoint q | p.1 ∈ W}
  · exact Set.indicator_of_mem hp f
  · rw [Set.indicator_of_notMem hp, hzero p hp]

/-- The unchanged physical raw mollifier at an observation in the cube vanishes outside
its genuine expanded cube, in the same chosen orientation and without changing the scene. -/
theorem originalPhysicalRawKernel_eq_zero_off_expanded_cube {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 ≤ R)
    {z x : Fin q → ℝ} (hz : z ∈ originalCenteredPhysicalCubeRegion b (2 * R))
    (hx : x ∉ originalCenteredPhysicalCubeRegion b (2 * R + 2)) : originalEuclideanMollifier q (z - x) = 0 := by
  rw [← originalEuclideanMollifier_inverse_frame b]
  apply raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)
  by_contra! hn
  apply hx
  rw [mem_originalCenteredPhysicalCubeRegion_iff]
  have hhalf : (2 * R + 2) / 2 = R + 1 := by ring
  rw [hhalf]
  apply (mem_haarRootCube_iff_norm_le (by linarith : 0 ≤ R + 1) _).mpr
  have hz' : ‖(orthonormalPhysicalCubeMap b).symm z‖ ≤ R := by
    apply (mem_haarRootCube_iff_norm_le hR _).mp
    simpa only [show 2 * R / 2 = R by ring] using (mem_originalCenteredPhysicalCubeRegion_iff b (2 * R) z).mp hz
  rw [map_sub] at hn
  have htri := norm_sub_le ((orthonormalPhysicalCubeMap b).symm z)
    ((orthonormalPhysicalCubeMap b).symm z - (orthonormalPhysicalCubeMap b).symm x)
  rw [sub_sub_cancel] at htri
  linarith

/-- Actual retained + port window conservation, retained raw/reflected equality and the
proved full-input response identity give the exact genuine physical port decomposition. -/
theorem originalOrientedPortClassDensity_eq_omittedRaw_add_response {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    {C : Set ℝ} (hC : MeasurableSet C)
    (μ ρ τ π : Measure (LegalMarkedPhysicalPoint q)) [IsFiniteMeasure ρ] [IsFiniteMeasure π]
    (hfinite : μ (originalCenteredPhysicalCubeRegion b (2 * R + 2) ×ˢ (univ : Set ℝ)) < ∞)
    (hfull : ρ + τ = μ)
    (hwindow : ρ + π = μ.restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R)})
    {z : Fin q → ℝ} (hz : z ∈ originalCenteredPhysicalCubeRegion b (2 * R))
    (hret : (∫ p in {p | p.2 ∈ C}, originalCanonicalOrientedReflectedKernel b R z p.1 ∂ρ) =
      ∫ p in {p | p.2 ∈ C}, originalEuclideanMollifier q (z - p.1) ∂ρ) :
    originalOrientedStageReflectedClassDensity b R C π z =
      (∫ p in {p | p.2 ∈ C}, originalEuclideanMollifier q (z - p.1) ∂τ) +
        originalOrientedClassReflectedInputScalarField b (originalEuclideanMollifier q) (2 * R) C μ z := by
  have hC' : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ C} := hC.preimage measurable_snd
  have hmap : Measurable (fun p : LegalMarkedPhysicalPoint q ↦ (z, p.1)) := measurable_const.prodMk measurable_fst
  have hK : Measurable (fun p : LegalMarkedPhysicalPoint q ↦ originalCanonicalOrientedReflectedKernel b R z p.1) := by
    simpa only [Function.comp_def] using (measurable_originalCanonicalOrientedReflectedKernel b R).comp hmap
  have hiK (σ : Measure (LegalMarkedPhysicalPoint q)) [IsFiniteMeasure σ] :
      Integrable (fun p ↦ originalCanonicalOrientedReflectedKernel b R z p.1) (σ.restrict {p | p.2 ∈ C}) := by
    apply Integrable.of_bound hK.aestronglyMeasurable ((3 : ℝ) ^ q * originalEuclideanMollifierBound q)
    exact Eventually.of_forall (fun p ↦ by
      simpa only [Real.norm_eq_abs, originalCanonicalOrientedReflectedKernel, Fintype.card_fin] using
        abs_originalCubeReflectedKernel_le (abs_originalEuclideanMollifier_le q) R
          ((orthonormalPhysicalCubeMap b).symm z) ((orthonormalPhysicalCubeMap b).symm p.1))
  have hg : Measurable (fun p : LegalMarkedPhysicalPoint q ↦ originalEuclideanMollifier q (z - p.1)) :=
    (contDiff_originalEuclideanMollifier q).continuous.measurable.comp (measurable_const.sub measurable_fst)
  have houter : MeasurableSet (originalCenteredPhysicalCubeRegion b (2 * R + 2)) :=
    (isCompact_originalStagePhysicalCube b (2 * R + 2)).measurableSet
  have hfinite' : (μ.restrict {p | p.2 ∈ C}) {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R + 2)} < ∞ := by
    apply lt_of_le_of_lt (Measure.restrict_apply_le _ _) ?_
    have he : {p : LegalMarkedPhysicalPoint q | p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R + 2)} =
        originalCenteredPhysicalCubeRegion b (2 * R + 2) ×ˢ (univ : Set ℝ) := by ext p; simp
    rwa [he]
  have hgI := originalWindowSupportedReadout_integrable houter hfinite' hg (originalEuclideanMollifierBound q)
    (fun p ↦ by simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using abs_originalEuclideanMollifier_le q (z - p.1))
    (fun p hp ↦ originalPhysicalRawKernel_eq_zero_off_expanded_cube b (by linarith) hz hp)
  have hclassfull : ρ.restrict {p | p.2 ∈ C} + τ.restrict {p | p.2 ∈ C} = μ.restrict {p | p.2 ∈ C} := by
    rw [← Measure.restrict_add, hfull]
  have hρg : Integrable (fun p ↦ originalEuclideanMollifier q (z - p.1)) (ρ.restrict {p | p.2 ∈ C}) := hgI.mono_measure (by rw [← hclassfull]; exact Measure.le_add_right le_rfl)
  have hτg : Integrable (fun p ↦ originalEuclideanMollifier q (z - p.1)) (τ.restrict {p | p.2 ∈ C}) := hgI.mono_measure (by rw [← hclassfull]; exact Measure.le_add_left le_rfl)
  have hraw : (∫ p in {p | p.2 ∈ C}, originalEuclideanMollifier q (z - p.1) ∂μ) =
      (∫ p in {p | p.2 ∈ C}, originalEuclideanMollifier q (z - p.1) ∂ρ) +
        (∫ p in {p | p.2 ∈ C}, originalEuclideanMollifier q (z - p.1) ∂τ) := by
    rw [← hclassfull, integral_add_measure hρg hτg]
  have href := originalOrientedFullInputReflectedClassDensity_eq_raw_add_response b hR hC μ hfinite hz
  have hwindow' : originalOrientedStageReflectedClassDensity b R C
      (μ.restrict {p | p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R)}) z =
      (∫ p in {p | p.2 ∈ C}, originalCanonicalOrientedReflectedKernel b R z p.1 ∂ρ) +
        originalOrientedStageReflectedClassDensity b R C π z := by
    unfold originalOrientedStageReflectedClassDensity
    rw [← hwindow, Measure.restrict_add, integral_add_measure (hiK ρ) (hiK π)]
  rw [hwindow', hret, hraw] at href
  linarith

end OTSelector.Reconstruction
