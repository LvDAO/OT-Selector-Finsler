import OTSelector.Reconstruction.OriginalPoissonHilbertInputMomentsActual
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Genuine dilation of the unchanged original input supplies arbitrary positive intensity. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Expanding unit-intensity input locations by this factor produces spatial intensity lambda. -/
def originalInputIntensityDilationScale (q : ℕ) (rate : ℝ) : ℝ := rate ^ (-(q : ℝ)⁻¹)

/-- The actual positive input dilation scale is nonzero. -/
theorem originalInputIntensityDilationScale_pos (q : ℕ) {rate : ℝ} (hrate : 0 < rate) :
    0 < originalInputIntensityDilationScale q rate := Real.rpow_pos_of_pos hrate _

/-- The true inverse Jacobian of the input dilation is exactly its desired spatial intensity. -/
theorem inv_pow_originalInputIntensityDilationScale {q : ℕ} (hq : 0 < q)
    {rate : ℝ} (hrate : 0 < rate) : (originalInputIntensityDilationScale q rate ^ q)⁻¹ = rate := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hp : originalInputIntensityDilationScale q rate ^ q = rate⁻¹ := by
    rw [originalInputIntensityDilationScale, ← Real.rpow_natCast, ← Real.rpow_mul hrate.le,
      neg_mul, inv_mul_cancel₀ hq0, Real.rpow_neg_one]
  rw [hp, inv_inv]

/-- Dilation reads the same original marked physical input at its actual scaled location. -/
def originalInputIntensityDilation (q : ℕ) {rate : ℝ} (hrate : 0 < rate) :
    LegalMarkedPhysicalPoint q ≃ᵐ LegalMarkedPhysicalPoint q :=
  (Homeomorph.smul (Units.mk0 (originalInputIntensityDilationScale q rate)
    (originalInputIntensityDilationScale_pos q hrate).ne')).toMeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)

/-- The full original spatial-times-mark intensity has the actual inverse-Jacobian factor. -/
theorem map_originalInputIntensityDilation {q : ℕ} (hq : 0 < q)
    {rate : ℝ} (hrate : 0 < rate) (γ : Measure ℝ) [IsFiniteMeasure γ] :
    (volume.prod γ).map (originalInputIntensityDilation q hrate) =
      ENNReal.ofReal rate • ((volume : Measure (Fin q → ℝ)).prod γ) := by
  let a := originalInputIntensityDilationScale q rate
  change (volume.prod γ).map (Prod.map (fun x : Fin q → ℝ ↦ a • x) id) = _
  rw [← Measure.map_prod_map volume γ (measurable_const_smul a) measurable_id,
    Measure.map_id, Measure.map_addHaar_smul volume
      (originalInputIntensityDilationScale_pos q hrate).ne']
  simp only [Module.finrank_pi, Fintype.card_fin]
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg
    (originalInputIntensityDilationScale_pos q hrate).le q)),
    inv_pow_originalInputIntensityDilationScale hq hrate, Measure.prod_smul_left]

/-- Actual change of variables supplies the intensity factor for any Hilbert readout. -/
theorem integral_comp_originalInputIntensityDilation {q : ℕ} (hq : 0 < q)
    {rate : ℝ} (hrate : 0 < rate) (γ : Measure ℝ) [IsFiniteMeasure γ]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : LegalMarkedPhysicalPoint q → H) :
    (∫ p, F (originalInputIntensityDilation q hrate p) ∂volume.prod γ) =
      rate • (∫ p, F p ∂volume.prod γ) := by
  rw [← integral_map_equiv (originalInputIntensityDilation q hrate),
    map_originalInputIntensityDilation hq hrate, integral_smul_measure, ENNReal.toReal_ofReal hrate.le]

/-- Original full-input Poisson moments at a genuinely dilated spatial intensity, retaining
its original marks and unchanged matching scene. No moment or intensity identity is assumed. -/
theorem LegalWeightedStationaryPoissonMatching.centered_dilatedFullInput_hilbert_moments
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (P : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hq : 0 < q) {rate : ℝ} (hrate : 0 < rate)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {N : Type*} [Countable N] (b : HilbertBasis N ℝ H)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {F : LegalMarkedPhysicalPoint q → H} (hF : Measurable F)
    (hsupport : ∀ p, p.1 ∉ K → F p = 0) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ p, ‖F p‖ ≤ B) (c : Fin 2) :
    let γ := if c = 0 then α else β
    let m := rate • (∫ p, F p ∂(volume : Measure (Fin q → ℝ)).prod γ)
    let I := fun s : LegalMarkedOptimalInputScene q ↦
      ∫ p, F (originalInputIntensityDilation q hrate p) ∂legalInputColorMeasure q s.2 c
    (∀ᵐ s ∂(P.law : Measure (LegalMarkedOptimalInputScene q)),
      Integrable (F ∘ originalInputIntensityDilation q hrate) (legalInputColorMeasure q s.2 c)) ∧
    MemLp (fun s ↦ I s - m) 2 (P.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ s, I s ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) = m ∧
    (∫ s, ‖I s - m‖^2 ∂(P.law : Measure (LegalMarkedOptimalInputScene q))) =
      rate * (∫ p, ‖F p‖^2 ∂(volume : Measure (Fin q → ℝ)).prod γ) := by
  let a := originalInputIntensityDilationScale q rate
  let O : (Fin q → ℝ) ≃ₜ (Fin q → ℝ) :=
    Homeomorph.smul (Units.mk0 a (originalInputIntensityDilationScale_pos q hrate).ne')
  let D := originalInputIntensityDilation q hrate
  let G := F ∘ D
  have hs : ∀ p : LegalMarkedPhysicalPoint q, p.1 ∉ O.symm '' K → G p = 0 := by
    intro p hp
    apply hsupport (D p)
    intro hx
    exact hp ⟨O p.1, hx, O.symm_apply_apply p.1⟩
  have h := P.centered_fullInput_hilbert_moments b (hK.image O.symm.continuous)
    (hF.comp D.measurable) hs hB (fun p ↦ hbound (D p)) c
  dsimp only at h
  let γ : Measure ℝ := if c = 0 then α else β
  have : IsProbabilityMeasure γ := by
    by_cases hc : c = 0 <;> simp only [γ, hc, ↓reduceIte] <;> infer_instance
  have hm : (∫ p, G p ∂(volume : Measure (Fin q → ℝ)).prod (if c = 0 then α else β)) =
      rate • (∫ p, F p ∂(volume : Measure (Fin q → ℝ)).prod (if c = 0 then α else β)) :=
    integral_comp_originalInputIntensityDilation hq hrate γ F
  have hsq : (∫ p, ‖G p‖^2 ∂(volume : Measure (Fin q → ℝ)).prod (if c = 0 then α else β)) =
      rate * (∫ p, ‖F p‖^2 ∂(volume : Measure (Fin q → ℝ)).prod (if c = 0 then α else β)) :=
    integral_comp_originalInputIntensityDilation hq hrate γ (fun p ↦ ‖F p‖^2)
  rw [hm, hsq] at h
  exact h

end OTSelector.Reconstruction
