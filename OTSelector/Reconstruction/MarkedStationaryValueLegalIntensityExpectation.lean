import OTSelector.Reconstruction.MarkedStationaryValueLegalIntensityCoupling

/-! Original legal pressure stability in the Poisson intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Shared-prefix coupling gives an intensity modulus for the actual legal
pressure, including realizations with a positive legal matching deficiency. -/
theorem FiniteScalarBins.legalMarkedPressure_diff_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (ρ δ : ℝ≥0) (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    |legalMarkedPressure q source target α β ρ kin g t -
      legalMarkedPressure q source target α β (ρ + δ) kin g t| ≤
      4 * ((D.count : ℝ) + 1) *
          (((ρ + δ : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G) * (δ : ℝ) +
        C * q * |((ρ + δ : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) - (ρ : ℝ) ^ (2 / (q : ℝ))| *
          (ρ : ℝ) := by
  let P := markedPreCouple q A B α β ρ δ
  let V : MarkedPreCoupleSpace q A B → ℝ := fun z ↦
    legalMarkedTilted q source target ρ kin g t (preSmallCloud z)
  let W : MarkedPreCoupleSpace q A B → ℝ := fun z ↦
    legalMarkedTilted q source target (ρ + δ) kin g t (preLargeCloud z)
  let K := 2 * ((D.count : ℝ) + 1) *
    (((ρ + δ : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)
  let L := C * q * |((ρ + δ : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) - (ρ : ℝ) ^ (2 / (q : ℝ))|
  have hmapS : P.map (preSmallCloud (q := q)) = twoMarkedCloudLaw q A B α β ρ :=
    map_preSmallCloud q α β ρ δ
  have hmapL : P.map (preLargeCloud (q := q)) = twoMarkedCloudLaw q A B α β (ρ + δ) :=
    map_preLargeCloud q α β ρ δ
  have hVI : Integrable V P := by
    have h := integrable_legalMarkedTilted q hs ht α β ρ hC hG hk hkb hg hgb t
    rw [← hmapS] at h
    exact h.comp_measurable (measurable_preSmallCloud q)
  have hWI : Integrable W P := by
    have h := integrable_legalMarkedTilted q hs ht α β (ρ + δ) hC hG hk hkb hg hgb t
    rw [← hmapL] at h
    exact h.comp_measurable (measurable_preLargeCloud q)
  have hVS : (∫ z, V z ∂P) = legalMarkedPressure q source target α β ρ kin g t := by
    unfold legalMarkedPressure
    rw [← hmapS]
    exact (integral_map (measurable_preSmallCloud q).aemeasurable
      (measurable_legalMarkedTilted q hs ht hk hg ρ t).aestronglyMeasurable).symm
  have hWL : (∫ z, W z ∂P) = legalMarkedPressure q source target α β (ρ + δ) kin g t := by
    unfold legalMarkedPressure
    rw [← hmapL]
    exact (integral_map (measurable_preLargeCloud q).aemeasurable
      (measurable_legalMarkedTilted q hs ht hk hg (ρ + δ) t).aestronglyMeasurable).symm
  have hcarrier := (ae_all_mSourceMark q α β (ρ + δ) hsource).and
    (ae_all_mMarkPair q α β (ρ + δ) (P := fun a b ↦ gap ≤ |target b - source a|) hsep)
  rw [← hmapL] at hcarrier
  have hpre := ae_of_ae_map (measurable_preLargeCloud q).aemeasurable hcarrier
  have hAE : ∀ᵐ z ∂P, |W z - V z| ≤
      K * (pcExtraSource z : ℝ) + K * (pcExtraTarget z : ℝ) + L * (pcSourceCount z : ℝ) := by
    filter_upwards [hpre] with z hz
    have hdel := D.abs_legalMarkedTilted_preSmall_sub_preLarge hgap q source target
      (ρ + δ).coe_nonneg hC hG kin hkb g hgb t z hz.1 hz.2
    have hscale := abs_legalMarkedTilted_scale_sub_le q source target hC kin hkb g t
      (ρ + δ) ρ (preSmallCloud z)
    calc
      _ ≤ |legalMarkedTilted q source target (ρ + δ) kin g t (preLargeCloud z) -
          legalMarkedTilted q source target (ρ + δ) kin g t (preSmallCloud z)| +
        |legalMarkedTilted q source target (ρ + δ) kin g t (preSmallCloud z) -
          legalMarkedTilted q source target ρ kin g t (preSmallCloud z)| := abs_sub_le _ _ _
      _ ≤ ((pcExtraSource z : ℝ) + (pcExtraTarget z : ℝ)) * K +
          (pcSourceCount z : ℝ) * L := by
        rw [abs_sub_comm] at hdel
        exact add_le_add hdel hscale
      _ = _ := by ring
  have hES := integrable_pcExtraSource q A B α β ρ δ
  have hET := integrable_pcExtraTarget q A B α β ρ δ
  have hNS := integrable_pcSourceCount q A B α β ρ δ
  have hBI : Integrable (fun z ↦ K * (pcExtraSource z : ℝ) +
      K * (pcExtraTarget z : ℝ) + L * (pcSourceCount z : ℝ)) P :=
    ((hES.const_mul K).fun_add (hET.const_mul K)).fun_add (hNS.const_mul L)
  calc
    _ = |(∫ z, W z ∂P) - ∫ z, V z ∂P| := by rw [hVS, hWL, abs_sub_comm]
    _ = |∫ z, W z - V z ∂P| := by rw [integral_sub hWI hVI]
    _ ≤ ∫ z, |W z - V z| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ z, K * (pcExtraSource z : ℝ) + K * (pcExtraTarget z : ℝ) +
        L * (pcSourceCount z : ℝ) ∂P := integral_mono_ae (hWI.sub hVI).abs hBI hAE
    _ = K * (δ : ℝ) + K * (δ : ℝ) + L * (ρ : ℝ) := by
      rw [integral_add ((hES.const_mul K).fun_add (hET.const_mul K)) (hNS.const_mul L),
        integral_add (hES.const_mul K) (hET.const_mul K), integral_const_mul,
        integral_const_mul, integral_const_mul, integral_pcExtraSource, integral_pcExtraTarget,
        integral_pcSourceCount]
    _ = _ := by dsimp [K, L]; ring

end OTSelector.Reconstruction
