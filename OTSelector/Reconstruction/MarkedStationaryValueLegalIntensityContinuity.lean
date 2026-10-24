import OTSelector.Reconstruction.MarkedStationaryValueLegalIntensityExpectation

/-! Actual legal pressure is continuous in the original Poisson intensity. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem FiniteScalarBins.legalMarkedPressure_diff_le_of_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (ρ σ : ℝ≥0) (hρσ : ρ ≤ σ) (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    |legalMarkedPressure q source target α β ρ kin g t -
      legalMarkedPressure q source target α β σ kin g t| ≤
      4 * ((D.count : ℝ) + 1) *
          ((σ : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G) * ((σ : ℝ) - ρ) +
        C * q * |(σ : ℝ) ^ (2 / (q : ℝ)) - (ρ : ℝ) ^ (2 / (q : ℝ))| *
          (σ : ℝ) := by
  have h := D.legalMarkedPressure_diff_le hgap q hs ht α β ρ (σ - ρ)
    hsource hsep hC hG hk hkb hg hgb t
  rw [add_tsub_cancel_of_le hρσ, NNReal.coe_sub hρσ] at h
  refine h.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_left (show (ρ : ℝ) ≤ σ by exact_mod_cast hρσ)
    (by positivity)

theorem FiniteScalarBins.abs_legalMarkedPressure_intensity_sub_le
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (ρ σ : ℝ≥0) (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    |legalMarkedPressure q source target α β ρ kin g t -
      legalMarkedPressure q source target α β σ kin g t| ≤
      4 * ((D.count : ℝ) + 1) *
          (((max ρ σ : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G) *
          |(ρ : ℝ) - σ| +
        C * q * |(ρ : ℝ) ^ (2 / (q : ℝ)) - (σ : ℝ) ^ (2 / (q : ℝ))| *
          ((max ρ σ : ℝ≥0) : ℝ) := by
  rcases le_total ρ σ with h | h
  · have hb := D.legalMarkedPressure_diff_le_of_le hgap q hs ht α β ρ σ h
      hsource hsep hC hG hk hkb hg hgb t
    have hr : (ρ : ℝ) ≤ σ := by exact_mod_cast h
    simpa only [max_eq_right h, abs_sub_comm ((σ : ℝ) ^ (2 / (q : ℝ))) ((ρ : ℝ) ^ (2 / (q : ℝ))),
      abs_of_nonpos (sub_nonpos.mpr hr), neg_sub] using hb
  · have hb := D.legalMarkedPressure_diff_le_of_le hgap q hs ht α β σ ρ h
      hsource hsep hC hG hk hkb hg hgb t
    have hr : (σ : ℝ) ≤ ρ := by exact_mod_cast h
    simpa only [max_eq_left h, abs_sub_comm
      (legalMarkedPressure q source target α β σ kin g t)
      (legalMarkedPressure q source target α β ρ kin g t),
      abs_of_nonneg (sub_nonneg.mpr hr)] using hb

theorem FiniteScalarBins.continuous_legalMarkedPressure
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Continuous (fun ρ : ℝ≥0 ↦ legalMarkedPressure q source target α β ρ kin g t) := by
  apply continuous_iff_continuousAt.mpr
  intro ρ
  let E : ℝ≥0 → ℝ := fun σ ↦
    4 * ((D.count : ℝ) + 1) *
      (((max σ ρ : ℝ≥0) : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G) * |(σ : ℝ) - ρ| +
      C * q * |(σ : ℝ) ^ (2 / (q : ℝ)) - (ρ : ℝ) ^ (2 / (q : ℝ))| *
        ((max σ ρ : ℝ≥0) : ℝ)
  have hp : Continuous (fun σ : ℝ≥0 ↦ (σ : ℝ) ^ (2 / (q : ℝ))) :=
    continuous_rpow_intensity q
  have hm : Continuous (fun σ : ℝ≥0 ↦ max σ ρ) := continuous_id.max continuous_const
  have hmr : Continuous (fun σ : ℝ≥0 ↦ ((max σ ρ : ℝ≥0) : ℝ)) :=
    continuous_subtype_val.comp hm
  have he : Continuous E :=
    ((continuous_const.mul (((hp.comp hm).mul continuous_const).add continuous_const)).mul
      ((continuous_subtype_val.sub continuous_const).abs)).add
      ((continuous_const.mul ((hp.sub continuous_const).abs)).mul hmr)
  have hzero : E ρ = 0 := by simp [E]
  have helim : Tendsto E (𝓝 ρ) (𝓝 0) := by simpa only [hzero] using he.tendsto ρ
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun σ ↦ dist_nonneg) (fun σ ↦ ?_) helim
  simpa only [Real.dist_eq] using
    D.abs_legalMarkedPressure_intensity_sub_le hgap q hs ht α β σ ρ
      hsource hsep hC hG hk hkb hg hgb t

theorem FiniteScalarBins.continuousOn_legalMarkedPressure_normalized
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    ContinuousOn (fun ρ : ℝ≥0 ↦ legalMarkedPressure q source target α β ρ kin g t / (ρ : ℝ))
      (Ioi 0) := by
  exact (D.continuous_legalMarkedPressure hgap q hs ht α β hsource hsep hC hG hk hkb hg hgb t).continuousOn.div
    continuous_subtype_val.continuousOn (fun ρ hρ ↦ ne_of_gt (by exact_mod_cast hρ))

theorem FiniteScalarBins.continuousOn_legalMarkedScalePressure
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    ContinuousOn (fun R : ℝ ↦ legalMarkedScalePressure q source target α β kin g R t) (Ioi 0) := by
  have hP := D.continuous_legalMarkedPressure hgap q hs ht α β hsource hsep hC hG hk hkb hg hgb t
  have hnum := hP.comp (continuous_real_toNNReal.comp (continuous_id.pow q))
  have hquot : ContinuousOn (fun R : ℝ ↦
      legalMarkedPressure q source target α β (Real.toNNReal (R ^ q)) kin g t / R ^ q) (Ioi 0) :=
    hnum.continuousOn.div (continuous_id.pow q).continuousOn
      (fun R hR ↦ pow_ne_zero q (ne_of_gt hR))
  apply hquot.congr
  intro R hR
  have hR0 : 0 < R := hR
  simp only [legalMarkedScalePressure, if_pos hR0]

theorem FiniteScalarBins.continuous_legalMarkedPressure_of_forward
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G) (t : ℝ) :
    Continuous (fun ρ : ℝ≥0 ↦ legalMarkedPressure q source target α β ρ kin g t) := by
  have h := D.continuous_legalMarkedPressure hgap q hs ht α β hsource hsep hC hG
    (measurable_forwardKinetic q hs ht hk) (abs_forwardKinetic_le q _ _ hC hkb)
    (measurable_forwardProbe hs ht hg) (abs_forwardProbe_le _ _ hG hgb) t
  have heq : (fun ρ : ℝ≥0 ↦ legalMarkedPressure q source target α β ρ
      (forwardKinetic q source target kin) (forwardProbe source target g) t) =
      (fun ρ : ℝ≥0 ↦ legalMarkedPressure q source target α β ρ kin g t) := by
    funext ρ
    unfold legalMarkedPressure
    exact integral_congr_ae (.of_forall (legalMarkedTilted_forward q source target ρ kin g t))
  rw [heq] at h
  exact h

end OTSelector.Reconstruction
