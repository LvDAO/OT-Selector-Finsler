import OTSelector.Reconstruction.MarkedStationaryValueLegalAllowedEnergyExtension
import OTSelector.Reconstruction.MarkedStationaryValueLegalShiftedEnergyFinite

/-!
# Actual legal support identifies the continuous shifted-energy test

Original source/target carrying and actual forward legality place every retained
edge in the real coefficient carrier. The continuous extension consequently
has exactly the original signed-energy expectation on these actual plans.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Original full clock supports and true legal edges put the actual normalized
optimal plan on its real coefficient carrier, even when clocks interleave. -/
theorem ae_clockPair_mem_legalMarkedNormalizedOptimalPlan_of_forward
    (q : ℕ) (L : ℝ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)),
      ∀ᵐ e ∂legalMarkedNormalizedOptimalPlan q L kin g t ω, (e.1.2, e.2.2) ∈ K := by
  have hαae : ∀ᵐ a ∂α, a ∈ A := ae_iff.mpr hα
  have hβae : ∀ᵐ b ∂β, b ∈ B := ae_iff.mpr hβ
  have hpair : ∀ᵐ w ∂α.prod β, w ∈ A ×ˢ B :=
    (ae_fst_of_ae hαae).and (ae_snd_of_ae hβae)
  filter_upwards [ae_clockPair_mem_legalMarkedOptimalPlan q L (L ^ q) kin g t α β
    (Real.toNNReal (L ^ q)) (hA.prod hB) hpair] with ω hω
  have hclock : ∀ᵐ e ∂legalMarkedNormalizedOptimalPlan q L kin g t ω,
      (e.1.2, e.2.2) ∈ A ×ˢ B := Measure.ae_smul_measure hω _
  have hforward : ∀ᵐ e ∂legalMarkedNormalizedOptimalPlan q L kin g t ω, e.1.2 < e.2.2 :=
    Measure.ae_smul_measure (ae_forward_legalMarkedOptimalPlan q L (L ^ q) kin g t ω) _
  filter_upwards [hclock, hforward] with e he hf
  exact hlegal e.1.2 he.1 e.2.2 he.2 hf

/-- The actual continuous weak-energy test is paid by exactly the actual
signed legal pressure plus its single nonnegative shift. Illegal entries and
arbitrary values of the extension are never evaluated by the retained plan. -/
theorem lintegral_legalMarkedNormalizedOptimalPlan_continuous_shifted_le
    (q : ℕ) (hq : 0 < q) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (F : C(PhysicalPairPalmMark (Fin q), ℝ))
    (hF : ∀ m : PhysicalPairPalmMark (Fin q), m.1 ∈ K →
      F m = kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G) :
    (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (F ((e.1.2, e.2.2), e.2.1 - e.1.1))
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ≤
      ENNReal.ofReal (legalMarkedScalePressure q id id α β kin g L t + |t| * G) := by
  apply le_trans ?_ (lintegral_legalMarkedNormalizedOptimalPlan_shifted_signed_le q hq hL
    α β hC hG hk hkn hkb hhom hg hgb t)
  apply le_of_eq
  apply lintegral_congr_ae
  filter_upwards [ae_clockPair_mem_legalMarkedNormalizedOptimalPlan_of_forward q L α β kin g t
    hA hB hα hβ hlegal] with ω hω
  apply lintegral_congr_ae
  filter_upwards [hω] with e he
  congr 1
  exact hF ((e.1.2, e.2.2), e.2.1 - e.1.1) he

end OTSelector.Reconstruction
