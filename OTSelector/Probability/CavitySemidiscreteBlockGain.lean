import OTSelector.Probability.CavitySemidiscreteBlockExchange

/-!
# Quantitative gains of complete target-block exchanges

Strict cycle certificates are integrated against the actual two removed subplans.
Finite sums of their source-target product integrals identify the gain of the
crossed-marginal competitor, with no extra displacement or calibration hypothesis.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S]

/-- Integrating a source-pair cycle certificate against nonnegative subdensities. -/
theorem weighted_product_cycle_gap
    (μ : Measure S) [SFinite μ] (u v f g h k : S → ℝ) (ε : ℝ)
    (hu : Integrable u μ) (hv : Integrable v μ)
    (huf : Integrable (fun s ↦ u s * f s) μ)
    (huh : Integrable (fun s ↦ u s * h s) μ)
    (hvg : Integrable (fun s ↦ v s * g s) μ)
    (hvk : Integrable (fun s ↦ v s * k s) μ)
    (hu0 : 0 ≤ᵐ[μ] u) (hv0 : 0 ≤ᵐ[μ] v)
    (hgap : ∀ᵐ z : S × S ∂μ.prod μ,
      0 < u z.1 → 0 < v z.2 → ε ≤ f z.1 + g z.2 - h z.1 - k z.2) :
    ε * (∫ s, u s ∂μ) * (∫ s, v s ∂μ) ≤
      (∫ s, u s * f s ∂μ) * (∫ s, v s ∂μ) +
      (∫ s, u s ∂μ) * (∫ s, v s * g s ∂μ) -
      (∫ s, u s * h s ∂μ) * (∫ s, v s ∂μ) -
      (∫ s, u s ∂μ) * (∫ s, v s * k s ∂μ) := by
  have hi₁ := huf.mul_prod hv
  have hi₂ := hu.mul_prod hvg
  have hi₃ := huh.mul_prod hv
  have hi₄ := hu.mul_prod hvk
  have hiadd : Integrable (fun z : S × S ↦
      (u z.1 * f z.1) * v z.2 + u z.1 * (v z.2 * g z.2)) (μ.prod μ) := hi₁.add hi₂
  have hisub : Integrable (fun z : S × S ↦
      (u z.1 * f z.1) * v z.2 + u z.1 * (v z.2 * g z.2) -
        (u z.1 * h z.1) * v z.2) (μ.prod μ) := hiadd.sub hi₃
  have hright : Integrable (fun z : S × S ↦
      (u z.1 * f z.1) * v z.2 + u z.1 * (v z.2 * g z.2) -
        (u z.1 * h z.1) * v z.2 - u z.1 * (v z.2 * k z.2)) (μ.prod μ) := hisub.sub hi₄
  have hleft : Integrable (fun z : S × S ↦ ε * (u z.1 * v z.2)) (μ.prod μ) :=
    (hu.mul_prod hv).const_mul ε
  have hle : ∀ᵐ z : S × S ∂μ.prod μ,
      ε * (u z.1 * v z.2) ≤
      (u z.1 * f z.1) * v z.2 + u z.1 * (v z.2 * g z.2) -
        (u z.1 * h z.1) * v z.2 - u z.1 * (v z.2 * k z.2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hu0,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hv0, hgap] with z huz hvz hz
    change 0 ≤ u z.1 at huz
    change 0 ≤ v z.2 at hvz
    by_cases hu : 0 < u z.1
    · by_cases hv : 0 < v z.2
      · have h := mul_le_mul_of_nonneg_right (hz hu hv) (mul_nonneg huz hvz)
        nlinarith only [h]
      · have hvz0 : v z.2 = 0 := le_antisymm (le_of_not_gt hv) hvz
        simp [hvz0]
    · have huz0 : u z.1 = 0 := le_antisymm (le_of_not_gt hu) huz
      simp [huz0]
  have hint := integral_mono_ae hleft hright hle
  rw [integral_const_mul, integral_prod_mul,
    integral_sub hisub hi₄, integral_sub hiadd hi₃, integral_add hi₁ hi₂,
    integral_prod_mul (fun s ↦ u s * f s) v,
    integral_prod_mul u (fun s ↦ v s * g s),
    integral_prod_mul (fun s ↦ u s * h s) v,
    integral_prod_mul u (fun s ↦ v s * k s)] at hint
  simpa only [mul_assoc] using hint

/-- Finite target summation converts all pair certificates into the total crossed gain. -/
theorem finite_target_block_cycle_gap {J : Type*} [Fintype J]
    (u v : J → ℝ) (D E : J → J → ℝ) (ε w : ℝ)
    (hu : ∑ j, u j = w) (hv : ∑ j, v j = w)
    (hgap : ∀ j k, ε * u j * v k ≤
      D j j * v k + u j * E k k - D j k * v k - u j * E k j) :
    ε * w * w ≤ w * ((∑ j, D j j) + ∑ k, E k k) -
      (∑ k, (∑ j, D j k) * v k) - ∑ j, (∑ k, E k j) * u j := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) fun k _ ↦ hgap j k
  have hleft : (∑ j, ∑ k, ε * u j * v k) = ε * w * w := by
    simp only [← Finset.mul_sum, hv, ← Finset.sum_mul, ← Finset.mul_sum, hu]
  have hdiagD : (∑ j, ∑ k, D j j * v k) = w * ∑ j, D j j := by
    simp only [← Finset.mul_sum, hv, ← Finset.sum_mul, mul_comm]
  have hdiagE : (∑ j, ∑ k, u j * E k k) = w * ∑ k, E k k := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hu]
  have hcrossD : (∑ j, ∑ k, D j k * v k) = ∑ k, (∑ j, D j k) * v k := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  have hcrossE : (∑ j, ∑ k, u j * E k j) = ∑ j, (∑ k, E k j) * u j := by
    simp only [← Finset.mul_sum, mul_comm]
  rw [hleft] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  rw [hdiagD, hdiagE, hcrossD, hcrossE] at h
  linarith only [h]

/-- A strict certificate on the two removed subplans gives the actual crossed competitor
an objective improvement of at least the gap times their common mass. -/
theorem semidiscreteBlockExchange_gain_ge
    {m : ℕ} (μ : Measure S) [SFinite μ] (p : Fin (m + 1) → ℝ)
    (a U V c : S → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (hUi : ∀ j, Integrable (fun s ↦ U s j) μ)
    (hVi : ∀ j, Integrable (fun s ↦ V s j) μ)
    (hU0 : ∀ᵐ s ∂μ, ∀ j, 0 ≤ U s j) (hV0 : ∀ᵐ s ∂μ, ∀ j, 0 ≤ V s j)
    (hUV : ∀ᵐ s ∂μ, ∀ j, U s j + V s j ≤ a s j)
    (w : ℝ) (hw : 0 < w)
    (hUm : (∑ j, ∫ s, U s j ∂μ) = w) (hVm : (∑ j, ∫ s, V s j ∂μ) = w)
    (ε : ℝ) (hgap : ∀ᵐ z : S × S ∂μ.prod μ, ∀ j k,
      0 < U z.1 j → 0 < V z.2 k → ε ≤ c z.1 j + c z.2 k - c z.1 k - c z.2 j) :
    ε * w ≤ semidiscreteAllocationCost μ c a -
      semidiscreteAllocationCost μ c (semidiscreteBlockExchange μ a U V w) := by
  have hUa j : (fun s ↦ U s j) ≤ᵐ[μ] fun s ↦ a s j := by
    filter_upwards [hV0, hUV] with s hs ht
    linarith only [hs j, ht j]
  have hVa j : (fun s ↦ V s j) ≤ᵐ[μ] fun s ↦ a s j := by
    filter_upwards [hU0, hUV] with s hs ht
    linarith only [hs j, ht j]
  have hUc j k := ha.integrable_suballocation_mul j (fun s ↦ U s j) (hUi j)
    (hU0.mono fun _ h ↦ h j) (hUa j) (fun s ↦ c s k) (hc k)
  have hVc j k := ha.integrable_suballocation_mul j (fun s ↦ V s j) (hVi j)
    (hV0.mono fun _ h ↦ h j) (hVa j) (fun s ↦ c s k) (hc k)
  have hnum := finite_target_block_cycle_gap
    (fun j ↦ ∫ s, U s j ∂μ) (fun j ↦ ∫ s, V s j ∂μ)
    (fun j k ↦ ∫ s, U s j * c s k ∂μ) (fun j k ↦ ∫ s, V s j * c s k ∂μ)
    ε w hUm hVm (fun j k ↦ weighted_product_cycle_gap μ
      (fun s ↦ U s j) (fun s ↦ V s k) (fun s ↦ c s j) (fun s ↦ c s k)
      (fun s ↦ c s k) (fun s ↦ c s j) ε (hUi j) (hVi k)
      (hUc j j) (hUc j k) (hVc k k) (hVc k j)
      (hU0.mono fun _ h ↦ h j) (hV0.mono fun _ h ↦ h k)
      (hgap.mono fun _ h ↦ h j k))
  have hcost := semidiscreteBlockExchange_cost μ a U V c w
    (fun j ↦ ha.integrable_mul c hc j) hUc hVc
  have heq : w * ((∑ j, ∫ s, U s j * c s j ∂μ) + (∑ j, ∫ s, V s j * c s j ∂μ)) -
      (∑ k, (∑ j, ∫ s, U s j * c s k ∂μ) * (∫ s, V s k ∂μ)) -
      (∑ j, (∑ k, ∫ s, V s k * c s j ∂μ) * (∫ s, U s j ∂μ)) =
      w * (semidiscreteAllocationCost μ c a -
        semidiscreteAllocationCost μ c (semidiscreteBlockExchange μ a U V w)) := by
    rw [hcost]
    field_simp
    ring
  rw [heq] at hnum
  apply (mul_le_mul_iff_right₀ hw).mp
  nlinarith only [hnum]

end OTSelector.Probability
