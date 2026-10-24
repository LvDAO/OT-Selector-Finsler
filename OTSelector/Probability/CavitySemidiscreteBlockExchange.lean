import OTSelector.Probability.CavitySemidiscreteSourceGlue

/-!
# Fractional exchanges between complete target blocks

The two removed subplans have equal total mass. Their product-marginal crosses
replace them, preserving every source and target marginal. This allows local
cycle certificates to involve any finite target subsets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Replace equal-mass subplans by the two crossed source-target products. -/
def semidiscreteBlockExchange (μ : Measure S) (a U V : S → Fin (m + 1) → ℝ)
    (w : ℝ) (s : S) (k : Fin (m + 1)) : ℝ :=
  a s k - U s k - V s k +
    (∑ j, U s j) / w * (∫ x, V x k ∂μ) + (∑ j, V s j) / w * (∫ x, U x k ∂μ)

/-- The product-marginal exchange is a genuine feasible fractional allocation. -/
theorem IsSemidiscreteAllocation.blockExchange
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (U V : S → Fin (m + 1) → ℝ)
    (hUi : ∀ j, Integrable (fun s ↦ U s j) μ)
    (hVi : ∀ j, Integrable (fun s ↦ V s j) μ)
    (hU0 : ∀ᵐ s ∂μ, ∀ j, 0 ≤ U s j) (hV0 : ∀ᵐ s ∂μ, ∀ j, 0 ≤ V s j)
    (hUV : ∀ᵐ s ∂μ, ∀ j, U s j + V s j ≤ a s j)
    (w : ℝ) (hw : 0 < w)
    (hUm : (∑ j, ∫ s, U s j ∂μ) = w) (hVm : (∑ j, ∫ s, V s j ∂μ) = w) :
    IsSemidiscreteAllocation μ p (semidiscreteBlockExchange μ a U V w) := by
  have hsumU := integrable_finsetSum Finset.univ (fun j _ ↦ hUi j)
  have hsumV := integrable_finsetSum Finset.univ (fun j _ ↦ hVi j)
  have hUint j : 0 ≤ ∫ s, U s j ∂μ := integral_nonneg_of_ae (hU0.mono fun _ h ↦ h j)
  have hVint j : 0 ≤ ∫ s, V s j ∂μ := integral_nonneg_of_ae (hV0.mono fun _ h ↦ h j)
  have hsumUm : (∫ s, ∑ j, U s j ∂μ) = w :=
    (integral_finsetSum _ (fun j _ ↦ hUi j)).trans hUm
  have hsumVm : (∫ s, ∑ j, V s j ∂μ) = w :=
    (integral_finsetSum _ (fun j _ ↦ hVi j)).trans hVm
  have hcrossU j : Integrable (fun s ↦ (∑ k, U s k) / w * (∫ x, V x j ∂μ)) μ :=
    (hsumU.div_const w).mul_const _
  have hcrossV j : Integrable (fun s ↦ (∑ k, V s k) / w * (∫ x, U x j ∂μ)) μ :=
    (hsumV.div_const w).mul_const _
  have hrem j : Integrable (fun s ↦ a s j - U s j - V s j) μ :=
    ((ha.integrable j).sub (hUi j)).sub (hVi j)
  have hremU j : Integrable (fun s ↦ a s j - U s j) μ :=
    (ha.integrable j).sub (hUi j)
  have hfirst j : Integrable (fun s ↦ a s j - U s j - V s j +
      (∑ k, U s k) / w * (∫ x, V x j ∂μ)) μ := (hrem j).add (hcrossU j)
  refine ⟨fun j ↦ (hfirst j).add (hcrossV j), ?_, ?_, ?_⟩
  · filter_upwards [hU0, hV0, hUV] with s hUs hVs hUVs
    intro j
    have hrem0 : 0 ≤ a s j - U s j - V s j := by linarith only [hUVs j]
    exact add_nonneg (add_nonneg hrem0
      (mul_nonneg (div_nonneg (Finset.sum_nonneg fun k _ ↦ hUs k) hw.le) (hVint j)))
      (mul_nonneg (div_nonneg (Finset.sum_nonneg fun k _ ↦ hVs k) hw.le) (hUint j))
  · filter_upwards [ha.sum_one] with s hs
    simp only [semidiscreteBlockExchange, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hUm, hVm, hs]
    rw [div_mul_cancel₀ _ hw.ne', div_mul_cancel₀ _ hw.ne']
    ring
  · intro j
    change (∫ s, (a s j - U s j - V s j) +
      (∑ k, U s k) / w * (∫ x, V x j ∂μ) +
      (∑ k, V s k) / w * (∫ x, U x j ∂μ) ∂μ) = p j
    rw [integral_add (hfirst j) (hcrossV j),
      integral_add (hrem j) (hcrossU j),
      integral_sub (hremU j) (hVi j),
      integral_sub (ha.integrable j) (hUi j),
      integral_mul_const, integral_mul_const, integral_div, integral_div,
      hsumUm, hsumVm, div_self hw.ne', one_mul, one_mul, ha.mass]
    ring

/-- The exact crossed-product objective, expressed entirely through original row integrals. -/
theorem semidiscreteBlockExchange_cost
    (μ : Measure S) (a U V c : S → Fin (m + 1) → ℝ) (w : ℝ)
    (hac : ∀ j, Integrable (fun s ↦ a s j * c s j) μ)
    (hUc : ∀ j k, Integrable (fun s ↦ U s j * c s k) μ)
    (hVc : ∀ j k, Integrable (fun s ↦ V s j * c s k) μ) :
    semidiscreteAllocationCost μ c (semidiscreteBlockExchange μ a U V w) =
      semidiscreteAllocationCost μ c a -
        (∑ j, ∫ s, U s j * c s j ∂μ) - (∑ j, ∫ s, V s j * c s j ∂μ) +
        (∑ k, (∑ j, ∫ s, U s j * c s k ∂μ) * (∫ s, V s k ∂μ)) / w +
        (∑ j, (∑ k, ∫ s, V s k * c s j ∂μ) * (∫ s, U s j ∂μ)) / w := by
  have hia := integrable_finsetSum Finset.univ (fun j _ ↦ hac j)
  have hiU := integrable_finsetSum Finset.univ (fun j _ ↦ hUc j j)
  have hiV := integrable_finsetSum Finset.univ (fun j _ ↦ hVc j j)
  have hiUV k : Integrable (fun s ↦
      (∑ j, U s j * c s k) * (∫ x, V x k ∂μ) / w) μ :=
    ((integrable_finsetSum _ (fun j _ ↦ hUc j k)).mul_const _).div_const _
  have hiVU k : Integrable (fun s ↦
      (∑ j, V s j * c s k) * (∫ x, U x k ∂μ) / w) μ :=
    ((integrable_finsetSum _ (fun j _ ↦ hVc j k)).mul_const _).div_const _
  have hrem : Integrable (fun s ↦
      (∑ j, a s j * c s j) - (∑ j, U s j * c s j) - (∑ j, V s j * c s j)) μ :=
    (hia.sub hiU).sub hiV
  have hfirst : Integrable (fun s ↦
      (∑ j, a s j * c s j) - (∑ j, U s j * c s j) - (∑ j, V s j * c s j) +
      ∑ k, (∑ j, U s j * c s k) * (∫ x, V x k ∂μ) / w) μ :=
    hrem.add (integrable_finsetSum _ (fun k _ ↦ hiUV k))
  have heq (s : S) : (∑ k, semidiscreteBlockExchange μ a U V w s k * c s k) =
      (∑ j, a s j * c s j) - (∑ j, U s j * c s j) - (∑ j, V s j * c s j) +
      (∑ k, (∑ j, U s j * c s k) * (∫ x, V x k ∂μ) / w) +
      (∑ k, (∑ j, V s j * c s k) * (∫ x, U x k ∂μ) / w) := by
    simp only [semidiscreteBlockExchange, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    congr 2
    · apply Finset.sum_congr rfl
      intro k _
      ring
    · funext k
      ring
  unfold semidiscreteAllocationCost
  simp_rw [heq]
  rw [integral_add hfirst (integrable_finsetSum _ (fun k _ ↦ hiVU k)),
    integral_add hrem (integrable_finsetSum _ (fun k _ ↦ hiUV k))]
  have hremU : Integrable (fun s ↦ (∑ j, a s j * c s j) - ∑ j, U s j * c s j) μ :=
    hia.sub hiU
  rw [integral_sub hremU hiV, integral_sub hia hiU,
    integral_finsetSum _ (fun j _ ↦ hUc j j),
    integral_finsetSum _ (fun j _ ↦ hVc j j),
    integral_finsetSum _ (fun k _ ↦ hiUV k),
    integral_finsetSum _ (fun k _ ↦ hiVU k)]
  simp only [integral_div, integral_mul_const,
    integral_finsetSum _ (fun j _ ↦ hUc j _),
    integral_finsetSum _ (fun j _ ↦ hVc j _), ← Finset.sum_div]

end OTSelector.Probability
