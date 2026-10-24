import OTSelector.Probability.CavitySemidiscreteCycleExchange

/-!
# Quantitative improvement from strict two-cycle violations

Integrating the strict source-pair cost gap gives an improvement proportional to
the exchanged mass. Since the exchanged plan preserves every marginal, any such
violation is bounded by the actual plan's excess above the semidiscrete optimum.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S]

/-- Equal positive source submasses separated by a pairwise cost-difference gap have
weighted-average separation at least that gap times their mass. -/
theorem weighted_cost_difference_gap
    (μ : Measure S) [SFinite μ] (u v d : S → ℝ) (ε : ℝ)
    (hu : Integrable u μ) (hv : Integrable v μ)
    (hud : Integrable (fun s ↦ u s * d s) μ)
    (hvd : Integrable (fun s ↦ v s * d s) μ)
    (hu0 : 0 ≤ᵐ[μ] u) (hv0 : 0 ≤ᵐ[μ] v)
    (hmass : (∫ s, u s ∂μ) = ∫ s, v s ∂μ)
    (hpos : 0 < ∫ s, u s ∂μ)
    (hgap : ∀ᵐ z : S × S ∂μ.prod μ,
      0 < u z.1 → 0 < v z.2 → ε ≤ d z.1 - d z.2) :
    ε * (∫ s, u s ∂μ) ≤ (∫ s, u s * d s ∂μ) - ∫ s, v s * d s ∂μ := by
  have hiuv := hu.mul_prod hv
  have hleft : Integrable (fun z : S × S ↦ ε * (u z.1 * v z.2)) (μ.prod μ) :=
    hiuv.const_mul ε
  have hir : Integrable (fun z : S × S ↦
      (u z.1 * d z.1) * v z.2 - u z.1 * (v z.2 * d z.2)) (μ.prod μ) :=
    (hud.mul_prod hv).sub (hu.mul_prod hvd)
  have hle : ∀ᵐ z : S × S ∂μ.prod μ,
      ε * (u z.1 * v z.2) ≤ (u z.1 * d z.1) * v z.2 - u z.1 * (v z.2 * d z.2) := by
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
  have h := integral_mono_ae hleft hir hle
  rw [integral_const_mul, integral_prod_mul,
    integral_sub (hud.mul_prod hv) (hu.mul_prod hvd),
    integral_prod_mul (fun s ↦ u s * d s) v,
    integral_prod_mul u (fun s ↦ v s * d s), ← hmass] at h
  nlinarith only [h, hpos]

/-- Strict two-cycle violations are quantitatively controlled by the actual optimality
excess. The proof constructs and evaluates the feasible fractional exchange. -/
theorem semidiscrete_strict_cycle_mass_le_excess
    {m : ℕ} (μ : Measure S) [SFinite μ]
    (p : Fin (m + 1) → ℝ) (a a₀ c : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (j l : Fin (m + 1)) (hjl : j ≠ l)
    (u v : S → ℝ) (hu : Integrable u μ) (hv : Integrable v μ)
    (hu0 : 0 ≤ᵐ[μ] u) (hv0 : 0 ≤ᵐ[μ] v)
    (hua : u ≤ᵐ[μ] fun s ↦ a s j) (hva : v ≤ᵐ[μ] fun s ↦ a s l)
    (hmass : (∫ s, u s ∂μ) = ∫ s, v s ∂μ) (hpos : 0 < ∫ s, u s ∂μ)
    (ε : ℝ) (hgap : ∀ᵐ z : S × S ∂μ.prod μ,
      0 < u z.1 → 0 < v z.2 → ε ≤ c z.1 j + c z.2 l - c z.1 l - c z.2 j) :
    ε * (∫ s, u s ∂μ) ≤
      semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀ := by
  have hd : Integrable (fun s ↦ c s j - c s l) μ := (hc j).sub (hc l)
  have h := weighted_cost_difference_gap μ u v (fun s ↦ c s j - c s l) ε hu hv
    (ha.integrable_suballocation_mul j u hu hu0 hua _ hd)
    (ha.integrable_suballocation_mul l v hv hv0 hva _ hd) hu0 hv0 hmass hpos
    (hgap.mono fun z hz hu hv ↦ by linarith only [hz hu hv])
  exact h.trans (semidiscreteCycleExchange_gain_le_excess
    μ p a a₀ c ha h₀ hc j l hjl u v hu hv hu0 hv0 hua hva hmass)

end OTSelector.Probability
