import OTSelector.Transport.Semidiscrete.OppositeOptima

/-!
# Actual fractional two-cycle exchanges

Equal amounts of source mass assigned to two different target labels may be swapped.
The construction preserves every source and target marginal and gives the exact
change in the original objective. It applies to every feasible fractional plan.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Exchange source suballocations `u` and `v` between the two target labels. -/
def semidiscreteCycleExchange (a : S → Fin (m + 1) → ℝ) (j l : Fin (m + 1))
    (u v : S → ℝ) (s : S) (k : Fin (m + 1)) : ℝ :=
  a s k + (if k = j then v s - u s else 0) + (if k = l then u s - v s else 0)

/-- Removing equal integrated source masses from two labels and swapping them preserves
all prescribed marginal masses, with no restrictions on the other target labels. -/
theorem IsSemidiscreteAllocation.cycleExchange
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (j l : Fin (m + 1)) (hjl : j ≠ l)
    (u v : S → ℝ) (hu : Integrable u μ) (hv : Integrable v μ)
    (hu0 : 0 ≤ᵐ[μ] u) (hv0 : 0 ≤ᵐ[μ] v)
    (hua : u ≤ᵐ[μ] fun s ↦ a s j) (hva : v ≤ᵐ[μ] fun s ↦ a s l)
    (hmass : (∫ s, u s ∂μ) = ∫ s, v s ∂μ) :
    IsSemidiscreteAllocation μ p (semidiscreteCycleExchange a j l u v) := by
  have hlj := Ne.symm hjl
  have huv : Integrable (fun s ↦ u s - v s) μ := hu.sub hv
  have hvu : Integrable (fun s ↦ v s - u s) μ := hv.sub hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hkj : k = j
    · simp only [semidiscreteCycleExchange, hkj, ite_true, hjl, ite_false, add_zero]
      exact (ha.integrable j).add hvu
    · by_cases hkl : k = l
      · simp only [semidiscreteCycleExchange, hkl, hlj, ite_false, ite_true, add_zero]
        exact (ha.integrable l).add huv
      · simpa [semidiscreteCycleExchange, hkj, hkl] using ha.integrable k
  · filter_upwards [ha.nonneg, hu0, hv0, hua, hva] with s hs hus hvs huas hvas
    change 0 ≤ u s at hus
    change 0 ≤ v s at hvs
    intro k
    by_cases hkj : k = j
    · simp only [semidiscreteCycleExchange, hkj, ite_true, hjl, ite_false, add_zero]
      linarith
    · by_cases hkl : k = l
      · simp only [semidiscreteCycleExchange, hkl, hlj, ite_false, ite_true, add_zero]
        linarith
      · simpa [semidiscreteCycleExchange, hkj, hkl] using hs k
  · filter_upwards [ha.sum_one] with s hs
    simp only [semidiscreteCycleExchange, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, hs]
    ring
  · intro k
    by_cases hkj : k = j
    · simp only [semidiscreteCycleExchange, hkj, ite_true, hjl, ite_false, add_zero]
      rw [integral_add (ha.integrable j) hvu, integral_sub hv hu,
        ha.mass, hmass, sub_self, add_zero]
    · by_cases hkl : k = l
      · simp only [semidiscreteCycleExchange, hkl, hlj, ite_false, ite_true, add_zero]
        rw [integral_add (ha.integrable l) huv, integral_sub hu hv,
          ha.mass, hmass, sub_self, add_zero]
      · simpa [semidiscreteCycleExchange, hkj, hkl] using ha.mass k

/-- A source suballocation remains bounded by one and can be integrated against every
original integrable edge cost. -/
theorem IsSemidiscreteAllocation.integrable_suballocation_mul
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (j : Fin (m + 1))
    (u : S → ℝ) (hu : Integrable u μ) (hu0 : 0 ≤ᵐ[μ] u)
    (hua : u ≤ᵐ[μ] fun s ↦ a s j) (f : S → ℝ) (hf : Integrable f μ) :
    Integrable (fun s ↦ u s * f s) μ := by
  apply hf.bdd_mul hu.aestronglyMeasurable
  filter_upwards [hu0, hua, ha.ae_le_one] with s hs hsa ha1
  simpa only [Real.norm_eq_abs, abs_of_nonneg hs] using hsa.trans (ha1 j)

/-- The exchange gain is exactly the difference between the two weighted cost-difference
integrals. This identity concerns the original objective, without a calibration assumption. -/
theorem semidiscreteCycleExchange_cost_gain
    (μ : Measure S) (p : Fin (m + 1) → ℝ) (a c : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (j l : Fin (m + 1)) (u v : S → ℝ) (hu : Integrable u μ) (hv : Integrable v μ)
    (hu0 : 0 ≤ᵐ[μ] u) (hv0 : 0 ≤ᵐ[μ] v)
    (hua : u ≤ᵐ[μ] fun s ↦ a s j) (hva : v ≤ᵐ[μ] fun s ↦ a s l) :
    semidiscreteAllocationCost μ c a -
      semidiscreteAllocationCost μ c (semidiscreteCycleExchange a j l u v) =
        (∫ s, u s * (c s j - c s l) ∂μ) - ∫ s, v s * (c s j - c s l) ∂μ := by
  have hid : Integrable (fun s ↦ c s j - c s l) μ := (hc j).sub (hc l)
  have hiu := ha.integrable_suballocation_mul j u hu hu0 hua _ hid
  have hiv := ha.integrable_suballocation_mul l v hv hv0 hva _ hid
  have hia := integrable_finsetSum Finset.univ (fun k _ ↦ ha.integrable_mul c hc k)
  have hidiff : Integrable (fun s ↦ u s * (c s j - c s l) -
      v s * (c s j - c s l)) μ := hiu.sub hiv
  have heq (s : S) :
      (∑ k, semidiscreteCycleExchange a j l u v s k * c s k) =
        (∑ k, a s k * c s k) - (u s * (c s j - c s l) - v s * (c s j - c s l)) := by
    simp only [semidiscreteCycleExchange, add_mul, Finset.sum_add_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  simp only [semidiscreteAllocationCost, heq]
  rw [integral_sub hia hidiff, integral_sub hiu hiv]
  ring

/-- Every feasible exchange gain is bounded by the original plan's excess above the
actual optimum. The witness is the explicit exchanged plan. -/
theorem semidiscreteCycleExchange_gain_le_excess
    (μ : Measure S) (p : Fin (m + 1) → ℝ) (a a₀ c : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (j l : Fin (m + 1)) (hjl : j ≠ l)
    (u v : S → ℝ) (hu : Integrable u μ) (hv : Integrable v μ)
    (hu0 : 0 ≤ᵐ[μ] u) (hv0 : 0 ≤ᵐ[μ] v)
    (hua : u ≤ᵐ[μ] fun s ↦ a s j) (hva : v ≤ᵐ[μ] fun s ↦ a s l)
    (hmass : (∫ s, u s ∂μ) = ∫ s, v s ∂μ) :
    (∫ s, u s * (c s j - c s l) ∂μ) - (∫ s, v s * (c s j - c s l) ∂μ) ≤
      semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀ := by
  have hfeas := ha.cycleExchange j l hjl u v hu hv hu0 hv0 hua hva hmass
  have hmin := h₀.2 _ hfeas
  rw [← semidiscreteCycleExchange_cost_gain μ p a c ha hc j l u v hu hv hu0 hv0 hua hva]
  exact sub_le_sub_left hmin _

end OTSelector.Probability
