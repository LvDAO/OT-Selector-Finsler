import OTSelector.Probability.CavitySemidiscreteCycleGain

/-!
# Canonical source-block witnesses for fractional cycle violations

The smaller of the two actual block masses is removed by proportional restriction.
This constructs an admissible equal-mass exchange directly from the original plan,
so the witness estimate requires no supplied reassignment or mass-balance hypothesis.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S]

/-- Scale an actual source-block restriction down to the specified mass. -/
def sourceBlockSubmass (μ : Measure S) (A : Set S) (f : S → ℝ) (w : ℝ) (s : S) : ℝ :=
  (w / ∫ x in A, f x ∂μ) * A.indicator f s

/-- Any mass between zero and the actual block mass has an integrable subdensity bounded
by the original density, with exactly the requested integral. -/
theorem sourceBlockSubmass_properties
    (μ : Measure S) (A : Set S) (hA : MeasurableSet A)
    (f : S → ℝ) (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f)
    (w : ℝ) (hw0 : 0 ≤ w) (hw : w ≤ ∫ x in A, f x ∂μ) :
    Integrable (sourceBlockSubmass μ A f w) μ ∧
      (0 ≤ᵐ[μ] sourceBlockSubmass μ A f w) ∧
      (sourceBlockSubmass μ A f w ≤ᵐ[μ] f) ∧
      (∫ s, sourceBlockSubmass μ A f w s ∂μ) = w := by
  classical
  have hmass0 : 0 ≤ ∫ x in A, f x ∂μ := hw0.trans hw
  have hratio0 : 0 ≤ w / ∫ x in A, f x ∂μ := div_nonneg hw0 hmass0
  have hratio1 : w / (∫ x in A, f x ∂μ) ≤ 1 := by
    by_cases hz : (∫ x in A, f x ∂μ) = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hmass0 (Ne.symm hz))).mpr hw
  refine ⟨(hf.indicator hA).const_mul _, ?_, ?_, ?_⟩
  · filter_upwards [hf0] with s hs
    change 0 ≤ sourceBlockSubmass μ A f w s
    change 0 ≤ f s at hs
    exact mul_nonneg hratio0 (by simpa only [Set.indicator_apply] using
      (show 0 ≤ if s ∈ A then f s else 0 by split_ifs; exact hs; exact le_rfl))
  · filter_upwards [hf0] with s hs
    change 0 ≤ f s at hs
    by_cases hsa : s ∈ A
    · simp only [sourceBlockSubmass, indicator_of_mem hsa]
      exact (mul_le_mul_of_nonneg_right hratio1 hs).trans_eq (one_mul _)
    · simpa [sourceBlockSubmass, hsa] using hs
  · simp only [sourceBlockSubmass, integral_const_mul, integral_indicator hA]
    by_cases hz : (∫ x in A, f x ∂μ) = 0
    · have hwz : w = 0 := le_antisymm (hz ▸ hw) hw0
      simp [hz, hwz]
    · exact div_mul_cancel₀ w hz

/-- Positive removed density comes from the original source block. -/
theorem sourceBlockSubmass_pos_mem (μ : Measure S) (A : Set S) (f : S → ℝ)
    (w : ℝ) {s : S} (h : 0 < sourceBlockSubmass μ A f w s) : s ∈ A := by
  by_contra hs
  simp [sourceBlockSubmass, hs] at h

/-- A strict two-cycle certificate constructs a genuine local modification, whose gain
is at least the certificate gap times the smaller of the original block masses. -/
theorem exists_semidiscrete_cycle_block_exchange
    {m : ℕ} (μ : Measure S) [SFinite μ]
    (p : Fin (m + 1) → ℝ) (a c : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (j l : Fin (m + 1)) (hjl : j ≠ l)
    (A B : Set S) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ε : ℝ) (hgap : ∀ s ∈ A, ∀ t ∈ B,
      ε ≤ c s j + c t l - c s l - c t j) :
    ∃ b : S → Fin (m + 1) → ℝ, IsSemidiscreteAllocation μ p b ∧
      (∀ s, s ∉ A ∪ B → b s = a s) ∧
      ε * min (∫ s in A, a s j ∂μ) (∫ s in B, a s l ∂μ) ≤
        semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c b := by
  let w := min (∫ s in A, a s j ∂μ) (∫ s in B, a s l ∂μ)
  have hj0 : 0 ≤ᵐ[μ] fun s ↦ a s j := ha.nonneg.mono fun _ h ↦ h j
  have hl0 : 0 ≤ᵐ[μ] fun s ↦ a s l := ha.nonneg.mono fun _ h ↦ h l
  have hw0 : 0 ≤ w := le_min
    (integral_nonneg_of_ae (ae_restrict_of_ae hj0))
    (integral_nonneg_of_ae (ae_restrict_of_ae hl0))
  by_cases hwpos : 0 < w
  · let u := sourceBlockSubmass μ A (fun s ↦ a s j) w
    let v := sourceBlockSubmass μ B (fun s ↦ a s l) w
    obtain ⟨hu, hu0, hua, hmu⟩ := sourceBlockSubmass_properties μ A hA
      (fun s ↦ a s j) (ha.integrable j) hj0 w hw0 (min_le_left _ _)
    obtain ⟨hv, hv0, hva, hmv⟩ := sourceBlockSubmass_properties μ B hB
      (fun s ↦ a s l) (ha.integrable l) hl0 w hw0 (min_le_right _ _)
    have hmass : (∫ s, u s ∂μ) = ∫ s, v s ∂μ := hmu.trans hmv.symm
    have hpos : 0 < ∫ s, u s ∂μ := hmu.symm ▸ hwpos
    refine ⟨semidiscreteCycleExchange a j l u v,
      ha.cycleExchange j l hjl u v hu hv hu0 hv0 hua hva hmass, ?_, ?_⟩
    · intro s hs
      have hsA : s ∉ A := fun h ↦ hs (Or.inl h)
      have hsB : s ∉ B := fun h ↦ hs (Or.inr h)
      have hus : u s = 0 := by simp [u, sourceBlockSubmass, hsA]
      have hvs : v s = 0 := by simp [v, sourceBlockSubmass, hsB]
      funext k
      simp [semidiscreteCycleExchange, hus, hvs]
    · rw [semidiscreteCycleExchange_cost_gain μ p a c ha hc j l u v hu hv hu0 hv0 hua hva]
      have hd : Integrable (fun s ↦ c s j - c s l) μ := (hc j).sub (hc l)
      have h := weighted_cost_difference_gap μ u v (fun s ↦ c s j - c s l) ε hu hv
        (ha.integrable_suballocation_mul j u hu hu0 hua _ hd)
        (ha.integrable_suballocation_mul l v hv hv0 hva _ hd) hu0 hv0 hmass hpos
        (Eventually.of_forall fun z huz hvz ↦ by
          have h := hgap z.1 (sourceBlockSubmass_pos_mem μ A _ w huz)
            z.2 (sourceBlockSubmass_pos_mem μ B _ w hvz)
          linarith only [h])
      rwa [hmu] at h
  · have hwz : w = 0 := le_antisymm (le_of_not_gt hwpos) hw0
    refine ⟨a, ha, fun _ _ ↦ rfl, ?_⟩
    change ε * w ≤ _
    rw [hwz, mul_zero, sub_self]

/-- A strict two-cycle certificate bounds the minimum of the two original block masses
by the actual optimality excess. The equal-mass exchange is constructed internally. -/
theorem semidiscrete_cycle_block_mass_le_excess
    {m : ℕ} (μ : Measure S) [SFinite μ]
    (p : Fin (m + 1) → ℝ) (a a₀ c : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (j l : Fin (m + 1)) (hjl : j ≠ l)
    (A B : Set S) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ε : ℝ) (hgap : ∀ s ∈ A, ∀ t ∈ B,
      ε ≤ c s j + c t l - c s l - c t j) :
    ε * min (∫ s in A, a s j ∂μ) (∫ s in B, a s l ∂μ) ≤
      semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀ := by
  obtain ⟨b, hb, _, hgain⟩ := exists_semidiscrete_cycle_block_exchange
    μ p a c ha hc j l hjl A B hA hB ε hgap
  exact hgain.trans (sub_le_sub_left (h₀.2 b hb) _)

end OTSelector.Probability
