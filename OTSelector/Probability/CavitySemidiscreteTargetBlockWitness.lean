import OTSelector.Probability.CavitySemidiscreteBlockGain

/-!
# Actual finite target-block cycle witnesses

The original allocation determines each source-target block mass. Proportional
restrictions produce equal subplan masses, and their crossed marginals give a
competitor supported on the two original source blocks.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- The actual allocation mass of a source set and finite set of target labels. -/
def semidiscreteBlockMass (μ : Measure S) (a : S → Fin (m + 1) → ℝ)
    (A : Set S) (J : Finset (Fin (m + 1))) : ℝ := ∑ j ∈ J, ∫ s in A, a s j ∂μ

/-- Restrict the actual plan to a source-target block and scale down to the given mass. -/
def sourceTargetBlockSubmass (μ : Measure S) (a : S → Fin (m + 1) → ℝ)
    (A : Set S) (J : Finset (Fin (m + 1))) (w : ℝ) (s : S) (j : Fin (m + 1)) : ℝ :=
  if j ∈ J then (w / semidiscreteBlockMass μ a A J) * A.indicator (fun x ↦ a x j) s else 0

/-- The actual block mass is nonnegative. -/
theorem IsSemidiscreteAllocation.blockMass_nonneg
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (A : Set S) (J : Finset (Fin (m + 1))) :
    0 ≤ semidiscreteBlockMass μ a A J :=
  Finset.sum_nonneg fun j _ ↦ integral_nonneg_of_ae
    (ae_restrict_of_ae (ha.nonneg.mono fun _ h ↦ h j))

/-- Proportional restriction constructs all subplan coefficients and their exact mass. -/
theorem sourceTargetBlockSubmass_properties
    (μ : Measure S) (p : Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) (A : Set S) (hA : MeasurableSet A)
    (J : Finset (Fin (m + 1))) (w : ℝ) (hw0 : 0 ≤ w)
    (hw : w ≤ semidiscreteBlockMass μ a A J) :
    (∀ j, Integrable (fun s ↦ sourceTargetBlockSubmass μ a A J w s j) μ) ∧
    (∀ᵐ s ∂μ, ∀ j, 0 ≤ sourceTargetBlockSubmass μ a A J w s j) ∧
    (∀ᵐ s ∂μ, ∀ j, sourceTargetBlockSubmass μ a A J w s j ≤ a s j) ∧
    (∑ j, ∫ s, sourceTargetBlockSubmass μ a A J w s j ∂μ) = w := by
  classical
  have hm0 := ha.blockMass_nonneg A J
  have hr0 : 0 ≤ w / semidiscreteBlockMass μ a A J := div_nonneg hw0 hm0
  have hr1 : w / semidiscreteBlockMass μ a A J ≤ 1 := by
    by_cases hz : semidiscreteBlockMass μ a A J = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne hm0 (Ne.symm hz))).mpr hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ J
    · simpa only [sourceTargetBlockSubmass, hj, ite_true] using
        ((ha.integrable j).indicator hA).const_mul (w / semidiscreteBlockMass μ a A J)
    · simp only [sourceTargetBlockSubmass, hj, ite_false]
      exact integrable_zero S ℝ μ
  · filter_upwards [ha.nonneg] with s hs
    intro j
    unfold sourceTargetBlockSubmass
    split_ifs with hj
    · exact mul_nonneg hr0 (by by_cases hsa : s ∈ A <;> simp [hsa, hs j])
    · exact le_rfl
  · filter_upwards [ha.nonneg] with s hs
    intro j
    by_cases hj : j ∈ J
    · by_cases hsa : s ∈ A
      · simp only [sourceTargetBlockSubmass, hj, ite_true, indicator_of_mem hsa]
        exact (mul_le_mul_of_nonneg_right hr1 (hs j)).trans_eq (one_mul _)
      · simpa [sourceTargetBlockSubmass, hj, hsa] using hs j
    · simpa [sourceTargetBlockSubmass, hj] using hs j
  · have heq j : (∫ s, sourceTargetBlockSubmass μ a A J w s j ∂μ) =
        if j ∈ J then (w / semidiscreteBlockMass μ a A J) * (∫ s in A, a s j ∂μ) else 0 := by
      by_cases hj : j ∈ J
      · simp only [sourceTargetBlockSubmass, hj, ite_true]
        rw [integral_const_mul, integral_indicator hA]
      · simp [sourceTargetBlockSubmass, hj]
    simp_rw [heq]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.mul_sum]
    change w / semidiscreteBlockMass μ a A J * semidiscreteBlockMass μ a A J = w
    by_cases hz : semidiscreteBlockMass μ a A J = 0
    · have hwz : w = 0 := le_antisymm (hz ▸ hw) hw0
      simp [hz, hwz]
    · exact div_mul_cancel₀ w hz

/-- Positive removed mass is carried by the original source-target block. -/
theorem sourceTargetBlockSubmass_pos_mem
    (μ : Measure S) (a : S → Fin (m + 1) → ℝ) (A : Set S)
    (J : Finset (Fin (m + 1))) (w : ℝ) {s : S} {j : Fin (m + 1)}
    (h : 0 < sourceTargetBlockSubmass μ a A J w s j) : s ∈ A ∧ j ∈ J := by
  constructor
  · by_contra hs
    simp [sourceTargetBlockSubmass, hs] at h
  · by_contra hj
    simp [sourceTargetBlockSubmass, hj] at h

/-- The two block masses generate an actual feasible competitor with the full certificate
improvement, using their crossed marginals and retaining the plan elsewhere. -/
theorem exists_semidiscrete_target_block_exchange
    (μ : Measure S) [SFinite μ] (p : Fin (m + 1) → ℝ)
    (a c : S → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (A B : Set S) (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B)
    (J L : Finset (Fin (m + 1))) (ε : ℝ)
    (hgap : ∀ s ∈ A, ∀ t ∈ B, ∀ j ∈ J, ∀ k ∈ L,
      ε ≤ c s j + c t k - c s k - c t j) :
    ∃ b : S → Fin (m + 1) → ℝ, IsSemidiscreteAllocation μ p b ∧
      (∀ s, s ∉ A ∪ B → b s = a s) ∧
      ε * min (semidiscreteBlockMass μ a A J) (semidiscreteBlockMass μ a B L) ≤
        semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c b := by
  let w := min (semidiscreteBlockMass μ a A J) (semidiscreteBlockMass μ a B L)
  have hw0 : 0 ≤ w := le_min (ha.blockMass_nonneg A J) (ha.blockMass_nonneg B L)
  by_cases hw : 0 < w
  · let U := sourceTargetBlockSubmass μ a A J w
    let V := sourceTargetBlockSubmass μ a B L w
    obtain ⟨hUi, hU0, hUa, hUm⟩ := sourceTargetBlockSubmass_properties
      μ p a ha A hA J w hw0 (min_le_left _ _)
    obtain ⟨hVi, hV0, hVa, hVm⟩ := sourceTargetBlockSubmass_properties
      μ p a ha B hB L w hw0 (min_le_right _ _)
    have hUV : ∀ᵐ s ∂μ, ∀ j, U s j + V s j ≤ a s j := by
      filter_upwards [hUa, hVa] with s hUs hVs
      intro j
      by_cases hsA : s ∈ A
      · have hsB : s ∉ B := fun h ↦ Set.disjoint_left.mp hAB hsA h
        have hVz : V s j = 0 := by simp [V, sourceTargetBlockSubmass, hsB]
        simpa only [hVz, add_zero] using hUs j
      · have hUz : U s j = 0 := by simp [U, sourceTargetBlockSubmass, hsA]
        simpa only [hUz, zero_add] using hVs j
    refine ⟨semidiscreteBlockExchange μ a U V w,
      ha.blockExchange U V hUi hVi hU0 hV0 hUV w hw hUm hVm, ?_, ?_⟩
    · intro s hs
      have hsA : s ∉ A := fun h ↦ hs (Or.inl h)
      have hsB : s ∉ B := fun h ↦ hs (Or.inr h)
      have hUz : ∀ j, U s j = 0 := fun j ↦ by simp [U, sourceTargetBlockSubmass, hsA]
      have hVz : ∀ j, V s j = 0 := fun j ↦ by simp [V, sourceTargetBlockSubmass, hsB]
      funext j
      simp [semidiscreteBlockExchange, hUz, hVz]
    · exact semidiscreteBlockExchange_gain_ge μ p a U V c ha hc
        hUi hVi hU0 hV0 hUV w hw hUm hVm ε (Eventually.of_forall fun z j k hj hk ↦ by
          obtain ⟨hsA, hjJ⟩ := sourceTargetBlockSubmass_pos_mem μ a A J w hj
          obtain ⟨hsB, hkL⟩ := sourceTargetBlockSubmass_pos_mem μ a B L w hk
          exact hgap z.1 hsA z.2 hsB j hjJ k hkL)
  · have hwz : w = 0 := le_antisymm (le_of_not_gt hw) hw0
    refine ⟨a, ha, fun _ _ ↦ rfl, ?_⟩
    change ε * w ≤ _
    rw [hwz, mul_zero, sub_self]

end OTSelector.Probability
