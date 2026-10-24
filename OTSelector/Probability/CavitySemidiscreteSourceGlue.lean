import OTSelector.Probability.CavitySemidiscreteCycleWitness

/-!
# Simultaneous local modifications of one semidiscrete plan

Feasible modifications with disjoint source supports can be applied simultaneously.
Target neighborhoods may overlap: every modification already preserves each target
mass. The objective improvement of the glued plan is the sum of the local improvements.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S I : Type*} [MeasurableSpace S] [Fintype I]

/-- Simultaneously add all local changes to the original allocation. -/
def semidiscreteSourceGlue (a : S → Fin (m + 1) → ℝ)
    (b : I → S → Fin (m + 1) → ℝ) (s : S) (j : Fin (m + 1)) : ℝ :=
  a s j + ∑ i, (b i s j - a s j)

omit [MeasurableSpace S] in
/-- On one source support, the glued allocation equals that actual local modification. -/
theorem semidiscreteSourceGlue_on
    (a : S → Fin (m + 1) → ℝ) (b : I → S → Fin (m + 1) → ℝ)
    (E : I → Set S) (hdisj : Pairwise (fun i k ↦ Disjoint (E i) (E k)))
    (hloc : ∀ i s, s ∉ E i → b i s = a s)
    (i : I) {s : S} (hs : s ∈ E i) : semidiscreteSourceGlue a b s = b i s := by
  classical
  funext j
  unfold semidiscreteSourceGlue
  rw [Finset.sum_eq_single i]
  · ring
  · intro k _ hki
    have hsk : s ∉ E k := fun h ↦ Set.disjoint_left.mp (hdisj (Ne.symm hki)) hs h
    rw [hloc k s hsk, sub_self]
  · simp

omit [MeasurableSpace S] in
/-- Outside all local supports the original allocation is retained exactly. -/
theorem semidiscreteSourceGlue_off
    (a : S → Fin (m + 1) → ℝ) (b : I → S → Fin (m + 1) → ℝ)
    (E : I → Set S) (hloc : ∀ i s, s ∉ E i → b i s = a s)
    {s : S} (hs : ∀ i, s ∉ E i) : semidiscreteSourceGlue a b s = a s := by
  funext j
  simp [semidiscreteSourceGlue, fun i ↦ hloc i s (hs i)]

/-- Disjoint-source gluing preserves all source and target marginals. It does not require
any disjointness of target supports of the local modifications. -/
theorem IsSemidiscreteAllocation.sourceGlue
    {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (b : I → S → Fin (m + 1) → ℝ) (hb : ∀ i, IsSemidiscreteAllocation μ p (b i))
    (E : I → Set S) (hdisj : Pairwise (fun i k ↦ Disjoint (E i) (E k)))
    (hloc : ∀ i s, s ∉ E i → b i s = a s) :
    IsSemidiscreteAllocation μ p (semidiscreteSourceGlue a b) := by
  classical
  have hdiff (i : I) (j : Fin (m + 1)) :
      Integrable (fun s ↦ b i s j - a s j) μ := (hb i).integrable j |>.sub (ha.integrable j)
  refine ⟨fun j ↦ (ha.integrable j).add (integrable_finsetSum _ (fun i _ ↦ hdiff i j)),
    ?_, ?_, ?_⟩
  · filter_upwards [ha.nonneg, ae_all_iff.mpr (fun i ↦ (hb i).nonneg)] with s has hbs
    by_cases hs : ∃ i, s ∈ E i
    · obtain ⟨i, hi⟩ := hs
      rw [semidiscreteSourceGlue_on a b E hdisj hloc i hi]
      exact hbs i
    · rw [semidiscreteSourceGlue_off a b E hloc (by simpa only [not_exists] using hs)]
      exact has
  · filter_upwards [ha.sum_one, ae_all_iff.mpr (fun i ↦ (hb i).sum_one)] with s has hbs
    simp only [semidiscreteSourceGlue, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, has, hbs, sub_self, Finset.sum_const_zero, add_zero]
  · intro j
    change (∫ s, a s j + ∑ i, (b i s j - a s j) ∂μ) = p j
    rw [integral_add (ha.integrable j) (integrable_finsetSum _ (fun i _ ↦ hdiff i j)),
      integral_finsetSum _ (fun i _ ↦ hdiff i j), ha.mass]
    simp only [integral_sub ((hb _).integrable j) (ha.integrable j),
      (hb _).mass, ha.mass, sub_self, Finset.sum_const_zero, add_zero]

/-- The objective of the actual simultaneous modification is the sum of local changes. -/
theorem semidiscreteSourceGlue_cost
    (μ : Measure S) (p : Fin (m + 1) → ℝ)
    (a : S → Fin (m + 1) → ℝ) (b : I → S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) (hb : ∀ i, IsSemidiscreteAllocation μ p (b i))
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ) :
    semidiscreteAllocationCost μ c (semidiscreteSourceGlue a b) =
      semidiscreteAllocationCost μ c a +
        ∑ i, (semidiscreteAllocationCost μ c (b i) - semidiscreteAllocationCost μ c a) := by
  have hia := integrable_finsetSum Finset.univ (fun j _ ↦ ha.integrable_mul c hc j)
  have hib i := integrable_finsetSum Finset.univ (fun j _ ↦ (hb i).integrable_mul c hc j)
  have hid i : Integrable (fun s ↦
      (∑ j, b i s j * c s j) - ∑ j, a s j * c s j) μ := (hib i).sub hia
  have heq (s : S) : (∑ j, semidiscreteSourceGlue a b s j * c s j) =
      (∑ j, a s j * c s j) + ∑ i, ((∑ j, b i s j * c s j) - ∑ j, a s j * c s j) := by
    simp only [semidiscreteSourceGlue, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, sub_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
  simp only [semidiscreteAllocationCost, heq]
  rw [integral_add hia (integrable_finsetSum _ (fun i _ ↦ hid i)),
    integral_finsetSum _ (fun i _ ↦ hid i)]
  simp only [integral_sub (hib _) hia]

/-- All local improvements on disjoint source supports fit within the original plan's
excess over the optimum. This is the finite packing inequality before root averaging. -/
theorem semidiscrete_disjoint_improvements_le_excess
    (μ : Measure S) (p : Fin (m + 1) → ℝ)
    (a a₀ : S → Fin (m + 1) → ℝ) (b : I → S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a) (hb : ∀ i, IsSemidiscreteAllocation μ p (b i))
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (E : I → Set S) (hdisj : Pairwise (fun i k ↦ Disjoint (E i) (E k)))
    (hloc : ∀ i s, s ∉ E i → b i s = a s) :
    (∑ i, (semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c (b i))) ≤
      semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀ := by
  have hmin := h₀.2 _ (ha.sourceGlue b hb E hdisj hloc)
  rw [semidiscreteSourceGlue_cost μ p a b ha hb c hc] at hmin
  have hneg : (∑ i, (semidiscreteAllocationCost μ c (b i) - semidiscreteAllocationCost μ c a)) =
      -(∑ i, (semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c (b i))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg] at hmin
  linarith only [hmin]

end OTSelector.Probability
