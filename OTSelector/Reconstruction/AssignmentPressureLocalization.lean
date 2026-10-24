import OTSelector.Reconstruction.RelativeExpectedPressure

/-!
# A cost gap bounds exceptional mass on the entire optimal face

The actual tilted pressure controls the mass placed on any event where the base
cost has a positive lower bound. The estimate holds for every fractional optimum,
so it does not select among tied assignments.
-/

open Set MeasureTheory Matrix
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {n : ℕ}

/-- Event mass of a probability-normalized feasible assignment matrix. -/
def fractionalEdgeMass (Q : Set (Fin n × Fin n))
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ := by
  classical
  exact (∑ i, ∑ j, if (i, j) ∈ Q then W i j else 0) / n

/-- A feasible fractional objective preserves entrywise cost inequalities. -/
theorem fractionalAssignmentCost_mono_of_feasible
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W ∈ doublyStochastic ℝ (Fin n))
    {c d : Matrix (Fin n) (Fin n) ℝ} (h : ∀ i j, c i j ≤ d i j) :
    fractionalAssignmentCost c W ≤ fractionalAssignmentCost d W := by
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (h i j) (nonneg_of_mem_doublyStochastic hW)

/-- A constant edge cost contributes precisely sample size times that constant. -/
theorem fractionalAssignmentCost_const_of_feasible
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W ∈ doublyStochastic ℝ (Fin n)) (G : ℝ) :
    fractionalAssignmentCost (fun _ _ ↦ G) W = n * G := by
  simp only [fractionalAssignmentCost, ← Finset.sum_mul,
    sum_row_of_mem_doublyStochastic hW, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- Bounded probes control every feasible fractional readout. -/
theorem fractionalAssignmentCost_abs_le_of_feasible
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W ∈ doublyStochastic ℝ (Fin n))
    {g : Matrix (Fin n) (Fin n) ℝ} {G : ℝ} (hg : ∀ i j, |g i j| ≤ G) :
    |fractionalAssignmentCost g W| ≤ n * G := by
  apply abs_le.mpr
  constructor
  · have h := fractionalAssignmentCost_mono_of_feasible hW
      (fun i j ↦ (abs_le.mp (hg i j)).1)
    simpa only [fractionalAssignmentCost_const_of_feasible hW, mul_neg] using h
  · have h := fractionalAssignmentCost_mono_of_feasible hW
      (fun i j ↦ (abs_le.mp (hg i j)).2)
    simpa only [fractionalAssignmentCost_const_of_feasible hW] using h

/-- A base-cost lower bound on an event controls its mass for every feasible
fractional assignment, independent of optimality. -/
theorem fractionalEdgeMass_mul_gap_le_cost
    {W c : Matrix (Fin n) (Fin n) ℝ} (hW : W ∈ doublyStochastic ℝ (Fin n))
    (Q : Set (Fin n × Fin n)) {gap : ℝ}
    (hc : ∀ i j, 0 ≤ c i j) (hgap : ∀ i j, (i, j) ∈ Q → gap ≤ c i j) :
    gap * fractionalEdgeMass Q W ≤ fractionalAssignmentCost c W / n := by
  classical
  have hsum : gap * (∑ i, ∑ j, if (i, j) ∈ Q then W i j else 0) ≤
      fractionalAssignmentCost c W := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hq : (i, j) ∈ Q
    · simp only [hq, ite_true]
      exact (mul_le_mul_of_nonneg_right (hgap i j hq)
        (nonneg_of_mem_doublyStochastic hW)).trans_eq (mul_comm _ _)
    · simp only [hq, ite_false, mul_zero]
      exact mul_nonneg (nonneg_of_mem_doublyStochastic hW) (hc i j)
  simpa only [fractionalEdgeMass, mul_div_assoc] using
    div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

/-- The actual tilted pressure controls exceptional mass uniformly over its whole
fractional optimal face. A scaled geometric gap is inserted directly as `gap`. -/
theorem optimalFractionalEdgeMass_le_pressure (hn : 0 < n)
    (c g W : Matrix (Fin n) (Fin n) ℝ) (Q : Set (Fin n × Fin n))
    (t G gap : ℝ) (hgap : 0 < gap)
    (hW : OptimalFractionalAssignment (perturbedEdgeCost c g t) W)
    (hc : ∀ i j, 0 ≤ c i j) (hcost : ∀ i j, (i, j) ∈ Q → gap ≤ c i j)
    (hg : ∀ i j, |g i j| ≤ G) :
    fractionalEdgeMass Q W ≤ (perturbedAssignmentValue c g t / n + |t| * G) / gap := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he := perturbedAssignmentValue_eq_of_optimalFractional c g W t hW
  rw [fractionalAssignmentCost_perturbedEdgeCost] at he
  have hprobe := fractionalAssignmentCost_abs_le_of_feasible hW.1 hg
  have hp : |t * fractionalAssignmentCost g W| ≤ n * (|t| * G) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hprobe (abs_nonneg t)).trans_eq (by ring)
  have henergy : fractionalAssignmentCost c W ≤
      perturbedAssignmentValue c g t + n * (|t| * G) := by
    have hh := (abs_le.mp hp).1
    linarith
  have hdiv : fractionalAssignmentCost c W / n ≤
      perturbedAssignmentValue c g t / n + |t| * G := by
    simpa only [add_div, mul_div_cancel_left₀ _ hn'.ne'] using
      div_le_div_of_nonneg_right henergy hn'.le
  apply (le_div_iff₀ hgap).mpr
  rw [mul_comm]
  exact (fractionalEdgeMass_mul_gap_le_cost hW.1 Q hc hcost).trans hdiv

/-- Every event has mass between zero and one under a feasible empirical matrix. -/
theorem fractionalEdgeMass_mem_Icc (hn : 0 < n)
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W ∈ doublyStochastic ℝ (Fin n))
    (Q : Set (Fin n × Fin n)) : fractionalEdgeMass Q W ∈ Icc (0 : ℝ) 1 := by
  classical
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnon : 0 ≤ ∑ i, ∑ j, if (i, j) ∈ Q then W i j else 0 := by
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      by split_ifs
         · exact nonneg_of_mem_doublyStochastic hW
         · exact le_rfl
  have hle : (∑ i, ∑ j, if (i, j) ∈ Q then W i j else 0) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ i, ∑ j, W i j := Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
        split_ifs
        · exact le_rfl
        · exact nonneg_of_mem_doublyStochastic hW
      _ = _ := by simp only [sum_row_of_mem_doublyStochastic hW, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ⟨div_nonneg hnon hn'.le, (div_le_one hn').mpr hle⟩

/-- The event mass is measurable for any measurable fractional optimizer. -/
theorem measurable_fractionalEdgeMass {Ω : Type*} [MeasurableSpace Ω]
    (Q : Ω → Set (Fin n × Fin n)) (W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ i j, MeasurableSet {ξ | (i, j) ∈ Q ξ})
    (hW : ∀ i j, Measurable (fun ξ ↦ W ξ i j)) :
    Measurable (fun ξ ↦ fractionalEdgeMass (Q ξ) (W ξ)) := by
  classical
  exact (Finset.measurable_sum _ (fun i _ ↦ Finset.measurable_sum _ (fun j _ ↦
    Measurable.ite (hQ i j) (hW i j) measurable_const))).div_const n

/-- The actual expected tilted pressure bounds the exceptional mass of every
measurable optimal fractional matrix under the unchanged sample law. -/
theorem expected_optimalFractionalEdgeMass_le_pressure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hn : 0 < n) (c g W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (Q : Ω → Set (Fin n × Fin n)) (t G gap : ℝ) (hgap : 0 < gap)
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hW : ∀ i j, Measurable (fun ξ ↦ W ξ i j))
    (hQ : ∀ i j, MeasurableSet {ξ | (i, j) ∈ Q ξ})
    (hci : ∀ i j, Integrable (fun ξ ↦ c ξ i j) P)
    (hopt : ∀ᵐ ξ ∂P, OptimalFractionalAssignment (perturbedEdgeCost (c ξ) (g ξ) t) (W ξ))
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ c ξ i j)
    (hcost : ∀ᵐ ξ ∂P, ∀ i j, (i, j) ∈ Q ξ → gap ≤ c ξ i j)
    (hgb : ∀ᵐ ξ ∂P, ∀ i j, |g ξ i j| ≤ G) :
    Integrable (fun ξ ↦ fractionalEdgeMass (Q ξ) (W ξ)) P ∧
      (∫ ξ, fractionalEdgeMass (Q ξ) (W ξ) ∂P) ≤
        ((∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂P) + |t| * G) / gap := by
  have hmass : Integrable (fun ξ ↦ fractionalEdgeMass (Q ξ) (W ξ)) P := by
    apply (integrable_const (1 : ℝ)).mono'
      (measurable_fractionalEdgeMass Q W hQ hW).aestronglyMeasurable
    filter_upwards [hopt] with ξ hoptξ
    have hb := fractionalEdgeMass_mem_Icc hn hoptξ.1 (Q ξ)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  have hgi (i j : Fin n) : Integrable (fun ξ ↦ g ξ i j) P := by
    apply (integrable_const G).mono' (hg i j).aestronglyMeasurable
    filter_upwards [hgb] with ξ hgbξ
    exact hgbξ i j
  have hvalue : Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / n) P := by
    have hi := Probability.integrable_assignmentValue P
      (fun ξ ↦ perturbedEdgeCost (c ξ) (g ξ) t)
      (fun i j ↦ (hc i j).add ((hg i j).const_mul t))
      (fun i j ↦ (hci i j).add ((hgi i j).const_mul t))
    simpa only [perturbedAssignmentValue, perturbedEdgeCost_zero] using hi.div_const (n : ℝ)
  refine ⟨hmass, ?_⟩
  have hle := integral_mono_ae hmass ((hvalue.add (integrable_const (|t| * G))).div_const gap) (by
    filter_upwards [hopt, hcn, hcost, hgb] with ξ hoptξ hcnξ hcostξ hgbξ
    exact optimalFractionalEdgeMass_le_pressure hn (c ξ) (g ξ) (W ξ) (Q ξ)
      t G gap hgap hoptξ hcnξ hcostξ hgbξ)
  simpa [integral_div, integral_add hvalue (integrable_const (|t| * G))] using hle

end OTSelector.Reconstruction
