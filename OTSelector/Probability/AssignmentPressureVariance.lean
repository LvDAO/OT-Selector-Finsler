import OTSelector.Finite.AssignmentCoordinateStability
import OTSelector.Probability.BoundedDifferencesVariance
import OTSelector.Probability.CavitySemidiscretePressureSampling

/-!
# Concentration of the genuine bounded assignment value

The actual minimum divided by sample size has variance at most `16 B^2 / n`
when each edge cost is bounded by `B`. Coordinates are paired observations;
replacing a pair changes only one source row and one target column. The bound
transfers to any original probability space carrying independent paired samples.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace OTSelector.Probability

variable {S T Ω : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Ω]

/-- The actual assignment minimum, divided by the number of observations. -/
noncomputable def sampleAssignmentMean {n : ℕ} (c : S → T → ℝ) (z : Fin n → S × T) : ℝ :=
  perturbedAssignmentValue (fun i j ↦ c (z i).1 (z j).2) 0 0 / (n : ℝ)

theorem measurable_sampleAssignmentMean {n : ℕ} {c : S → T → ℝ}
    (hc : Measurable (Function.uncurry c)) : Measurable (sampleAssignmentMean (n := n) c) := by
  apply Measurable.div_const
  apply measurable_assignmentValue
  intro i j
  exact hc.comp (show Measurable (fun z : Fin n → S × T ↦ ((z i).1, (z j).2)) by
    fun_prop)

omit [MeasurableSpace S] [MeasurableSpace T] in
theorem sampleAssignmentMean_abs_le {n : ℕ} (hn : 0 < n) {c : S → T → ℝ}
    {B : ℝ} (hc : ∀ x y, |c x y| ≤ B) (z : Fin n → S × T) :
    |sampleAssignmentMean c z| ≤ B := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [sampleAssignmentMean, abs_div, abs_of_pos hn']
  apply (div_le_iff₀ hn').mpr
  simpa only [mul_comm] using assignmentValue_abs_le_of_edge_bound
    (fun i j ↦ c (z i).1 (z j).2) B (fun i j ↦ hc _ _)

omit [MeasurableSpace S] [MeasurableSpace T] in
theorem sampleAssignmentMean_update_abs_sub_le {n : ℕ} (hn : 0 < n)
    {c : S → T → ℝ} {B : ℝ} (hB : 0 ≤ B) (hc : ∀ x y, |c x y| ≤ B)
    (z : Fin n → S × T) (i : Fin n) (w : S × T) :
    |sampleAssignmentMean c (Function.update z i w) - sampleAssignmentMean c z| ≤
      4 * B / (n : ℝ) := by
  simp only [sampleAssignmentMean, ← sub_div, abs_div,
    abs_of_pos (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]
  exact div_le_div_of_nonneg_right (assignmentValue_pair_update_abs_sub_le c hB hc z i w)
    (Nat.cast_nonneg n)

/-- A finite product of genuine paired observations satisfies the variance bound. -/
theorem variance_sampleAssignmentMean_pi_le (Q : Measure (S × T)) [IsProbabilityMeasure Q]
    {n : ℕ} (hn : 0 < n) {c : S → T → ℝ}
    (hc : Measurable (Function.uncurry c)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x y, |c x y| ≤ B) :
    variance (sampleAssignmentMean (n := n) c) (Measure.pi fun _ : Fin n ↦ Q) ≤
      16 * B ^ 2 / (n : ℝ) := by
  have h := variance_pi_le_sum_sq_of_bounded_differences Q n
    (measurable_sampleAssignmentMean hc) (sampleAssignmentMean_abs_le hn hbound)
    (fun _ ↦ 4 * B / (n : ℝ))
    (fun i z w ↦ sampleAssignmentMean_update_abs_sub_le hn hB hbound z i w)
  convert h using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp
  ring

/-- Original independent paired samples inherit the actual variance bound. -/
theorem variance_sampleAssignmentMean_iid_le
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure (S × T)) [IsProbabilityMeasure Q]
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → S × T)
    (hZ : ∀ i, Measurable (Z i)) (hi : iIndepFun Z P)
    (hlaw : ∀ i, P.map (Z i) = Q) {c : S → T → ℝ}
    (hc : Measurable (Function.uncurry c)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x y, |c x y| ≤ B) :
    variance (fun ω ↦ sampleAssignmentMean c (fun i ↦ Z i ω)) P ≤
      16 * B ^ 2 / (n : ℝ) := by
  have hvec : Measurable (fun ω i ↦ Z i ω) := measurable_pi_lambda _ hZ
  have hmap : P.map (fun ω i ↦ Z i ω) = Measure.pi (fun _ : Fin n ↦ Q) := by
    rw [hi.map_fun_eq_pi_map (fun i ↦ (hZ i).aemeasurable)]
    simp_rw [hlaw]
  have hpres : MeasurePreserving (fun ω i ↦ Z i ω) P (Measure.pi fun _ : Fin n ↦ Q) :=
    ⟨hvec, hmap⟩
  rw [hpres.variance_fun_comp (measurable_sampleAssignmentMean hc).aemeasurable]
  exact variance_sampleAssignmentMean_pi_le Q hn hc hB hbound

/-- The original finite pressure has an explicit centered deviation probability. -/
theorem deviation_sampleAssignmentMean_iid_le
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure (S × T)) [IsProbabilityMeasure Q]
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → S × T)
    (hZ : ∀ i, Measurable (Z i)) (hi : iIndepFun Z P)
    (hlaw : ∀ i, P.map (Z i) = Q) {c : S → T → ℝ}
    (hc : Measurable (Function.uncurry c)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x y, |c x y| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |sampleAssignmentMean c (fun i ↦ Z i ω) -
      ∫ ω', sampleAssignmentMean c (fun i ↦ Z i ω') ∂P|} ≤
        (16 * B ^ 2 / (n : ℝ)) / ε ^ 2 := by
  have hm : Measurable (fun ω ↦ sampleAssignmentMean c (fun i ↦ Z i ω)) :=
    (measurable_sampleAssignmentMean hc).comp (measurable_pi_lambda _ hZ)
  have h2 : MemLp (fun ω ↦ sampleAssignmentMean c (fun i ↦ Z i ω)) 2 P :=
    MemLp.of_bound hm.aestronglyMeasurable B (Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs] using sampleAssignmentMean_abs_le hn hbound (fun i ↦ Z i ω))
  have h := meas_ge_le_variance_div_sq h2 hε
  have hreal := (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)))
  exact hreal.trans (div_le_div_of_nonneg_right
    (variance_sampleAssignmentMean_iid_le P Q hn Z hZ hi hlaw hc hB hbound) (sq_nonneg _))

end OTSelector.Probability
