import OTSelector.Finite.PerturbedTileRepair
import OTSelector.Reconstruction.IIDTypedCountRepair

/-!
# Physical tile counts from measurable labels

The physical tile blocks are indexed by a label of each sample point.  The
fiber size `blockSizeS` of a label array agrees with the indicator count used
by the iid count-repair estimates.  Consequently the deterministic tile repair
inequality can be restated with indicator counts, and its count discrepancy is
controlled by the existing iid type-count theorem whenever the two color label
sets have equal population mass.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

open OTSelector Reconstruction

/-- The source fiber size of a label array is the indicator count of the
corresponding label set. -/
theorem blockSizeS_comp_eq_indicator_sum {X : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {n : ℕ}
    (label : X → ι) (sample : Fin n → X) (c : ι) :
    ((blockSizeS (fun i => label (sample i)) c : ℕ) : ℝ) =
      ∑ i, ({x : X | label x = c}.indicator (fun _ => (1 : ℝ)) (sample i)) := by
  rw [blockSizeS, blockFinset]
  have h : ((Finset.univ.filter (fun i : Fin n => label (sample i) = c)).card : ℝ) =
      ∑ i : Fin n, (if label (sample i) = c then (1 : ℝ) else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : label (sample i) = c <;> simp [Set.indicator_apply, hi]

/-- The target fiber size, in the same form. -/
theorem blockSizeT_comp_eq_indicator_sum {Y : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {n : ℕ}
    (label : Y → ι) (sample : Fin n → Y) (c : ι) :
    ((blockSizeT (fun j => label (sample j)) c : ℕ) : ℝ) =
      ∑ j, ({y : Y | label y = c}.indicator (fun _ => (1 : ℝ)) (sample j)) := by
  rw [blockSizeT, blockFinset]
  have h : ((Finset.univ.filter (fun j : Fin n => label (sample j) = c)).card : ℝ) =
      ∑ j : Fin n, (if label (sample j) = c then (1 : ℝ) else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : label (sample j) = c <;> simp [Set.indicator_apply, hj]

/-- **Physical tile repair with indicator counts.**  The deterministic repair
inequality, restated with the indicator counts of measurable label sets. -/
theorem perturbedAssignmentValue_le_sum_block_add_indicator
    {M : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (labelS labelT : M → ι) (XS YT : Fin n → M)
    (d g : Fin n → Fin n → ℝ) {t B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i j, d i j + t * g i j ≤ B) :
    perturbedAssignmentValue d g t ≤
      (∑ c : ι, PartialMatching.maxCardValue
        (blockCost (fun i => labelS (XS i))
          (fun j => labelT (YT j)) (perturbedEdgeCost d g t) c)) +
      B * (1 / 2) * ∑ c : ι,
        |(∑ i, ({x : M | labelS x = c}.indicator (fun _ => (1 : ℝ)) (XS i))) -
          (∑ j, ({y : M | labelT y = c}.indicator (fun _ => (1 : ℝ)) (YT j)))| := by
  have h := PartialMatching.perturbedAssignmentValue_le_sum_block_add_discrepancy
    (fun i => labelS (XS i)) (fun j => labelT (YT j)) d g t B hB0 hB
  simpa only [blockSizeS_comp_eq_indicator_sum, blockSizeT_comp_eq_indicator_sum,
    mul_assoc] using h

/-- **Count discrepancy from iid label laws.**  If the two label sets have equal
population mass, the expected discrepancy of the indicator counts is at most
`sqrt (2 n w)`. -/
theorem iidIndicatorCount_difference_bound
    {Ω X Y ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {n : ℕ} (xs : Fin n → Ω → X) (ys : Fin n → Ω → Y)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = ν)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmass : μ.real A = ν.real B) :
    Integrable (fun ξ => |iidTypeCount xs A ξ - iidTypeCount ys B ξ|) P ∧
      (∫ ξ, |iidTypeCount xs A ξ - iidTypeCount ys B ξ| ∂P) ≤
        Real.sqrt (2 * (n : ℝ) * μ.real A) :=
  iidTypeCount_difference_bound P μ ν xs ys hx hy hxi hyi hxl hyl hxy hA hB hmass

end OTSelector.Probability
