import OTSelector.Reconstruction.DyadicCubePartition
import OTSelector.Reconstruction.DyadicMatchingRate

/-!
# A genuine dyadic competitor for original iid cube samples

The squared assignment value is controlled by finite-depth dyadic fluctuations
under an arbitrary population law on the closed cube.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The literal squared coordinate cost of two original cube samples. -/
def cubeSquaredEdgeCost {Ω : Type*} {q n : ℕ}
    (xs ys : Fin n → Ω → DyadicUnitCube q) (ξ : Ω) (i j : Fin n) : ℝ :=
  ‖dyadicCubePoint (xs i ξ) - dyadicCubePoint (ys j ξ)‖ ^ 2

/-- Every finite cutoff gives an actual expected squared assignment bound;
there is no regularity or density assumption on the common cube law. -/
theorem expected_cubeSquaredAssignment_multiscale
    {Ω : Type*} [MeasurableSpace Ω] {q n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P) (K : ℕ) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (cubeSquaredEdgeCost xs ys ξ) 0 0) P ∧
    (∫ ξ, perturbedAssignmentValue (cubeSquaredEdgeCost xs ys ξ) 0 0 ∂P) ≤
      (n : ℝ) * (1 / 4 : ℝ) ^ K + (1 / 2 : ℝ) *
        ∑ k ∈ Finset.range K, (1 / 4 : ℝ) ^ k *
          Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (k + 1) + 1) ^ q) := by
  classical
  let cell := fun k : Fin K ↦ dyadicCubeCell (q := q) (k.val + 1)
  have hm : ∀ (k : Fin K) a, MeasurableSet {x | cell k x = a} := by
    intro k a
    exact (measurable_dyadicCubeCell (k.val + 1)) (measurableSet_singleton a)
  have hnested : ∀ (k l : Fin K), k ≤ l → ∀ a b,
      cell l a = cell l b → cell k a = cell k b := by
    intro k l hkl a b hab
    exact dyadicCubeCell_nested (Nat.add_le_add_right hkl 1) a b hab
  have hmp : Measurable (dyadicCubePoint (q := q)) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  have hc (i j : Fin n) : Measurable (fun ξ ↦ cubeSquaredEdgeCost xs ys ξ i j) :=
    ((hmp.comp (hx i)).sub (hmp.comp (hy j))).norm.pow_const 2
  have hcost (ξ : Ω) (i j : Fin n) : cubeSquaredEdgeCost xs ys ξ i j ≤
      (1 / 4 : ℝ) ^ K + ∑ k : Fin K, (1 / 4 : ℝ) ^ k.val *
        partitionDistance (cell k (xs i ξ)) (cell k (ys j ξ)) := by
    change ‖dyadicCubePoint (xs i ξ) - dyadicCubePoint (ys j ξ)‖ ^ 2 ≤
      (1 / 4 : ℝ) ^ K + ∑ k : Fin K, (1 / 4 : ℝ) ^ k.val *
        partitionDistance (dyadicCubeCell (k.val + 1) (xs i ξ)) (dyadicCubeCell (k.val + 1) (ys j ξ))
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ (1 / 4 : ℝ) ^ k *
      partitionDistance (dyadicCubeCell (k + 1) (xs i ξ)) (dyadicCubeCell (k + 1) (ys j ξ)))]
    exact dyadicCube_sqdist_multiscale K (xs i ξ) (ys j ξ)
  have h := expected_hierarchical_assignment_bound P μ xs ys hx hy hxi hyi hxl hyl hxy
    cell hm hnested (cubeSquaredEdgeCost xs ys) hc (fun ξ i j ↦ sq_nonneg _)
    ((1 / 4 : ℝ) ^ K) (fun k : Fin K ↦ (1 / 4 : ℝ) ^ k.val)
    (fun _ ↦ by positivity) hcost
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at h
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (1 / 4 : ℝ) ^ k *
    Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (k + 1) + 1) ^ q))] at h
  exact h

/-- Distribution-free quadratic matching for the actual two independent iid
colors in a closed q-cube. The threshold q > 4 is discharged by the cutoff. -/
theorem expected_cubeSquaredAssignment_rate
    {Ω : Type*} [MeasurableSpace Ω] {q n : ℕ} (hq : 4 < q)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (cubeSquaredEdgeCost xs ys ξ) 0 0) P ∧
    (∫ ξ, perturbedAssignmentValue (cubeSquaredEdgeCost xs ys ξ) 0 0 ∂P) ≤
      dyadicMatchingConstant q * (n : ℝ) ^ (1 - 2 / (q : ℝ)) := by
  by_cases hn : 0 < n
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨K, hK⟩ := exists_dyadicCube_rate_cutoff hq hnR
    have h := expected_cubeSquaredAssignment_multiscale P μ xs ys hx hy hxi hyi hxl hyl hxy K
    exact ⟨h.1, h.2.trans hK⟩
  · have hn0 : n = 0 := by omega
    subst n
    have hqR : (4 : ℝ) < q := by exact_mod_cast hq
    have hγ : 0 < 1 - 2 / (q : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
    simp [perturbedAssignmentValue, assignmentCost, Real.zero_rpow hγ.ne']

set_option backward.isDefEq.respectTransparency false in
/-- Any actual nonnegative edge cost controlled by the same original cube labels
inherits the squared matching rate, with its genuine whole-chart constant. -/
theorem expected_cost_le_cubeMatching_rate
    {Ω : Type*} [MeasurableSpace Ω] {q n : ℕ} (hq : 4 < q)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j)) {C : ℝ} (hC : 0 ≤ C)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hcost : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ C * cubeSquaredEdgeCost xs ys ξ i j) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (cost ξ) 0 0) P ∧
    (∫ ξ, perturbedAssignmentValue (cost ξ) 0 0 ∂P) ≤
      C * dyadicMatchingConstant q * (n : ℝ) ^ (1 - 2 / (q : ℝ)) := by
  have hcube := expected_cubeSquaredAssignment_rate hq P μ xs ys hx hy hxi hyi hxl hyl hxy
  have hci (i j : Fin n) : Integrable (fun ξ ↦ cost ξ i j) P := by
    apply (integrable_const C).mono' (hc i j).aestronglyMeasurable
    filter_upwards [hcn, hcost] with ξ hnξ hcξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hnξ i j)]
    apply (hcξ i j).trans
    have hb := pow_le_pow_left₀ (norm_nonneg _) (dyadicCube_dist_le_one (xs i ξ) (ys j ξ)) 2
    simpa only [cubeSquaredEdgeCost, one_pow, mul_one] using mul_le_mul_of_nonneg_left hb hC
  have hi := Probability.integrable_assignmentValue P cost hc hci
  refine ⟨hi, ?_⟩
  have hv : ∀ᵐ ξ ∂P, perturbedAssignmentValue (cost ξ) 0 0 ≤
      C * perturbedAssignmentValue (cubeSquaredEdgeCost xs ys ξ) 0 0 := by
    filter_upwards [hcost] with ξ hcξ
    let σ := optimalAssignment (cubeSquaredEdgeCost xs ys ξ)
    have hle := perturbedAssignmentValue_le (cost ξ) 0 0 σ
    simp only [perturbedEdgeCost_zero] at hle
    apply hle.trans
    have hσ : OptimalAssignment (perturbedEdgeCost (cubeSquaredEdgeCost xs ys ξ) 0 0) σ := by
      simpa [σ, perturbedEdgeCost] using optimalAssignment_isOptimal (cubeSquaredEdgeCost xs ys ξ)
    have heq := perturbedAssignmentValue_eq_of_optimal (cubeSquaredEdgeCost xs ys ξ) 0 0 σ hσ
    simp at heq
    rw [heq]
    change (∑ i, cost ξ i (σ i)) ≤ C * ∑ i, cubeSquaredEdgeCost xs ys ξ i (σ i)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ hcξ i (σ i))
  have hle := integral_mono_ae hi (hcube.1.const_mul C) hv
  rw [integral_const_mul] at hle
  exact hle.trans ((mul_le_mul_of_nonneg_left hcube.2 hC).trans_eq (by ring))

end OTSelector.Reconstruction
