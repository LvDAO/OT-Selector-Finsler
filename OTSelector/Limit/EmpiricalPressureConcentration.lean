import OTSelector.Limit.EmpiricalPressureSelector
import OTSelector.Probability.AssignmentPressureConvergence

/-!
# Concentration of the original distance pressure above effective dimension four

On the compact union of the original supports, the actual distance slack is a
bounded continuous paired cost. For `q > 4`, the scale `n^(2/q)` grows slower
than square root. The genuine pressure minus its original expectation therefore
converges to zero in probability for every fixed paired probe and tilt.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

namespace OTSelector.Pressure

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The actual iid distance pressure concentrates around its own expectation.
Compactness applies to the support union with the restricted ambient distance. -/
theorem tendsto_centered_empiricalDistancePressure
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ ν : ProbabilityMeasure M)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun ω i ↦ X n i ω) (fun ω i ↦ Y n i ω) (P n))
    (φ : M → ℝ) (hφ : Continuous φ) (q : ℝ) (hq : 4 < q)
    (f : (M × M) →ᵇ ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {ω |
      ε ≤ |empiricalDistancePressure (fun i ↦ X n i ω) (fun i ↦ Y n i ω)
        φ (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f t -
        ∫ ω', empiricalDistancePressure (fun i ↦ X n i ω') (fun i ↦ Y n i ω')
          φ (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f t ∂P n|}) atTop (𝓝 0) := by
  let s : (M × M) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun z ↦ dist z.1 z.2 - φ z.2 + φ z.1,
      ((continuous_fst.dist continuous_snd).sub (hφ.comp continuous_snd)).add
        (hφ.comp continuous_fst)⟩
  let c (n : ℕ) (x y : M) : ℝ :=
    ((n + 1 : ℕ) : ℝ) ^ (2 / q) * s (x, y) + t * f (x, y)
  have hc (n : ℕ) : Measurable (Function.uncurry (c n)) :=
    (s.continuous.const_mul _ |>.add (f.continuous.const_mul t)).measurable
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have ha : 2 / q < 1 / 2 := by
    rw [div_lt_iff₀ hqpos]
    linarith
  have hb (n : ℕ) (x y : M) : |c n x y| ≤
      (‖s‖ + |t| * ‖f‖) * ((n + 1 : ℕ) : ℝ) ^ (2 / q) := by
    have hscale : 1 ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / q) :=
      Real.one_le_rpow (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
        (div_nonneg (by norm_num) hqpos.le)
    calc
      |c n x y| ≤ |((n + 1 : ℕ) : ℝ) ^ (2 / q) * s (x, y)| + |t * f (x, y)| :=
        abs_add_le _ _
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / q) * ‖s‖ + |t| * ‖f‖ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (le_trans zero_le_one hscale)]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (s.norm_coe_le_norm (x, y)) (le_trans zero_le_one hscale))
          (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x, y)) (abs_nonneg t))
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / q) * ‖s‖ +
          (|t| * ‖f‖) * ((n + 1 : ℕ) : ℝ) ^ (2 / q) := by
        exact add_le_add le_rfl
          (le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hscale)
      _ = _ := by ring
  have h := Probability.tendsto_centered_bipartiteAssignmentMean P
    (μ : Measure M) (ν : Measure M) X Y hX hY hXi hYi hXlaw hYlaw hXY c hc
    (add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))) ha hb hε
  have heq (n : ℕ) (ω : Ω n) :
      Probability.sampleAssignmentMean (c n) (fun i ↦ (X n i ω, Y n i ω)) =
      empiricalDistancePressure (fun i ↦ X n i ω) (fun i ↦ Y n i ω)
        φ (((n + 1 : ℕ) : ℝ) ^ (2 / q)) f t := by
    unfold Probability.sampleAssignmentMean empiricalDistancePressure perturbedAssignmentValue
    unfold OTSelector.perturbedEdgeCost
    simp only [zero_mul, add_zero]
    rfl
  simpa only [heq] using h

end OTSelector.Pressure
