import OTSelector.Probability.BinomialDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Fine reference complexity multiplies only the vanishing original count error. -/
open Filter
open scoped Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- A fixed finite collection of actual unscaled edge bounds pays no normalized
cost for the original square-root count discrepancy when q > 4. -/
theorem tendsto_original_model_count_price_zero
    {C : Type*} [Fintype C] {q : ℕ} (hq : 4 < q)
    (multiplicity bound : C → ℝ) (G tilt : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      (∑ c, multiplicity c * ((n : ℝ) ^ (2 / (q : ℝ)) * bound c + |tilt| * G)) *
        Real.sqrt (2 * (n : ℝ) * (k : ℝ)) / n) atTop (𝓝 0) := by
  classical
  have hc (c : C) := (OTSelector.Probability.tendsto_binomial_repairError_zero hq
    (bound c) G tilt k).const_mul (2 * multiplicity c)
  have hs := tendsto_finsetSum Finset.univ (fun c _ ↦ hc c)
  simp only [mul_zero, Finset.sum_const_zero] at hs
  convert hs using 1
  funext n
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The good and small bad original hierarchies each carry one fixed finite
histogram. Their combined model augmentation cost vanishes at fixed depth. -/
theorem tendsto_original_model_good_bad_count_error_zero
    {C : Type*} [Fintype C] {q : ℕ} (hq : 4 < q)
    (multiplicity bound : C → ℝ) (G tilt : ℝ) (goodTypes badTypes depth : ℕ) :
    Tendsto (fun n : ℕ ↦
      (∑ c, multiplicity c * ((n : ℝ) ^ (2 / (q : ℝ)) * bound c + |tilt| * G)) *
        ((goodTypes : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ depth + 1) ^ q) +
          (badTypes : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) / n)
      atTop (𝓝 0) := by
  have hg := (tendsto_original_model_count_price_zero hq multiplicity bound G tilt
    ((2 ^ depth + 1) ^ q)).const_mul (goodTypes : ℝ)
  have hb := (tendsto_original_model_count_price_zero hq multiplicity bound G tilt
    ((2 ^ (1 : ℕ) + 1) ^ q)).const_mul (badTypes : ℝ)
  have h := hg.add hb
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext n
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- The original hierarchy's own normalized count term also vanishes. -/
theorem tendsto_original_model_energy_count_zero {q : ℕ} (hq : 4 < q) (A : ℝ) :
    Tendsto (fun n : ℕ ↦ A * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2)) atTop (𝓝 0) := by
  have hqR : (4 : ℝ) < q := Nat.cast_lt.mpr hq
  have hqpos : (0 : ℝ) < q := by positivity
  have hneg : 2 / (q : ℝ) - 1 / 2 < 0 := by
    have h : 2 / (q : ℝ) < 1 / 2 := (div_lt_iff₀ hqpos).mpr (by linarith)
    linarith
  have h := ((tendsto_rpow_neg_atTop (y := -(2 / (q : ℝ) - 1 / 2))
    (by linarith)).comp tendsto_natCast_atTop_atTop).const_mul A
  simpa only [Function.comp_def, neg_neg, mul_zero] using h

/-- A small compact discard can be chosen after the finite cells. The scalar
observable itself must be unchanged as that approximation is refined. -/
theorem eventually_le_of_all_small_compact_errors
    (value : ℕ → ℝ) (leading discarded : ℝ) {exponent : ℝ} (hexponent : 0 < exponent)
    (hupper : ∀ θ : ℝ, 0 < θ → ∃ error : ℕ → ℝ,
      Tendsto error atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        value n ≤ leading + discarded * θ ^ exponent + error n) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ n in atTop, value n ≤ leading + tolerance := by
  intro tolerance htolerance
  have hc : Tendsto (fun θ : ℝ ↦ discarded * θ ^ exponent) (𝓝 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 exponent (Or.inr hexponent.le)).tendsto.const_mul discarded
    simpa only [Real.zero_rpow (ne_of_gt hexponent), mul_zero] using h
  have hsmall : ∀ᶠ θ : ℝ in 𝓝 0, discarded * θ ^ exponent < tolerance / 2 :=
    hc.eventually (gt_mem_nhds (by linarith))
  obtain ⟨radius,hradius,hball⟩ := Metric.mem_nhds_iff.mp hsmall
  let θ := radius / 2
  have hθ : 0 < θ := by dsimp only [θ]; linarith
  have hθsmall : discarded * θ ^ exponent < tolerance / 2 := by
    apply hball
    change dist θ 0 < radius
    rw [Real.dist_eq, sub_zero, abs_of_pos hθ]
    dsimp only [θ]
    linarith
  obtain ⟨error,herror,hbound⟩ := hupper θ hθ
  have he : ∀ᶠ n in atTop, error n < tolerance / 2 := herror.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hbound,he] with n hn he
  linarith

end OTSelector.Reconstruction
