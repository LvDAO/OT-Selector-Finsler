import OTSelector.Gauge.LocalLimitCost

/-!
# Smooth scalar profiles and four-point costs

The nonnegative Peano kernel compares every twice differentiable scalar profile with the
quadratic profile. Reflection acts on both the graph and the profile, so no evenness is assumed.
`SmoothProfile` records only analytic data, normalization, and positive curvature bounds.
-/

open Set MeasureTheory
open scoped Interval

namespace OTSelector

/-- Curvature bounds transfer to the forward four-point cost on any compact slope interval. -/
theorem gaugedFourPointCost_compare_quadratic
    {A B m M lam xi eta a b : ℝ} (hAB : A ≤ B) (hxi : xi < eta)
    {gamma f f' f'' : ℝ → ℝ} (hgamma : Continuous gamma)
    (hLip : ScalarLipschitz lam gamma) (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B)
    (hf : ∀ y ∈ Icc A B, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc A B, HasDerivAt f' (f'' y) y)
    (hf'cont : ContinuousOn f' (Icc A B)) (hf''cont : ContinuousOn f'' (Icc A B))
    (hcurv : ∀ t ∈ Icc A B, m ≤ f'' t ∧ f'' t ≤ M)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc A B)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    m * quadraticCost gamma xi eta a b ≤ gaugedFourPointCost f f' gamma xi eta a b ∧
      gaugedFourPointCost f f' gamma xi eta a b ≤ M * quadraticCost gamma xi eta a b := by
  let H := hingeKernel gamma xi eta a b
  have hH : IntervalIntegrable H volume A B :=
    hingeKernel_intervalIntegrable hAB hxi.le hgamma hrange
  have hFH : IntervalIntegrable (fun t ↦ f'' t * H t) volume A B := by
    apply hH.continuousOn_mul
    simpa only [uIcc_of_le hAB] using hf''cont
  have hH0 : ∀ t, 0 ≤ H t := hingeKernel_nonneg hxi hgamma hLip hlam0 hlam ha hb
  have hlo : (∫ t in A..B, m * H t) ≤ ∫ t in A..B, f'' t * H t := by
    apply intervalIntegral.integral_mono_on hAB (hH.const_mul _) hFH
    exact fun t ht ↦ mul_le_mul_of_nonneg_right (hcurv t ht).1 (hH0 t)
  have hhi : (∫ t in A..B, f'' t * H t) ≤ ∫ t in A..B, M * H t := by
    apply intervalIntegral.integral_mono_on hAB hFH (hH.const_mul _)
    exact fun t ht ↦ mul_le_mul_of_nonneg_right (hcurv t ht).2 (hH0 t)
  have hF := gaugedFourPointCost_eq_hinge_integral hAB hxi.le hgamma hrange
    hf hf' hf'cont hf''cont hq ha hb
  have hQ := quadraticCost_eq_hinge_integral hAB hxi.le hgamma hrange hq ha hb
  constructor
  · rw [hF, hQ, ← intervalIntegral.integral_const_mul]
    exact hlo
  · rw [hF, hQ, ← intervalIntegral.integral_const_mul]
    exact hhi

/-- A two-sided curvature error gives a relative four-point cost error. -/
theorem gaugedFourPointCost_sub_quadratic_abs_le
    {A B eps lam xi eta a b : ℝ} (hAB : A ≤ B) (hxi : xi < eta)
    {gamma f f' f'' : ℝ → ℝ} (hgamma : Continuous gamma)
    (hLip : ScalarLipschitz lam gamma) (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc A B)
    (hf : ∀ y ∈ Icc A B, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc A B, HasDerivAt f' (f'' y) y)
    (hf'cont : ContinuousOn f' (Icc A B)) (hf''cont : ContinuousOn f'' (Icc A B))
    (hcurv : ∀ t ∈ Icc A B, |f'' t - 1| ≤ eps)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc A B)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    |gaugedFourPointCost f f' gamma xi eta a b - quadraticCost gamma xi eta a b| ≤
      eps * quadraticCost gamma xi eta a b := by
  have hcomp := gaugedFourPointCost_compare_quadratic (m := 1 - eps) (M := 1 + eps)
    hAB hxi hgamma hLip hlam0 hlam hrange hf hf' hf'cont hf''cont
    (fun t ht ↦ by have h := abs_le.mp (hcurv t ht); constructor <;> linarith) hq ha hb
  apply abs_le.mpr
  constructor <;> nlinarith [hcomp.1, hcomp.2]

/-- Reflecting the cost as well as the graph preserves the signed four-point functional. -/
theorem gaugedFourPointCost_reflected
    (f f' gamma : ℝ → ℝ) (xi eta a b : ℝ) :
    gaugedFourPointCost (fun z ↦ f (-z)) (fun z ↦ -f' (-z))
        (reflectedGraph gamma) (-xi) (-eta) a b =
      gaugedFourPointCost f f' gamma xi eta a b := by
  have hi : (∫ x in -xi..-eta, -f' (-(reflectedGraph gamma x))) =
      ∫ x in xi..eta, f' (gamma x) := by
    simp only [reflectedGraph, neg_neg, intervalIntegral.integral_neg]
    rw [intervalIntegral.integral_comp_neg (f := fun x ↦ f' (gamma x))]
    simp only [neg_neg]
    rw [intervalIntegral.integral_symm]
    ring
  unfold gaugedFourPointCost
  simp only [fourPointQuotient_reflectedGraph, fourPointSourceValue, fourPointTargetValue,
    reflectedGraph, neg_neg]
  rw [show (∫ x in -xi..-eta, -f' (gamma (-x))) =
    ∫ x in xi..eta, f' (gamma x) by simpa only [reflectedGraph, neg_neg] using hi]

/-- A coincident-endpoint four-point functional vanishes, independently of the profile. -/
theorem gaugedFourPointCost_diagonal
    (f f' gamma : ℝ → ℝ) (xi a b : ℝ) (hD : a + b ≠ 0) :
    gaugedFourPointCost f f' gamma xi xi a b = 0 := by
  have hq : fourPointQuotient gamma xi xi a b = gamma xi := by
    unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
      fourPointDenominator
    field_simp
    ring
  simp [gaugedFourPointCost, hq, fourPointDenominator,
    fourPointSourceValue, fourPointTargetValue]
  ring

/-- A normalized `C²` scalar profile with positive curvature on the unit slope strip.
The fields are analytic hypotheses; no transport or selection conclusion is assumed. -/
structure SmoothProfile where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ
  hasDeriv_value : ∀ x, HasDerivAt value (first x) x
  hasDeriv_first : ∀ x, HasDerivAt first (second x) x
  continuous_second : Continuous second
  value_zero : value 0 = 0
  first_zero : first 0 = 0
  second_zero : second 0 = 1
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  curvature_bounds : ∀ x ∈ Icc (-1 : ℝ) 1, lower ≤ second x ∧ second x ≤ upper

namespace SmoothProfile

variable (P : SmoothProfile)

theorem continuous_first : Continuous P.first :=
  continuous_iff_continuousAt.mpr fun x ↦ (P.hasDeriv_first x).continuousAt

theorem upper_pos : 0 < P.upper := by
  have h := (P.curvature_bounds 0 (by constructor <;> norm_num)).2
  rw [P.second_zero] at h
  linarith

/-- Reflection preserves normalization and both curvature constants. -/
noncomputable def reflect : SmoothProfile where
  value x := P.value (-x)
  first x := -P.first (-x)
  second x := P.second (-x)
  hasDeriv_value x := by
    simpa [Function.comp_def] using (P.hasDeriv_value (-x)).comp x (hasDerivAt_neg x)
  hasDeriv_first x := by
    simpa [Function.comp_def, Pi.neg_def] using
      ((P.hasDeriv_first (-x)).comp x (hasDerivAt_neg x)).neg
  continuous_second := P.continuous_second.comp continuous_neg
  value_zero := by simpa using P.value_zero
  first_zero := by simp [P.first_zero]
  second_zero := by simpa using P.second_zero
  lower := P.lower
  upper := P.upper
  lower_pos := P.lower_pos
  curvature_bounds x hx := P.curvature_bounds (-x) (by
    constructor <;> linarith [hx.1, hx.2])

/-- The four-point gauged cost for this profile. -/
noncomputable def gaugedCost (gamma : ℝ → ℝ) (xi eta a b : ℝ) : ℝ :=
  gaugedFourPointCost P.value P.first gamma xi eta a b

@[simp] theorem gaugedCost_reflected (gamma : ℝ → ℝ) (xi eta a b : ℝ) :
    P.reflect.gaugedCost (reflectedGraph gamma) (-xi) (-eta) a b =
      P.gaugedCost gamma xi eta a b :=
  gaugedFourPointCost_reflected P.value P.first gamma xi eta a b

/-- Uniform curvature comparison for increasing endpoints. -/
theorem compare_quadratic_forward
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    P.lower * quadraticCost gamma xi eta a b ≤ P.gaugedCost gamma xi eta a b ∧
      P.gaugedCost gamma xi eta a b ≤ P.upper * quadraticCost gamma xi eta a b := by
  exact gaugedFourPointCost_compare_quadratic (by norm_num) hxi hgamma hLip hlam0 hlam
    hrange (fun y _ ↦ P.hasDeriv_value y) (fun y _ ↦ P.hasDeriv_first y)
    P.continuous_first.continuousOn P.continuous_second.continuousOn
    P.curvature_bounds hq ha hb

/-- The same curvature comparison holds for all endpoint orders, with no evenness assumption. -/
theorem compare_quadratic
    {lam xi eta a b : ℝ} {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2)
    (hrange : ∀ x ∈ uIcc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    P.lower * quadraticCost gamma xi eta a b ≤ P.gaugedCost gamma xi eta a b ∧
      P.gaugedCost gamma xi eta a b ≤ P.upper * quadraticCost gamma xi eta a b := by
  rcases lt_trichotomy xi eta with h | h | h
  · exact P.compare_quadratic_forward h hgamma hLip hlam0 hlam
      (by simpa only [uIcc_of_le h.le] using hrange) hq ha hb
  · subst eta
    have hD : a + b ≠ 0 := by linarith [ha.1, hb.1]
    simp [gaugedCost, quadraticCost, gaugedFourPointCost_diagonal _ _ _ _ _ _ hD]
  · have hrev := P.reflect.compare_quadratic_forward (show -xi < -eta by linarith)
      (reflectedGraph_continuous hgamma) (reflectedGraph_lipschitz hLip) hlam0 hlam
      (reflectedGraph_range (by simpa only [uIcc_of_ge h.le] using hrange))
      (reflectedGraph_quotient_range hq) ha hb
    rw [gaugedCost_reflected] at hrev
    simpa only [reflect, quadraticCost_reflected] using hrev

/-- The profile coercivity constants multiply the existing quadratic constants. -/
theorem coercive_forward
    {lam xi eta a b : ℝ} (hxi : xi < eta) {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hrange : ∀ x ∈ Icc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    P.lower * quadraticLowerConstant' lam * (eta - xi) ^ 2 ≤
        P.gaugedCost gamma xi eta a b ∧
      P.gaugedCost gamma xi eta a b ≤
        P.upper * quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  have hc := P.compare_quadratic_forward hxi hgamma hLip hlam0
    (hlam.trans (by norm_num)) hrange hq ha hb
  constructor
  · calc
      _ = P.lower * (quadraticLowerConstant' lam * (eta - xi) ^ 2) := by ring
      _ ≤ P.lower * quadraticCost gamma xi eta a b :=
        mul_le_mul_of_nonneg_left
          (quadraticGauge_lower_bound hxi hgamma hLip hlam0 hlam ha hb) P.lower_pos.le
      _ ≤ _ := hc.1
  · calc
      _ ≤ P.upper * quadraticCost gamma xi eta a b := hc.2
      _ ≤ P.upper * (quadraticUpperConstant lam * (eta - xi) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (quadraticGauge_upper_bound hxi hgamma hLip hlam0 hlam ha hb) P.upper_pos.le
      _ = _ := by ring

/-- Coercivity for increasing, decreasing, and coincident endpoints. -/
theorem coercive
    {lam xi eta a b : ℝ} {gamma : ℝ → ℝ}
    (hgamma : Continuous gamma) (hLip : ScalarLipschitz lam gamma)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hrange : ∀ x ∈ uIcc xi eta, gamma x ∈ Icc (-1 : ℝ) 1)
    (hq : fourPointQuotient gamma xi eta a b ∈ Icc (-1 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    P.lower * quadraticLowerConstant' lam * (eta - xi) ^ 2 ≤
        P.gaugedCost gamma xi eta a b ∧
      P.gaugedCost gamma xi eta a b ≤
        P.upper * quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  rcases lt_trichotomy xi eta with h | h | h
  · exact P.coercive_forward h hgamma hLip hlam0 hlam
      (by simpa only [uIcc_of_le h.le] using hrange) hq ha hb
  · subst eta
    have hD : a + b ≠ 0 := by linarith [ha.1, hb.1]
    simp [gaugedCost, gaugedFourPointCost_diagonal _ _ _ _ _ _ hD]
  · have hrev := P.reflect.coercive_forward (show -xi < -eta by linarith)
      (reflectedGraph_continuous hgamma) (reflectedGraph_lipschitz hLip) hlam0 hlam
      (reflectedGraph_range (by simpa only [uIcc_of_ge h.le] using hrange))
      (reflectedGraph_quotient_range hq) ha hb
    rw [gaugedCost_reflected] at hrev
    have hs : (-eta - -xi) ^ 2 = (eta - xi) ^ 2 := by ring
    simpa only [reflect, hs] using hrev

end SmoothProfile

end OTSelector
