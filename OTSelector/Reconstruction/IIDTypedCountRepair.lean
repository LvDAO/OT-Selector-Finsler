import OTSelector.Probability.BipartiteAssignmentConcentration
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Real.Sqrt

/-!
# Original iid type counts and count repair

Type membership is read on the original samples. The mean and variance estimates
use their actual iid laws and independent colors, including types of zero mass.
They supply the count component of deterministic population-piece recovery.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The real count of an original finite sample lying in a measurable type. -/
def iidTypeCount {Ω X : Type*} {n : ℕ} (sample : Fin n → Ω → X) (A : Set X) : Ω → ℝ :=
  fun ξ ↦ ∑ i, A.indicator (fun _ ↦ (1 : ℝ)) (sample i ξ)

/-- A measurable type indicator has its exact Bernoulli variance under the
original population, whether or not the type has positive mass. -/
theorem variance_type_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {A : Set X} (hA : MeasurableSet A) :
    variance (A.indicator (fun _ ↦ (1 : ℝ))) μ = μ.real A - (μ.real A) ^ 2 := by
  have h2 : MemLp (A.indicator (fun _ ↦ (1 : ℝ))) 2 μ := (memLp_const 1).indicator hA
  rw [variance_eq_sub h2]
  have hsq : (A.indicator (fun _ ↦ (1 : ℝ))) ^ 2 = A.indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hsq]
  have he : (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂μ) = μ.real A :=
    integral_indicator_one hA
  rw [he]

/-- Actual iid type counts have the population mean and binomial variance,
without replacing or conditioning the original sample array. -/
theorem iidTypeCount_moments {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure X) [IsProbabilityMeasure μ]
    {n : ℕ} (sample : Fin n → Ω → X)
    (hs : ∀ i, Measurable (sample i)) (hi : iIndepFun sample P)
    (hlaw : ∀ i, P.map (sample i) = μ) {A : Set X} (hA : MeasurableSet A) :
    MemLp (iidTypeCount sample A) 2 P ∧
      (∫ ξ, iidTypeCount sample A ξ ∂P) = n * μ.real A ∧
      variance (iidTypeCount sample A) P = n * (μ.real A - (μ.real A) ^ 2) := by
  let f := A.indicator (fun _ ↦ (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hA
  have h2 : MemLp f 2 μ := (memLp_const 1).indicator hA
  have hp (i : Fin n) : MeasurePreserving (sample i) P μ := ⟨hs i, hlaw i⟩
  have hrow (i : Fin n) : MemLp (fun ξ ↦ f (sample i ξ)) 2 P := h2.comp_measurePreserving (hp i)
  have hsum : MemLp (iidTypeCount sample A) 2 P :=
    memLp_finsetSum _ (fun i _ ↦ hrow i)
  have hmean (i : Fin n) : (∫ ξ, f (sample i ξ) ∂P) = μ.real A := by
    rw [← integral_map (hs i).aemeasurable hf.aestronglyMeasurable, hlaw i]
    exact integral_indicator_one hA
  have hvar (i : Fin n) : variance (fun ξ ↦ f (sample i ξ)) P =
      μ.real A - (μ.real A) ^ 2 :=
    ((hp i).variance_fun_comp hf.aemeasurable).trans (variance_type_indicator μ hA)
  refine ⟨hsum, ?_, ?_⟩
  · change (∫ ξ, ∑ i, f (sample i ξ) ∂P) = _
    rw [integral_finsetSum _ (fun i _ ↦ (hrow i).integrable (by norm_num))]
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · have hind := hi.comp (fun _ ↦ f) (fun _ ↦ hf)
    have heq : iidTypeCount sample A = ∑ i, (fun ξ ↦ f (sample i ξ)) := by
      funext ξ
      simp only [iidTypeCount, Finset.sum_apply, f]
    rw [heq, IndepFun.variance_sum (fun i _ ↦ hrow i)
      (fun i _ j _ hij ↦ hind.indepFun hij)]
    simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Cauchy--Schwarz on a probability space in the form needed for count repair. -/
theorem integral_abs_le_sqrt_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ} (h2 : MemLp f 2 P) :
    (∫ ξ, |f ξ| ∂P) ≤ Real.sqrt (∫ ξ, (f ξ) ^ 2 ∂P) := by
  have hv := variance_nonneg (fun ξ ↦ |f ξ|) P
  have ha2 : MemLp (fun ξ ↦ |f ξ|) 2 P := by
    simpa only [Real.norm_eq_abs] using h2.norm
  rw [variance_eq_sub ha2] at hv
  have hsq : (fun ξ ↦ |f ξ|) ^ 2 = fun ξ ↦ (f ξ) ^ 2 := by
    funext ξ
    simp only [Pi.pow_apply, sq_abs]
  rw [hsq] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- Independent original colors with equal population type mass have a
square-root count discrepancy. No equality of the realized counts is assumed. -/
theorem iidTypeCount_difference_bound
    {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {n : ℕ} (xs : Fin n → Ω → X) (ys : Fin n → Ω → Y)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = ν)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmass : μ.real A = ν.real B) :
    Integrable (fun ξ ↦ |iidTypeCount xs A ξ - iidTypeCount ys B ξ|) P ∧
      (∫ ξ, |iidTypeCount xs A ξ - iidTypeCount ys B ξ| ∂P) ≤
        Real.sqrt (2 * (n : ℝ) * μ.real A) := by
  obtain ⟨hx2, hxm, hxv⟩ := iidTypeCount_moments P μ xs hx hxi hxl hA
  obtain ⟨hy2, hym, hyv⟩ := iidTypeCount_moments P ν ys hy hyi hyl hB
  have hf : Measurable (fun z : Fin n → X ↦
      ∑ i, A.indicator (fun _ ↦ (1 : ℝ)) (z i)) :=
    Finset.measurable_sum _ (fun i _ ↦ (measurable_const.indicator hA).comp (measurable_pi_apply i))
  have hg : Measurable (fun z : Fin n → Y ↦
      ∑ i, B.indicator (fun _ ↦ (1 : ℝ)) (z i)) :=
    Finset.measurable_sum _ (fun i _ ↦ (measurable_const.indicator hB).comp (measurable_pi_apply i))
  have hind : IndepFun (iidTypeCount xs A) (iidTypeCount ys B) P := hxy.comp hf hg
  have h2 := hx2.sub hy2
  have hiX := hx2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hiY := hy2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hzero : (∫ ξ, iidTypeCount xs A ξ - iidTypeCount ys B ξ ∂P) = 0 := by
    rw [integral_sub hiX hiY, hxm, hym, hmass, sub_self]
  have hsecond : (∫ ξ, (iidTypeCount xs A ξ - iidTypeCount ys B ξ) ^ 2 ∂P) ≤
      2 * (n : ℝ) * μ.real A := by
    have hvar := variance_fun_sub hx2 hy2
    rw [hind.covariance_eq_zero hx2 hy2, hxv, hyv, ← hmass] at hvar
    have hs := variance_eq_sub h2
    change variance (fun ξ ↦ iidTypeCount xs A ξ - iidTypeCount ys B ξ) P =
      (∫ ξ, (iidTypeCount xs A ξ - iidTypeCount ys B ξ) ^ 2 ∂P) -
        (∫ ξ, iidTypeCount xs A ξ - iidTypeCount ys B ξ ∂P) ^ 2 at hs
    rw [hzero] at hs
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq := sq_nonneg (μ.real A)
    nlinarith
  exact ⟨(hiX.sub hiY).abs,
    (integral_abs_le_sqrt_secondMoment h2).trans (Real.sqrt_le_sqrt hsecond)⟩

/-- Summing square roots of finitely many original type masses loses only the
square root of the number of types. Zero-mass types require no normalization. -/
theorem sum_sqrt_typeMass_le {T : Type*} [Fintype T] (p : T → ℝ)
    (hp : ∀ t, 0 ≤ p t) :
    (∑ t, Real.sqrt (p t)) ≤ Real.sqrt ((Fintype.card T : ℝ) * ∑ t, p t) := by
  have h := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
    (f := fun _ : T ↦ (1 : ℝ)) (g := p) (fun _ ↦ zero_le_one) hp
  simpa only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Real.sqrt_mul (Nat.cast_nonneg (Fintype.card T))] using h

/-- The full discrepancy of finitely many deterministic population types is
controlled by their total original mass. The type events may include independent
RN marks on an enlarged original sample space. -/
theorem iidTypeCount_total_difference_bound
    {Ω X Y T : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype T] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {n : ℕ} (xs : Fin n → Ω → X) (ys : Fin n → Ω → Y)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = ν)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (A : T → Set X) (B : T → Set Y)
    (hA : ∀ t, MeasurableSet (A t)) (hB : ∀ t, MeasurableSet (B t))
    (hmass : ∀ t, μ.real (A t) = ν.real (B t)) {ε : ℝ}
    (hε : ∑ t, μ.real (A t) = ε) :
    Integrable (fun ξ ↦ ∑ t, |iidTypeCount xs (A t) ξ - iidTypeCount ys (B t) ξ|) P ∧
      (∫ ξ, ∑ t, |iidTypeCount xs (A t) ξ - iidTypeCount ys (B t) ξ| ∂P) ≤
        Real.sqrt (2 * (n : ℝ) * Fintype.card T * ε) := by
  have ht (t : T) := iidTypeCount_difference_bound P μ ν xs ys hx hy hxi hyi
    hxl hyl hxy (hA t) (hB t) (hmass t)
  refine ⟨integrable_finsetSum _ (fun t _ ↦ (ht t).1), ?_⟩
  rw [integral_finsetSum _ (fun t _ ↦ (ht t).1)]
  calc
    _ ≤ ∑ t, Real.sqrt (2 * (n : ℝ) * μ.real (A t)) :=
      Finset.sum_le_sum (fun t _ ↦ (ht t).2)
    _ ≤ Real.sqrt ((Fintype.card T : ℝ) * ∑ t, 2 * (n : ℝ) * μ.real (A t)) :=
      sum_sqrt_typeMass_le _ (fun t ↦ by positivity)
    _ = Real.sqrt (2 * (n : ℝ) * Fintype.card T * ε) := by
      rw [← Finset.mul_sum, hε]
      congr 1
      ring

end OTSelector.Reconstruction
