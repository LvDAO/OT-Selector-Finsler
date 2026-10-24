import OTSelector.Finite.MaxCardValueRelativeStability
import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.PoissonCountDiscrepancy
import OTSelector.Probability.MarkedPressureLimit

/-!
# Relative stability of the marked pressure under kernel perturbations

If the nonnegative kinetic kernel `kin'` differs from `kin` by at most a
relative `delta <= 1`, the tilted marked value changes by at most `delta` times
its size plus the probe shift `|t| G` per matched pair.  Integrating over the
Poissonized marked cloud gives the corresponding pressure stability, with the
mean pair count bounded by the intensity.

This is the analytic mechanism by which a frozen physical kernel, known to be a
relative `O(delta)` perturbation of the ideal local kernel, changes the local
marked pressure by only a relative `O(delta)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- **Pointwise relative kernel stability of the tilted marked value.** -/
theorem abs_markedTilted_sub_le_of_relative_kernel
    (q : ℕ) {r t δ G : ℝ} (hr : 0 ≤ r)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hG0 : 0 ≤ G)
    {kin kin' : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : ∀ a b v, 0 ≤ kin a b v)
    (hrel : ∀ a b v, |kin' a b v - kin a b v| ≤ δ * kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    |markedTilted q r kin' g t ω - markedTilted q r kin g t ω| ≤
      δ * (markedTilted q r kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * |t| * G) := by
  classical
  have hrpow0 : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  let cs : A × B → B → (Fin q → ℝ) → ℝ := fun p _ v => kin p.1 p.2 v
  let c : Fin (mSourceCount ω) → Fin (mTargetCount ω) → ℝ :=
    fun i j => r ^ (2 / (q : ℝ)) *
      kin (mSourceMark ω i) (mTargetMark ω j)
        (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))
  let c' : Fin (mSourceCount ω) → Fin (mTargetCount ω) → ℝ :=
    fun i j => r ^ (2 / (q : ℝ)) *
      kin' (mSourceMark ω i) (mTargetMark ω j)
        (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))
  let pr : Fin (mSourceCount ω) → Fin (mTargetCount ω) → ℝ :=
    fun i j => mProbe g ω (i : ℕ) (j : ℕ)
  have hc0 : ∀ i j, 0 ≤ c i j := by
    intro i j
    exact mul_nonneg hrpow0 (hkin _ _ _)
  have hpr : ∀ i j, |pr i j| ≤ G := by
    intro i j
    exact abs_mProbe_le q hgb ω (i : ℕ) (j : ℕ)
  have hcrel : ∀ i j, |c' i j - c i j| ≤ δ * c i j := by
    intro i j
    have h1 := hrel (mSourceMark ω i) (mTargetMark ω j)
      (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))
    have h2 : r ^ (2 / (q : ℝ)) * |kin' (mSourceMark ω i) (mTargetMark ω j)
        (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) -
          kin (mSourceMark ω i) (mTargetMark ω j)
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| ≤
        r ^ (2 / (q : ℝ)) * (δ * kin (mSourceMark ω i) (mTargetMark ω j)
          (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))) :=
      mul_le_mul_of_nonneg_left h1 hrpow0
    calc |c' i j - c i j| = r ^ (2 / (q : ℝ)) *
          |kin' (mSourceMark ω i) (mTargetMark ω j)
              (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) -
            kin (mSourceMark ω i) (mTargetMark ω j)
              (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| := by
          rw [show c' i j - c i j = r ^ (2 / (q : ℝ)) *
              (kin' (mSourceMark ω i) (mTargetMark ω j)
                  (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j)) -
                kin (mSourceMark ω i) (mTargetMark ω j)
                  (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))) by ring]
          rw [abs_mul, abs_of_nonneg hrpow0]
      _ ≤ r ^ (2 / (q : ℝ)) * (δ * kin (mSourceMark ω i) (mTargetMark ω j)
            (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))) := h2
      _ = δ * c i j := by ring
  have hmain := PartialMatching.abs_maxCardValue_perturbed_sub_le_of_relative_kinetic
    (c := c) (c' := c') (g := pr) (t := t) (G := G) (δ := δ)
    hδ0 hδ1 hG0 hc0 hpr hcrel
  simpa only [markedTilted, tiltedCloudValue, mKineticCost, mProbe, c, c', pr,
    Nat.cast_min] using hmain

/-- The source Poisson count has mean equal to the intensity. -/
theorem integral_mSourceCount (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω : TwoMarkedCloudSpace q A B, ((mSourceCount ω : ℕ) : ℝ)
      ∂(twoMarkedCloudLaw (q := q) A B α β r) = (r : ℝ) := by
  haveI hA : IsProbabilityMeasure (markedSeqLaw (q := q) A α) :=
    isProbabilityMeasure_markedSeqLaw (q := q) A α
  haveI hB : IsProbabilityMeasure (markedSeqLaw (q := q) B β) :=
    isProbabilityMeasure_markedSeqLaw (q := q) B β
  have hInt := integrable_mSourceCount (q := q) α β r
  have hIntA : Integrable (fun a : MarkedCloudSpace q A => ((a.1 : ℕ) : ℝ))
      (markedPoissonLaw (q := q) A α r) := by
    unfold markedPoissonLaw
    exact (integrable_id_poissonMeasure r).comp_fst _
  rw [show twoMarkedCloudLaw (q := q) A B α β r =
      (markedPoissonLaw (q := q) A α r).prod (markedPoissonLaw (q := q) B β r) from rfl,
    integral_prod _ hInt]
  change (∫ a : MarkedCloudSpace q A,
      (∫ _b : MarkedCloudSpace q B, ((a.1 : ℕ) : ℝ) ∂
        (markedPoissonLaw (q := q) B β r)) ∂(markedPoissonLaw (q := q) A α r)) = (r : ℝ)
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [show markedPoissonLaw (q := q) A α r =
      (poissonMeasure r).prod (markedSeqLaw (q := q) A α) from rfl, integral_prod _ hIntA]
  change (∫ n : ℕ, (∫ _s : ℕ → (Fin q → ℝ) × A, (n : ℝ) ∂
      (markedSeqLaw (q := q) A α)) ∂(poissonMeasure r)) = (r : ℝ)
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact integral_id_poissonMeasure r


/-- **Relative kernel stability of the marked pressure.**  A relative `delta`
perturbation of the nonnegative kinetic kernel changes the marked pressure by at
most `delta` times its size plus the probe shift times the intensity. -/
theorem abs_markedPressure_sub_le_of_relative_kernel
    (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) {t δ C G : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin kin' : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_meas : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin'_meas : Measurable (Function.uncurry (fun p : A × B => kin' p.1 p.2)))
    (hkin : ∀ a b v, 0 ≤ kin a b v)
    (hrel : ∀ a b v, |kin' a b v - kin a b v| ≤ δ * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    |markedPressure q A B α β r kin' g t - markedPressure q A B α β r kin g t| ≤
      δ * (markedPressure q A B α β r kin g t + |t| * G * (r : ℝ)) := by
  classical
  have hlaw : IsProbabilityMeasure (twoMarkedCloudLaw (q := q) A B α β r) := inferInstance
  -- Integrability of both tilted values and of the minimal count.
  have hkin'_bound : ∀ a b v, |kin' a b v| ≤ (2 * C) * ∑ l, v l ^ 2 := by
    intro a b v
    have h1 := hrel a b v
    have h2 := hkin_bound a b v
    have h3 := hkin a b v
    have hle : kin a b v ≤ C * ∑ l, v l ^ 2 := le_of_abs_le h2
    have hδkin : δ * kin a b v ≤ C * ∑ l, v l ^ 2 := by
      calc δ * kin a b v ≤ 1 * kin a b v := mul_le_mul_of_nonneg_right hδ1 h3
        _ = kin a b v := one_mul _
        _ ≤ C * ∑ l, v l ^ 2 := hle
    calc |kin' a b v| = |kin a b v + (kin' a b v - kin a b v)| := by ring_nf
      _ ≤ |kin a b v| + |kin' a b v - kin a b v| := abs_add_le _ _
      _ ≤ C * ∑ l, v l ^ 2 + δ * kin a b v := add_le_add h2 h1
      _ ≤ C * ∑ l, v l ^ 2 + C * ∑ l, v l ^ 2 := add_le_add (le_refl _) hδkin
      _ = 2 * C * ∑ l, v l ^ 2 := by ring
  have hInt : Integrable (markedTilted (q := q) (r := (r : ℝ)) kin g t)
      (twoMarkedCloudLaw (q := q) A B α β r) :=
    integrable_markedTilted (q := q) α β r r.coe_nonneg hC0 hG0
      hkin_meas hkin_bound hg hgb t
  have hInt' : Integrable (markedTilted (q := q) (r := (r : ℝ)) kin' g t)
      (twoMarkedCloudLaw (q := q) A B α β r) :=
    integrable_markedTilted (q := q) α β r r.coe_nonneg
      (mul_nonneg (by norm_num) hC0) hG0 hkin'_meas hkin'_bound hg hgb t
  have hMin : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ))
      (twoMarkedCloudLaw (q := q) A B α β r) :=
    integrable_mMinCount (q := q) α β r
  -- Pointwise bound.
  have hpt : ∀ᵐ ω ∂(twoMarkedCloudLaw (q := q) A B α β r),
      |markedTilted (q := q) (r := (r : ℝ)) kin' g t ω -
        markedTilted (q := q) (r := (r : ℝ)) kin g t ω| ≤
      δ * (markedTilted (q := q) (r := (r : ℝ)) kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * |t| * G) :=
    Filter.Eventually.of_forall fun ω =>
      abs_markedTilted_sub_le_of_relative_kernel (t := t) q r.coe_nonneg hδ0 hδ1 hG0
        hkin hrel hgb t ω
  -- The mean minimal count is at most the intensity.
  have hminMean : (∫ ω : TwoMarkedCloudSpace q A B,
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)) ≤ (r : ℝ) := by
    have hsrcInt := integrable_mSourceCount (q := q) α β r
    have hmono : (∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)) ≤
        ∫ ω, ((mSourceCount ω : ℕ) : ℝ) ∂(twoMarkedCloudLaw (q := q) A B α β r) :=
      integral_mono hMin hsrcInt fun ω => by
        exact Nat.cast_le.mpr (Nat.min_le_left (mSourceCount ω) (mTargetCount ω))
    rwa [integral_mSourceCount] at hmono
  have hMinK : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * |t| * G)
      (twoMarkedCloudLaw (q := q) A B α β r) := by
    simpa only [mul_assoc] using hMin.mul_const (|t| * G)
  -- Integrability of the right-hand side.
  have hRhs : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      δ * (markedTilted (q := q) (r := (r : ℝ)) kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * |t| * G))
      (twoMarkedCloudLaw (q := q) A B α β r) := by
    have h1 : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        markedTilted (q := q) (r := (r : ℝ)) kin g t ω +
          ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * |t| * G)
        (twoMarkedCloudLaw (q := q) A B α β r) := by
      exact hInt.add hMinK
    exact h1.const_mul δ
  have habsInt : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      |markedTilted (q := q) (r := (r : ℝ)) kin' g t ω -
        markedTilted (q := q) (r := (r : ℝ)) kin g t ω|)
      (twoMarkedCloudLaw (q := q) A B α β r) :=
    (hInt'.sub hInt).abs
  have hsub : |markedPressure q A B α β r kin' g t -
      markedPressure q A B α β r kin g t| =
      |∫ ω, (markedTilted (q := q) (r := (r : ℝ)) kin' g t ω -
        markedTilted (q := q) (r := (r : ℝ)) kin g t ω)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)| := by
    unfold markedPressure
    rw [integral_sub hInt' hInt]
  calc |markedPressure q A B α β r kin' g t - markedPressure q A B α β r kin g t|
      = |∫ ω, (markedTilted (q := q) (r := (r : ℝ)) kin' g t ω -
          markedTilted (q := q) (r := (r : ℝ)) kin g t ω)
          ∂(twoMarkedCloudLaw (q := q) A B α β r)| := hsub
    _ ≤ ∫ ω, |markedTilted (q := q) (r := (r : ℝ)) kin' g t ω -
          markedTilted (q := q) (r := (r : ℝ)) kin g t ω|
          ∂(twoMarkedCloudLaw (q := q) A B α β r) := abs_integral_le_integral_abs
    _ ≤ ∫ ω, δ * (markedTilted (q := q) (r := (r : ℝ)) kin g t ω +
          ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * |t| * G)
          ∂(twoMarkedCloudLaw (q := q) A B α β r) :=
        integral_mono_ae habsInt hRhs hpt
    _ = δ * (markedPressure q A B α β r kin g t + |t| * G *
          (∫ ω : TwoMarkedCloudSpace q A B,
            ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
              ∂(twoMarkedCloudLaw (q := q) A B α β r))) := by
        rw [integral_const_mul]
        congr 1
        rw [integral_add hInt hMinK, integral_mul_const, integral_mul_const]
        unfold markedPressure
        ring
    _ ≤ δ * (markedPressure q A B α β r kin g t + |t| * G * (r : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hδ0
        have hGt : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
        linarith [mul_le_mul_of_nonneg_left hminMean hGt]

/-- **Relative kernel stability of the scale pressure.**  The relative bound is
uniform in the scale. -/
theorem abs_markedScalePressure_sub_le_of_relative_kernel
    (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {R t δ C G : ℝ}
    (hR : 0 < R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin kin' : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_meas : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin'_meas : Measurable (Function.uncurry (fun p : A × B => kin' p.1 p.2)))
    (hkin : ∀ a b v, 0 ≤ kin a b v)
    (hrel : ∀ a b v, |kin' a b v - kin a b v| ≤ δ * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    |markedScalePressure q A B α β kin' g R t -
        markedScalePressure q A B α β kin g R t| ≤
      δ * (markedScalePressure q A B α β kin g R t + |t| * G) := by
  have hRq : (0 : ℝ) < R ^ q := pow_pos hR q
  have hcoer : ((Real.toNNReal (R ^ q) : ℝ≥0) : ℝ) = R ^ q :=
    Real.coe_toNNReal _ hRq.le
  rw [markedScalePressure_of_pos q α β hR, markedScalePressure_of_pos q α β hR]
  have h := abs_markedPressure_sub_le_of_relative_kernel (q := q) α β
    (Real.toNNReal (R ^ q)) (t := t) (δ := δ) (C := C) (G := G)
    hδ0 hδ1 hC0 hG0 hkin_meas hkin_bound hkin'_meas hkin hrel hg hgb
  rw [hcoer] at h
  have hdiv : |markedPressure q A B α β (Real.toNNReal (R ^ q)) kin' g t / R ^ q -
      markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t / R ^ q| =
      |markedPressure q A B α β (Real.toNNReal (R ^ q)) kin' g t -
        markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t| / R ^ q := by
    rw [div_sub_div_same, abs_div, abs_of_pos hRq]
  rw [hdiv]
  have h2 : |markedPressure q A B α β (Real.toNNReal (R ^ q)) kin' g t -
        markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t| / R ^ q ≤
      δ * (markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t + |t| * G * R ^ q) /
        R ^ q := by
    exact div_le_div_of_nonneg_right h hRq.le
  refine h2.trans_eq ?_
  field_simp

/-- **Relative kernel stability of the pressure limit.**  If both scale
pressures converge, their limits inherit the relative kernel bound. -/
theorem abs_pressureLimit_sub_le_of_relative_kernel
    (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {t δ C G : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin kin' : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_meas : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin'_meas : Measurable (Function.uncurry (fun p : A × B => kin' p.1 p.2)))
    (hkin : ∀ a b v, 0 ≤ kin a b v)
    (hrel : ∀ a b v, |kin' a b v - kin a b v| ≤ δ * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p p' : ℝ}
    (hp : Tendsto (fun R => markedScalePressure q A B α β kin g R t) atTop (𝓝 p))
    (hp' : Tendsto (fun R => markedScalePressure q A B α β kin' g R t) atTop (𝓝 p')) :
    |p' - p| ≤ δ * (p + |t| * G) := by
  have hlim : Tendsto (fun R : ℝ =>
      |markedScalePressure q A B α β kin' g R t -
        markedScalePressure q A B α β kin g R t|) atTop (𝓝 |p' - p|) :=
    (hp'.sub hp).abs
  have hbound : Tendsto (fun R : ℝ =>
      δ * (markedScalePressure q A B α β kin g R t + |t| * G)) atTop
      (𝓝 (δ * (p + |t| * G))) :=
    ((hp.add_const (|t| * G)).const_mul δ)
  refine le_of_tendsto_of_tendsto hlim hbound ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact abs_markedScalePressure_sub_le_of_relative_kernel (q := q) α β
    hR hδ0 hδ1 hC0 hG0 hkin_meas hkin_bound hkin'_meas hkin hrel hg hgb

end OTSelector.Probability
