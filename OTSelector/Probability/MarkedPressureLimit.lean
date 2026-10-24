import OTSelector.Probability.MarkedPressureBound
import OTSelector.Probability.MarkedBlockComparison
import OTSelector.Probability.MarkedPressureScale

/-!
# The scale-normalized marked pressure and its two-sided bound

The pressure comparison is naturally expressed in terms of the real scale `R`
with intensity `R ^ q`; the normalized quantity is `P R / R ^ q`.  This module
records the scale-normalized pressure, the lower bound coming from the shifted
nonnegative edge cost, and the resulting two-sided bound and Lipschitz
properties.
-/

open scoped BigOperators NNReal
open MeasureTheory

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The scale-normalized marked pressure: intensity `R ^ q`, normalized by
`R ^ q`.  At nonpositive scales it is set to zero. -/
noncomputable def markedScalePressure (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (R t : ℝ) : ℝ :=
  if 0 < R then markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t / R ^ q else 0

/-- The value of the scale-normalized pressure at a positive scale. -/
theorem markedScalePressure_of_pos (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {R t : ℝ} (hR : 0 < R) :
    markedScalePressure q A B α β kin g R t =
      markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t / R ^ q := by
  unfold markedScalePressure
  rw [if_pos hR]

/-- The maximum-cardinality value of a nonnegative cost matrix is nonnegative. -/
theorem maxCardValue_nonneg {m n : ℕ} {c : Fin m → Fin n → ℝ}
    (h : ∀ i j, 0 ≤ c i j) : 0 ≤ PartialMatching.maxCardValue c := by
  exact PartialMatching.maxCardValue_nonneg h

/-- The shifted marked value is nonnegative when the kinetic kernel is. -/
theorem cloudValueNat_mMarkedShiftedEdge_nonneg (q : ℕ) {r t G : ℝ} (hr : 0 ≤ r)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hgb : ∀ a b, |g a b| ≤ G)
    (ω : TwoMarkedCloudSpace q A B) :
    0 ≤ cloudValueNat (mMarkedShiftedEdge (A := A) (B := B) q r kin g t G)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω := by
  classical
  apply maxCardValue_nonneg
  intro i j
  unfold mMarkedShiftedEdge
  rw [if_pos ⟨i.isLt, j.isLt⟩]
  have hk : 0 ≤ mKineticCost q r kin ω (i : ℕ) (j : ℕ) := by
    unfold mKineticCost
    exact mul_nonneg (Real.rpow_nonneg hr _) (hkin_nonneg _ _ _)
  have hpl := probe_mul_le (A := A) (B := B) t (g := g) (G := G) hgb
    (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
  have hneg2 : -(t * mProbe g ω (i : ℕ) (j : ℕ)) ≤ |t| * G := by
    have h' := probe_mul_le (A := A) (B := B) (-t) (g := g) (G := G) hgb
      (mSourceMark ω (i : ℕ)) (mTargetMark ω (j : ℕ))
    simpa only [mProbe, neg_mul, abs_neg] using h'
  linarith

/-- The expectation of the matched cardinality is at most the intensity. -/
theorem integral_mMinCount_le (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) :
    ∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
      ∂(twoMarkedCloudLaw (q := q) A B α β r) ≤ (r : ℝ) := by
  have hmin := integrable_mMinCount (q := q) α β r
  have hsrc := integrable_mSourceCount (q := q) α β r
  have hle : ∀ ω : TwoMarkedCloudSpace q A B,
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) ≤ ((mSourceCount ω : ℕ) : ℝ) := by
    intro ω
    exact_mod_cast min_le_left _ _
  calc ∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
        ∂(twoMarkedCloudLaw (q := q) A B α β r)
      ≤ ∫ ω, ((mSourceCount ω : ℕ) : ℝ) ∂(twoMarkedCloudLaw (q := q) A B α β r) :=
        integral_mono hmin hsrc hle
    _ = (r : ℝ) := by
        rw [integral_mSourceCount_eq]

/-- Lower bound on the marked pressure from the shifted nonnegative cost. -/
theorem markedPressure_lower_bound (q : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (r : ℝ≥0) {C G t : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    -((r : ℝ) * (|t| * G)) ≤ markedPressure q A B α β r kin g t := by
  classical
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  -- Pointwise nonnegativity of the shifted value.
  have hnn : ∀ ω, 0 ≤ cloudValueNat
      (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω :=
    fun ω => cloudValueNat_mMarkedShiftedEdge_nonneg q hr0 hkin_nonneg hgb ω
  have hint_shift : Integrable (fun ω => cloudValueNat
      (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω)
      (twoMarkedCloudLaw (q := q) A B α β r) :=
    integrable_mMarkedShiftedValue q α β r hC0 hG0 hkin hkin_bound hg hgb t
  have hmin := integrable_mMinCount (q := q) α β r
  have htil := integrable_markedTilted (q := q) α β r hr0 hC0 hG0 hkin hkin_bound hg hgb t
  -- Integral identity for the shifted value.
  have hpoint : ∀ ω, cloudValueNat
      (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω =
      markedTilted (q := q) (r := (r : ℝ)) kin g t ω +
        ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * (|t| * G) :=
    fun ω => cloudValueNat_mMarkedShiftedEdge q (r : ℝ) kin g t G ω
  have hIntEq : ∫ ω, cloudValueNat
      (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω
      ∂(twoMarkedCloudLaw (q := q) A B α β r) =
      markedPressure q A B α β r kin g t +
        (∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
          ∂(twoMarkedCloudLaw (q := q) A B α β r)) * (|t| * G) := by
    rw [show (∫ ω, cloudValueNat
        (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
        (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω
        ∂(twoMarkedCloudLaw (q := q) A B α β r)) =
        ∫ ω, (markedTilted (q := q) (r := (r : ℝ)) kin g t ω +
          ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) * (|t| * G))
          ∂(twoMarkedCloudLaw (q := q) A B α β r) from by
      apply integral_congr_ae
      filter_upwards with ω
      exact hpoint ω]
    rw [integral_add htil (hmin.mul_const _), integral_mul_const]
    rfl
  have hnonneg_int : 0 ≤ ∫ ω, cloudValueNat
      (mMarkedShiftedEdge (A := A) (B := B) q (r : ℝ) kin g t G)
      (mSourceCount (A := A) (B := B)) (mTargetCount (A := A) (B := B)) ω
      ∂(twoMarkedCloudLaw (q := q) A B α β r) :=
    integral_nonneg (fun ω => hnn ω)
  have hminle := integral_mMinCount_le q α β r
  have hs : (0 : ℝ) ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
  rw [hIntEq] at hnonneg_int
  nlinarith [hnonneg_int, hminle, hs, mul_nonneg hr0 hs]

end OTSelector.Probability

namespace OTSelector.Probability

/-- Two-sided sharp bound for the marked pressure at intensities at least one. -/
theorem exists_abs_markedPressure_bound (q : ℕ) (hq : 4 < q)
    (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] :
    ∃ Kq : ℝ, 0 ≤ Kq ∧
      ∀ (C G t : ℝ), 0 ≤ C → 0 ≤ G →
      ∀ (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ),
        Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)) →
        Measurable (Function.uncurry g) →
        (∀ a b v, 0 ≤ kin a b v) →
        (∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2) →
        (∀ a b, |g a b| ≤ G) →
        ∀ r : ℝ≥0, 1 ≤ r →
          |markedPressure q A B α β r kin g t| ≤ Kq * (C + |t| * G) * (r : ℝ) := by
  obtain ⟨Cq, hCq0, hCq⟩ := exists_markedPressure_bound (q := q) hq A B α β
  refine ⟨max Cq 1, le_max_of_le_left hCq0, ?_⟩
  intro C G t hC0 hG0 kin g hkin hg hkin_nonneg hkin_bound hgb r hr1
  have hupper := hCq C G t hC0 hG0 kin g hkin hg hkin_nonneg hkin_bound hgb r hr1
  have hlower := markedPressure_lower_bound (q := q) α β r hC0 hG0 hkin hkin_nonneg
    hkin_bound hg hgb (t := t)
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  have hs0 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
  have hCG : 0 ≤ C + |t| * G := add_nonneg hC0 hs0
  have h1 : (0 : ℝ) ≤ (C + |t| * G) * (r : ℝ) := mul_nonneg hCG hr0
  rw [abs_le]
  constructor
  · -- lower bound
    have h : -((r : ℝ) * (|t| * G)) ≥ -(1 * ((C + |t| * G) * (r : ℝ))) := by
      have : (|t| * G) ≤ C + |t| * G := le_add_of_nonneg_left hC0
      nlinarith
    nlinarith [hlower, h, le_max_right Cq 1]
  · -- upper bound
    have hle : Cq * (C + |t| * G) * (r : ℝ) ≤ max Cq 1 * (C + |t| * G) * (r : ℝ) := by
      have hmax : Cq ≤ max Cq 1 := le_max_left _ _
      nlinarith
    linarith


/-! ## Concavity, Lipschitz and boundedness of the scale pressure -/

/-- Concavity of the scale-normalized pressure in the tilt. -/
theorem markedScalePressure_concaveOn (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (R : ℝ) :
    ConcaveOn ℝ Set.univ (fun t => markedScalePressure q A B α β kin g R t) := by
  classical
  by_cases hR : 0 < R
  · have hbase := concaveOn_markedPressure (q := q) α β (Real.toNNReal (R ^ q))
      (by positivity) hC0 hG0 hkin hkin_bound hg hgb
    have hc : (0 : ℝ) ≤ (R ^ q)⁻¹ := inv_nonneg.mpr (pow_nonneg hR.le q)
    have hsmul := hbase.smul hc
    refine hsmul.congr ?_
    intro t _
    change (R ^ q)⁻¹ * markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t =
      markedScalePressure q A B α β kin g R t
    rw [markedScalePressure_of_pos q α β hR]
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  · have hR' : ¬ 0 < R := hR
    have hzero : (fun t => markedScalePressure q A B α β kin g R t) = fun _ => 0 := by
      funext t
      unfold markedScalePressure
      rw [if_neg hR']
    rw [hzero]
    exact concaveOn_const 0 convex_univ

/-- The scale-normalized pressure is `G`-Lipschitz in the tilt. -/
theorem markedScalePressure_lipschitz (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (R t u : ℝ) :
    |markedScalePressure q A B α β kin g R t -
      markedScalePressure q A B α β kin g R u| ≤ G * |t - u| := by
  classical
  by_cases hR : 0 < R
  · rw [markedScalePressure_of_pos q α β hR, markedScalePressure_of_pos q α β hR,
      ← sub_div, abs_div, abs_of_pos (pow_pos hR q)]
    have hP := abs_markedPressure_sub_le (q := q) α β (Real.toNNReal (R ^ q))
      (C := C) (G := G) (by positivity) hC0 hG0
      hkin hkin_bound hg hgb t u
    have hmin := integral_mMinCount_le q α β (Real.toNNReal (R ^ q))
    have hrcoe : ((Real.toNNReal (R ^ q) : ℝ≥0) : ℝ) = R ^ q :=
      Real.coe_toNNReal _ (pow_nonneg hR.le q)
    have hGtu : 0 ≤ G * |t - u| := mul_nonneg hG0 (abs_nonneg _)
    have hP' : |markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t -
        markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g u| ≤
        (R ^ q) * (G * |t - u|) := by
      refine hP.trans ?_
      exact mul_le_mul_of_nonneg_right (by simpa only [hrcoe] using hmin) hGtu
    calc |markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t -
          markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g u| / R ^ q
        ≤ ((R ^ q) * (G * |t - u|)) / R ^ q :=
          div_le_div_of_nonneg_right hP' (pow_pos hR q).le
      _ = G * |t - u| := by field_simp
  · have hR' : ¬ 0 < R := hR
    unfold markedScalePressure
    rw [if_neg hR', if_neg hR']
    simp only [sub_self, abs_zero]
    exact mul_nonneg hG0 (abs_nonneg _)

/-- Uniform boundedness of the scale pressure at scales at least one. -/
theorem exists_markedScalePressure_bound (q : ℕ) (hq : 4 < q)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    ∀ t : ℝ, ∃ Bnd : ℝ, ∀ R : ℝ, 1 ≤ R →
      |markedScalePressure q A B α β kin g R t| ≤ Bnd := by
  classical
  obtain ⟨Kq, hKq0, hKq⟩ := exists_abs_markedPressure_bound (q := q) hq A B α β
  intro t
  refine ⟨Kq * (C + |t| * G), ?_⟩
  intro R hR1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  rw [markedScalePressure_of_pos q α β hR, abs_div, abs_of_pos (pow_pos hR q)]
  have hr1 : (1 : ℝ≥0) ≤ Real.toNNReal (R ^ q) := by
    rw [← Real.toNNReal_one]
    exact (Real.toNNReal_le_toNNReal_iff (pow_nonneg hR.le q)).mpr (by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR1 q)
  have hbound := hKq C G t hC0 hG0 kin g hkin hg hkin_nonneg hkin_bound hgb
    (Real.toNNReal (R ^ q)) hr1
  have hrcoe : ((Real.toNNReal (R ^ q) : ℝ≥0) : ℝ) = R ^ q :=
    Real.coe_toNNReal _ (pow_nonneg hR.le q)
  have hCG : 0 ≤ C + |t| * G := add_nonneg hC0 (mul_nonneg (abs_nonneg t) hG0)
  have hden : 0 < R ^ q := pow_pos hR q
  rw [hrcoe] at hbound
  calc |markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t| / R ^ q
      ≤ (Kq * (C + |t| * G) * R ^ q) / R ^ q :=
        div_le_div_of_nonneg_right hbound hden.le
    _ = Kq * (C + |t| * G) := by field_simp

/-- Continuity of the scale pressure at positive scales. -/
theorem continuousAt_markedScalePressure (q : ℕ) {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (fun R => markedScalePressure q A B α β kin g R t) L := by
  classical
  have hpos : (0 : ℝ≥0) < Real.toNNReal (L ^ q) := by
    rw [Real.toNNReal_pos]
    exact pow_pos hL q
  have hcontρ : ContinuousAt
      (fun r : ℝ≥0 => markedPressure q A B α β r kin g t / (r : ℝ))
      (Real.toNNReal (L ^ q)) :=
    continuousAt_markedPressure_scale (q := q) (t := t) A B α β hC0 hG0 hkin
      hkin_bound hg hgb hpos
  have hto : ContinuousAt (fun R : ℝ => Real.toNNReal (R ^ q)) L :=
    (continuous_real_toNNReal.comp (continuous_pow q)).continuousAt
  have hcomp : ContinuousAt
      ((fun r : ℝ≥0 => markedPressure q A B α β r kin g t / (r : ℝ)) ∘
        (fun R : ℝ => Real.toNNReal (R ^ q))) L :=
    ContinuousAt.comp (f := fun R : ℝ => Real.toNNReal (R ^ q)) hcontρ hto
  refine hcomp.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hL] with R hR
  rw [Function.comp_apply, markedScalePressure_of_pos q α β hR,
    Real.coe_toNNReal _ (pow_nonneg hR.le q)]

end OTSelector.Probability
