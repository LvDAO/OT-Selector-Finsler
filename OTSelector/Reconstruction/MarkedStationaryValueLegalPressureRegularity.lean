import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity
import OTSelector.Reconstruction.MarkedStationaryValueLegalCloud

/-!
# Regularity of the actual forward legal Poisson pressure

The graph remains the original strict clock graph. Bounds are required only on
legal edges; zero extension is used solely for domination and measurability.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Zero extension of a kinetic kernel off the original forward mark domain. -/
def forwardKinetic (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (a : A) (b : B) (v : Fin q → ℝ) : ℝ :=
  if sourceClock a < targetClock b then kin a b v else 0

/-- Zero extension of a probe off the original forward mark domain. -/
def forwardProbe (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (probe : A → B → ℝ) (a : A) (b : B) : ℝ :=
  if sourceClock a < targetClock b then probe a b else 0

/-- Forward extension preserves joint kernel measurability. -/
theorem measurable_forwardKinetic (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2))) :
    Measurable (Function.uncurry (fun p : A × B ↦
      forwardKinetic q sourceClock targetClock kin p.1 p.2)) := by
  apply Measurable.ite
  · exact measurableSet_lt (hs.comp (measurable_fst.comp measurable_fst))
      (ht.comp (measurable_snd.comp measurable_fst))
  · exact hk
  · exact measurable_const

/-- Forward extension preserves joint probe measurability. -/
theorem measurable_forwardProbe {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe)) :
    Measurable (Function.uncurry (forwardProbe sourceClock targetClock probe)) :=
  hp.ite (measurableSet_lt (hs.comp measurable_fst) (ht.comp measurable_snd)) measurable_const

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Quadratic domination is needed only on forward mark pairs. -/
theorem abs_forwardKinetic_le (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hk : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2) :
    ∀ a b v, |forwardKinetic q sourceClock targetClock kin a b v| ≤ C * ∑ l, v l ^ 2 := by
  intro a b v
  by_cases hab : sourceClock a < targetClock b
  · simpa [forwardKinetic, hab] using hk a b hab v
  · simp only [forwardKinetic, hab, ↓reduceIte, abs_zero]
    exact mul_nonneg hC (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Probe domination is needed only on forward mark pairs. -/
theorem abs_forwardProbe_le (sourceClock : A → ℝ) (targetClock : B → ℝ)
    {probe : A → B → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hp : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G) :
    ∀ a b, |forwardProbe sourceClock targetClock probe a b| ≤ G := by
  intro a b
  by_cases hab : sourceClock a < targetClock b
  · simpa [forwardProbe, hab] using hp a b hab
  · simpa [forwardProbe, hab] using hG

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The literal finite legal value ignores this zero extension. -/
theorem legalMarkedTilted_forward (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    legalMarkedTilted q sourceClock targetClock r
      (forwardKinetic q sourceClock targetClock kin)
      (forwardProbe sourceClock targetClock probe) t ω =
        legalMarkedTilted q sourceClock targetClock r kin probe t ω := by
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j hij
  have hforward : sourceClock (mSourceMark ω i) < targetClock (mTargetMark ω j) := by
    simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and] using hij
  simp only [mKineticCost, mProbe, forwardKinetic, forwardProbe, hforward, ↓reduceIte]

/-- Actual legal finite pressures are integrable using bounds only on forward pairs. -/
theorem integrable_legalMarkedTilted_of_forward (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G) (t : ℝ) :
    Integrable (legalMarkedTilted q sourceClock targetClock r kin probe t)
      (twoMarkedCloudLaw q A B α β r) := by
  have hi := integrable_legalMarkedTilted q hs ht α β r hC hG
    (measurable_forwardKinetic q hs ht hk) (abs_forwardKinetic_le q _ _ hC hkb)
    (measurable_forwardProbe hs ht hp) (abs_forwardProbe_le _ _ hG hpb) t
  have heq : legalMarkedTilted q sourceClock targetClock r
      (forwardKinetic q sourceClock targetClock kin)
      (forwardProbe sourceClock targetClock probe) t =
        legalMarkedTilted q sourceClock targetClock r kin probe t :=
    funext (legalMarkedTilted_forward q sourceClock targetClock r kin probe t)
  rw [heq] at hi
  exact hi

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The actual finite legal value is Lipschitz with its own maximum cardinality. -/
theorem abs_legalMarkedTilted_sub_le (q : ℕ)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    {G : ℝ} (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G)
    (r t u : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    |legalMarkedTilted q sourceClock targetClock r kin probe t ω -
      legalMarkedTilted q sourceClock targetClock r kin probe u ω| ≤
        (PartialMatching.legalMaximumCard
          (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω) : ℝ) *
            (G * |t - u|) := by
  apply PartialMatching.abs_legalMaximumValue_tilt_sub_le
  intro i j hij
  apply hpb
  simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and] using hij

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Concavity of the actual legal finite value, without a Hall-feasibility premise. -/
theorem concaveOn_legalMarkedTilted (q : ℕ)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    (r : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    ConcaveOn ℝ univ (fun t ↦ legalMarkedTilted q sourceClock targetClock r kin probe t ω) :=
  PartialMatching.concaveOn_legalMaximumValue_tilt _ _ _

/-- Concavity passes to the actual original legal Poisson pressure. -/
theorem concaveOn_legalMarkedPressure (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G) :
    ConcaveOn ℝ univ (legalMarkedPressure q sourceClock targetClock α β r kin probe) := by
  let V := legalMarkedTilted q sourceClock targetClock r kin probe
  have hI (t : ℝ) : Integrable (V t) (twoMarkedCloudLaw q A B α β r) :=
    integrable_legalMarkedTilted_of_forward q hs ht α β r hC hG hk hkb hp hpb t
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  have hcomb : Integrable (fun ω ↦ a * V t ω + b * V u ω)
      (twoMarkedCloudLaw q A B α β r) := ((hI t).const_mul a).add ((hI u).const_mul b)
  have hpt (ω) : a * V t ω + b * V u ω ≤ V (a * t + b * u) ω := by
    exact (concaveOn_legalMarkedTilted q sourceClock targetClock kin probe r ω).2
      (mem_univ t) (mem_univ u) ha hb hab
  have h := integral_mono hcomb (hI (a * t + b * u)) hpt
  rw [integral_add ((hI t).const_mul a) ((hI u).const_mul b),
    integral_const_mul, integral_const_mul] at h
  simpa only [legalMarkedPressure, smul_eq_mul] using h

/-- The actual legal pressure has a Lipschitz constant controlled by the
original expected source count, including Hall-deficient realizations. -/
theorem abs_legalMarkedPressure_sub_le (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G) (t u : ℝ) :
    |legalMarkedPressure q sourceClock targetClock α β r kin probe t -
      legalMarkedPressure q sourceClock targetClock α β r kin probe u| ≤
        (r : ℝ) * (G * |t - u|) := by
  let V := legalMarkedTilted q sourceClock targetClock r kin probe
  have hI (t : ℝ) : Integrable (V t) (twoMarkedCloudLaw q A B α β r) :=
    integrable_legalMarkedTilted_of_forward q hs ht α β r hC hG hk hkb hp hpb t
  have hpt (ω) : |V t ω - V u ω| ≤ (mSourceCount ω : ℝ) * (G * |t - u|) := by
    apply (abs_legalMarkedTilted_sub_le q sourceClock targetClock kin probe hpb r t u ω).trans
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _)))
      (mul_nonneg hG (abs_nonneg _))
  calc |legalMarkedPressure q sourceClock targetClock α β r kin probe t -
        legalMarkedPressure q sourceClock targetClock α β r kin probe u|
      = |∫ ω, V t ω - V u ω ∂twoMarkedCloudLaw q A B α β r| := by
          rw [integral_sub (hI t) (hI u)]; rfl
    _ ≤ ∫ ω, |V t ω - V u ω| ∂twoMarkedCloudLaw q A B α β r :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, (mSourceCount ω : ℝ) * (G * |t - u|)
        ∂twoMarkedCloudLaw q A B α β r :=
      integral_mono ((hI t).sub (hI u)).abs ((integrable_mSourceCount q α β r).mul_const _) hpt
    _ = (r : ℝ) * (G * |t - u|) := by
      rw [integral_mul_const, integral_mSourceCount_eq]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Nonnegative kinetic energy on legal edges gives a source-count lower bound. -/
theorem legalMarkedTilted_lower_bound (q : ℕ)
    (sourceClock : A → ℝ) (targetClock : B → ℝ)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkn : ∀ a b, sourceClock a < targetClock b → ∀ v, 0 ≤ kin a b v)
    {probe : A → B → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G)
    {r : ℝ} (hr : 0 ≤ r) (t : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    -((mSourceCount ω : ℝ) * (|t| * G)) ≤
      legalMarkedTilted q sourceClock targetClock r kin probe t ω := by
  have hentry (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω))
      (hij : (i, j) ∈ legalMarkedGraph q (mSourceCount ω) (mTargetCount ω)
        sourceClock targetClock ω) :
      -(|t| * G) ≤ mKineticCost q r kin ω i j + t * mProbe probe ω i j := by
    have hforward : sourceClock (mSourceMark ω i) < targetClock (mTargetMark ω j) := by
      simpa only [legalMarkedGraph, Finset.mem_filter, Finset.mem_univ, true_and] using hij
    have hkin : 0 ≤ mKineticCost q r kin ω i j :=
      mul_nonneg (Real.rpow_nonneg hr _) (hkn _ _ hforward _)
    have hprobe : |t * mProbe probe ω i j| ≤ |t| * G := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpb _ _ hforward) (abs_nonneg t)
    linarith [(neg_abs_le (t * mProbe probe ω i j))]
  have hle := PartialMatching.le_legalMaximumValue_of_allowed _ _ hentry
  have hcard : (PartialMatching.legalMaximumCard
      (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) sourceClock targetClock ω) : ℝ) ≤
        (mSourceCount ω : ℝ) :=
    Nat.cast_le.mpr ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))
  have hmult := mul_le_mul_of_nonneg_right hcard (mul_nonneg (abs_nonneg t) hG)
  change _ ≤ PartialMatching.legalMaximumValue _ _
  linarith

/-- The original legal Poisson pressure is bounded below without perfect matching. -/
theorem legalMarkedPressure_lower_bound (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkn : ∀ a b, sourceClock a < targetClock b → ∀ v, 0 ≤ kin a b v)
    (hkb : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G) (t : ℝ) :
    -((r : ℝ) * (|t| * G)) ≤
      legalMarkedPressure q sourceClock targetClock α β r kin probe t := by
  have hI := integrable_legalMarkedTilted_of_forward q hs ht α β r hC hG hk hkb hp hpb t
  have hbound := ((integrable_mSourceCount q α β r).mul_const (|t| * G)).neg
  have h := integral_mono hbound hI
    (legalMarkedTilted_lower_bound q sourceClock targetClock hkn hG hpb r.coe_nonneg t)
  simp only [Pi.neg_apply] at h
  rw [integral_neg, integral_mul_const, integral_mSourceCount_eq] at h
  exact h

/-- Normalization gives a uniform Lipschitz bound at every spatial scale. -/
theorem legalMarkedScalePressure_lipschitz (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G) (R t u : ℝ) :
    |legalMarkedScalePressure q sourceClock targetClock α β kin probe R t -
      legalMarkedScalePressure q sourceClock targetClock α β kin probe R u| ≤ G * |t - u| := by
  by_cases hR : 0 < R
  · simp only [legalMarkedScalePressure, hR, ↓reduceIte, ← sub_div, abs_div,
      abs_of_pos (pow_pos hR q)]
    have h := abs_legalMarkedPressure_sub_le q hs ht α β (Real.toNNReal (R ^ q))
      hC hG hk hkb hp hpb t u
    rw [Real.coe_toNNReal _ (pow_nonneg hR.le q)] at h
    exact (div_le_iff₀ (pow_pos hR q)).mpr (by nlinarith [h])
  · simp only [legalMarkedScalePressure, hR, ↓reduceIte, sub_self, abs_zero]
    exact mul_nonneg hG (abs_nonneg _)

/-- Concavity persists after scale normalization. -/
theorem concaveOn_legalMarkedScalePressure (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, sourceClock a < targetClock b → ∀ v,
      |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, sourceClock a < targetClock b → |probe a b| ≤ G) (R : ℝ) :
    ConcaveOn ℝ univ (legalMarkedScalePressure q sourceClock targetClock α β kin probe R) := by
  by_cases hR : 0 < R
  · have hbase := concaveOn_legalMarkedPressure q hs ht α β (Real.toNNReal (R ^ q))
      hC hG hk hkb hp hpb
    have hsmul := hbase.smul (inv_nonneg.mpr (pow_nonneg hR.le q))
    refine hsmul.congr ?_
    intro t _
    simp only [smul_eq_mul, legalMarkedScalePressure, hR, ↓reduceIte,
      div_eq_mul_inv]
    ring
  · have hzero : legalMarkedScalePressure q sourceClock targetClock α β kin probe R =
        fun _ ↦ 0 := by
      funext t
      simp only [legalMarkedScalePressure, hR, ↓reduceIte]
    rw [hzero]
    exact concaveOn_const 0 convex_univ

end OTSelector.Reconstruction
