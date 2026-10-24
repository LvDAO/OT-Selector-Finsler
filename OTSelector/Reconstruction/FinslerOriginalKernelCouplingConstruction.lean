import OTSelector.Reconstruction.FinslerOriginalKernelPressureStability
import OTSelector.Reconstruction.FinslerOriginalKernelMarkedPoisson

/-!
# Kernel coupling construction from a coupling of the marked point laws

This module closes gap (a) of FinslerOriginalKernelPressureStability.lean: from a
coupling of the marked point laws it constructs a coupling measure
coupledCloudPairLaw of the two kernel-marked two-cloud laws whose marginals are
exactly the two cloud laws and which pairs equal counts almost surely, and it
feeds the construction into the pressure stability theorem.

The construction keeps the counts common (a single Poisson variable for the
source count and a single one for the target count) and couples the source and
target marked sequences coordinatewise through the point-law couplings, so that
the two clouds share the positions and only differ in the marks.

Main results:

* map_infinitePi_coupledSeqFst / Snd: coordinatewise projections of the coupled
  iid sequence law, via infinitePi_map_pi;
* coupledCloudPairLaw_fst / coupledCloudPairLaw_snd: the two marginals of the
  coupling are exactly the kernel-marked two-cloud laws;
* coupledCloudPairLaw_counts_eq: the source and target counts agree almost surely;
* abs_markedEdgeCost_sub_le_of_uniform and markedEdgeErrorBound: the uniform
  edge-error constant of a mark-coupled pair;
* abs_kernelMarkedPressure_sub_le_of_pointLawCoupling: the kernel-marked pressure
  difference is bounded by the integral over the coupling of the minimum count
  times markedEdgeErrorBound, which is the hypothesis of
  abs_kernelMarkedPressure_sub_le_of_coupling.

The leaf-block law identification of gap (b) is not proved here; the exact
remaining producer steps are documented at the end of the file.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open OTSelector OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The truncated squared displacement is bounded by the dimension -/

/-- The squared length of a truncated displacement is at most the dimension. -/
theorem mDisplacement_sq_sum_le_card (q : ℕ) (x y : Fin q → ℝ) :
    ∑ l, mDisplacement x y l ^ 2 ≤ (q : ℝ) := by
  have hterm : ∀ l : Fin q, mDisplacement x y l ^ 2 ≤ 1 := by
    intro l
    have hx := cubeTruncPoint_mem x l
    have hy := cubeTruncPoint_mem y l
    have habs : |mDisplacement x y l| ≤ 1 := by
      unfold mDisplacement
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h := pow_le_pow_left₀ (abs_nonneg _) habs 2
    simpa [sq_abs] using h
  calc ∑ l : Fin q, mDisplacement x y l ^ 2
      ≤ ∑ _l : Fin q, (1 : ℝ) := Finset.sum_le_sum fun l _ => hterm l
    _ = (q : ℝ) := by simp

/-! ## The uniform edge error constant -/

/-- The uniform bound on the change of a marked edge cost under a change of the
marks, when the kinetic amplitude satisfies the lane's quadratic bound and the
probe is bounded. -/
noncomputable def markedEdgeErrorBound (q : ℕ) (r t C G : ℝ) : ℝ :=
  |r ^ (2 / (q : ℝ))| * (2 * C * (q : ℝ)) + |t| * (2 * G)

/-- **Pointwise edge stability.**  If the kinetic amplitude is controlled by the
squared truncated displacement with constant C, the probe by G, and both are
nonnegative, then the marked edge costs of two arbitrary marked two-cloud
samples at the same index pair differ by at most markedEdgeErrorBound. -/
theorem abs_markedEdgeCost_sub_le_of_uniform {q : ℕ} {r t C G : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (w1 w2 : TwoMarkedCloudSpace q A B) (i j : ℕ) :
    |markedEdgeCost q r kin g t w1 i j - markedEdgeCost q r kin g t w2 i j| ≤
      markedEdgeErrorBound q r t C G := by
  have hsq1 := mDisplacement_sq_sum_le_card q (mSourcePoint w1 i) (mTargetPoint w1 j)
  have hsq2 := mDisplacement_sq_sum_le_card q (mSourcePoint w2 i) (mTargetPoint w2 j)
  have hb1 := hkin_bound (mSourceMark w1 i) (mTargetMark w1 j)
    (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))
  have hb2 := hkin_bound (mSourceMark w2 i) (mTargetMark w2 j)
    (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))
  have hg1 := hgb (mSourceMark w1 i) (mTargetMark w1 j)
  have hg2 := hgb (mSourceMark w2 i) (mTargetMark w2 j)
  have hq1 : |kin (mSourceMark w1 i) (mTargetMark w1 j)
      (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| ≤ C * (q : ℝ) :=
    le_trans hb1 (mul_le_mul_of_nonneg_left hsq1 hC)
  have hq2 : |kin (mSourceMark w2 i) (mTargetMark w2 j)
      (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))| ≤ C * (q : ℝ) :=
    le_trans hb2 (mul_le_mul_of_nonneg_left hsq2 hC)
  have hk : |r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
      r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))| ≤
      |r ^ (2 / (q : ℝ))| * (2 * C * (q : ℝ)) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have htri : |kin (mSourceMark w1 i) (mTargetMark w1 j)
          (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
        kin (mSourceMark w2 i) (mTargetMark w2 j)
          (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))| ≤
        |kin (mSourceMark w1 i) (mTargetMark w1 j)
          (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| +
        |kin (mSourceMark w2 i) (mTargetMark w2 j)
          (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (kin (mSourceMark w1 i) (mTargetMark w1 j)
          (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)))
        (- kin (mSourceMark w2 i) (mTargetMark w2 j)
          (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j)))
    linarith
  have hgd : |t * g (mSourceMark w1 i) (mTargetMark w1 j) -
      t * g (mSourceMark w2 i) (mTargetMark w2 j)| ≤ |t| * (2 * G) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have htri : |g (mSourceMark w1 i) (mTargetMark w1 j) -
        g (mSourceMark w2 i) (mTargetMark w2 j)| ≤
        |g (mSourceMark w1 i) (mTargetMark w1 j)| +
        |g (mSourceMark w2 i) (mTargetMark w2 j)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (g (mSourceMark w1 i) (mTargetMark w1 j))
        (- g (mSourceMark w2 i) (mTargetMark w2 j))
    linarith
  unfold markedEdgeCost mKineticCost mProbe markedEdgeErrorBound
  have hsplit : (r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) +
      t * g (mSourceMark w1 i) (mTargetMark w1 j)) -
      (r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j)) +
      t * g (mSourceMark w2 i) (mTargetMark w2 j)) =
      (r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
      r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))) +
      (t * g (mSourceMark w1 i) (mTargetMark w1 j) -
      t * g (mSourceMark w2 i) (mTargetMark w2 j)) := by ring
  calc |(r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
          (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) +
        t * g (mSourceMark w1 i) (mTargetMark w1 j)) -
        (r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
          (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j)) +
        t * g (mSourceMark w2 i) (mTargetMark w2 j))|
      = |(r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
            (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
          r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
            (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))) +
          (t * g (mSourceMark w1 i) (mTargetMark w1 j) -
          t * g (mSourceMark w2 i) (mTargetMark w2 j))| := by rw [hsplit]
    _ ≤ |r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
            (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
          r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
            (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))| +
          |t * g (mSourceMark w1 i) (mTargetMark w1 j) -
          t * g (mSourceMark w2 i) (mTargetMark w2 j)| := abs_add_le _ _
    _ ≤ |r ^ (2 / (q : ℝ))| * (2 * C * (q : ℝ)) + |t| * (2 * G) :=
        add_le_add hk hgd

/-! ## The coupled sequence projections -/

/-- Read the first mark of a coupled marked point. -/
def coupledMarkFst {q : ℕ} (p : (Fin q → ℝ) × (A × A)) : (Fin q → ℝ) × A :=
  (p.1, p.2.1)

/-- Read the second mark of a coupled marked point. -/
def coupledMarkSnd {q : ℕ} (p : (Fin q → ℝ) × (A × A)) : (Fin q → ℝ) × A :=
  (p.1, p.2.2)

theorem measurable_coupledMarkFst {q : ℕ} :
    Measurable (coupledMarkFst (q := q) (A := A)) := by
  unfold coupledMarkFst
  fun_prop

theorem measurable_coupledMarkSnd {q : ℕ} :
    Measurable (coupledMarkSnd (q := q) (A := A)) := by
  unfold coupledMarkSnd
  fun_prop

/-- Coordinatewise first-mark projection of a coupled marked sequence. -/
def coupledSeqFst {q : ℕ} (s : ℕ → (Fin q → ℝ) × (A × A)) : ℕ → (Fin q → ℝ) × A :=
  fun i => coupledMarkFst (s i)

/-- Coordinatewise second-mark projection of a coupled marked sequence. -/
def coupledSeqSnd {q : ℕ} (s : ℕ → (Fin q → ℝ) × (A × A)) : ℕ → (Fin q → ℝ) × A :=
  fun i => coupledMarkSnd (s i)

theorem measurable_coupledSeqFst {q : ℕ} :
    Measurable (coupledSeqFst (q := q) (A := A)) := by
  unfold coupledSeqFst
  exact measurable_pi_iff.mpr fun i =>
    measurable_coupledMarkFst.comp (measurable_pi_apply i)

theorem measurable_coupledSeqSnd {q : ℕ} :
    Measurable (coupledSeqSnd (q := q) (A := A)) := by
  unfold coupledSeqSnd
  exact measurable_pi_iff.mpr fun i =>
    measurable_coupledMarkSnd.comp (measurable_pi_apply i)

/-- **The iid sequence law of the first marks.** -/
theorem map_infinitePi_coupledSeqFst {q : ℕ}
    (γs : Measure ((Fin q → ℝ) × (A × A))) [IsProbabilityMeasure γs] :
    (Measure.infinitePi (fun _ : ℕ => γs)).map (coupledSeqFst (q := q) (A := A)) =
      Measure.infinitePi (fun _ : ℕ => γs.map (coupledMarkFst (q := q) (A := A))) := by
  have hfun : (fun x : ℕ → (Fin q → ℝ) × (A × A) => fun i => coupledMarkFst (x i)) =
      coupledSeqFst (q := q) (A := A) := by
    funext x i
    rfl
  rw [← hfun]
  exact Measure.infinitePi_map_pi (μ := fun _ : ℕ => γs)
    (f := fun _ (p : (Fin q → ℝ) × (A × A)) => coupledMarkFst p)
    (fun _ => measurable_coupledMarkFst (A := A))

/-- **The iid sequence law of the second marks.** -/
theorem map_infinitePi_coupledSeqSnd {q : ℕ}
    (γs : Measure ((Fin q → ℝ) × (A × A))) [IsProbabilityMeasure γs] :
    (Measure.infinitePi (fun _ : ℕ => γs)).map (coupledSeqSnd (q := q) (A := A)) =
      Measure.infinitePi (fun _ : ℕ => γs.map (coupledMarkSnd (q := q) (A := A))) := by
  have hfun : (fun x : ℕ → (Fin q → ℝ) × (A × A) => fun i => coupledMarkSnd (x i)) =
      coupledSeqSnd (q := q) (A := A) := by
    funext x i
    rfl
  rw [← hfun]
  exact Measure.infinitePi_map_pi (μ := fun _ : ℕ => γs)
    (f := fun _ (p : (Fin q → ℝ) × (A × A)) => coupledMarkSnd p)
    (fun _ => measurable_coupledMarkSnd (A := A))

/-! ## The two single-cloud projections -/

/-- The count and first-mark coupled-sequence projection. -/
def countSeqFst (q : ℕ) (p : ℕ × (ℕ → (Fin q → ℝ) × (A × A))) :
    MarkedCloudSpace q A :=
  (p.1, coupledSeqFst (A := A) p.2)

/-- The count and second-mark coupled-sequence projection. -/
def countSeqSnd (q : ℕ) (p : ℕ × (ℕ → (Fin q → ℝ) × (A × A))) :
    MarkedCloudSpace q A :=
  (p.1, coupledSeqSnd (A := A) p.2)

theorem measurable_countSeqFst (q : ℕ) :
    Measurable (countSeqFst (q := q) (A := A)) := by
  unfold countSeqFst
  exact measurable_fst.prodMk (measurable_coupledSeqFst.comp measurable_snd)

theorem measurable_countSeqSnd (q : ℕ) :
    Measurable (countSeqSnd (q := q) (A := A)) := by
  unfold countSeqSnd
  exact measurable_fst.prodMk (measurable_coupledSeqSnd.comp measurable_snd)

/-- **One cloud as the image of a count and a coupled sequence, first marks.** -/
theorem map_countSeqFst (q : ℕ) (R : ℝ≥0)
    (γs : Measure ((Fin q → ℝ) × (A × A))) [IsProbabilityMeasure γs]
    {K : Kernel (Fin q → ℝ) A} [IsMarkovKernel K]
    (hγ : γs.map (coupledMarkFst (q := q) (A := A)) = markedPointLaw q K) :
    (((poissonMeasure R).prod (Measure.infinitePi (fun _ : ℕ => γs))).map
        (countSeqFst (q := q) (A := A))) = kernelMarkedCloudLaw q A K R := by
  unfold countSeqFst
  rw [show (fun p : ℕ × (ℕ → (Fin q → ℝ) × (A × A)) => (p.1, coupledSeqFst p.2)) =
      Prod.map id (coupledSeqFst (q := q) (A := A)) from rfl]
  rw [← Measure.map_prod_map (poissonMeasure R)
    (Measure.infinitePi (fun _ : ℕ => γs)) measurable_id measurable_coupledSeqFst]
  rw [Measure.map_id, map_infinitePi_coupledSeqFst (A := A) γs, hγ]
  unfold kernelMarkedCloudLaw kernelMarkedSeqLaw markedPointLaw
  rfl

/-- **One cloud as the image of a count and a coupled sequence, second marks.** -/
theorem map_countSeqSnd (q : ℕ) (R : ℝ≥0)
    (γs : Measure ((Fin q → ℝ) × (A × A))) [IsProbabilityMeasure γs]
    {K : Kernel (Fin q → ℝ) A} [IsMarkovKernel K]
    (hγ : γs.map (coupledMarkSnd (q := q) (A := A)) = markedPointLaw q K) :
    (((poissonMeasure R).prod (Measure.infinitePi (fun _ : ℕ => γs))).map
        (countSeqSnd (q := q) (A := A))) = kernelMarkedCloudLaw q A K R := by
  unfold countSeqSnd
  rw [show (fun p : ℕ × (ℕ → (Fin q → ℝ) × (A × A)) => (p.1, coupledSeqSnd p.2)) =
      Prod.map id (coupledSeqSnd (q := q) (A := A)) from rfl]
  rw [← Measure.map_prod_map (poissonMeasure R)
    (Measure.infinitePi (fun _ : ℕ => γs)) measurable_id measurable_coupledSeqSnd]
  rw [Measure.map_id, map_infinitePi_coupledSeqSnd (A := A) γs, hγ]
  unfold kernelMarkedCloudLaw kernelMarkedSeqLaw markedPointLaw
  rfl

/-! ## The coupling measure of the two kernel-marked cloud laws -/

/-- The underlying independent product: a source count, the coupled source marked
sequence, a target count, and the coupled target marked sequence. -/
noncomputable def coupledUnderlyingLaw (q : ℕ) (R : ℝ≥0)
    (γs : Measure ((Fin q → ℝ) × (A × A)))
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γs]
    [IsProbabilityMeasure γt] :
    Measure ((ℕ × (ℕ → (Fin q → ℝ) × (A × A))) ×
      (ℕ × (ℕ → (Fin q → ℝ) × (B × B)))) :=
  ((poissonMeasure R).prod (Measure.infinitePi (fun _ : ℕ => γs))).prod
    ((poissonMeasure R).prod (Measure.infinitePi (fun _ : ℕ => γt)))

/-- The coupling map: both clouds share the counts and the positions, and read
their marks from the two coordinates of the coupled marked points. -/
def coupledCloudMap (q : ℕ) :
    ((ℕ × (ℕ → (Fin q → ℝ) × (A × A))) ×
      (ℕ × (ℕ → (Fin q → ℝ) × (B × B)))) →
    (TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B) :=
  fun z =>
    (((z.1.1, coupledSeqFst (A := A) z.1.2),
      (z.2.1, coupledSeqFst (A := B) z.2.2)),
     ((z.1.1, coupledSeqSnd (A := A) z.1.2),
      (z.2.1, coupledSeqSnd (A := B) z.2.2)))

theorem measurable_coupledCloudMap (q : ℕ) :
    Measurable (coupledCloudMap (q := q) (A := A) (B := B)) := by
  unfold coupledCloudMap
  refine Measurable.prod ?_ ?_
  · refine Measurable.prod ?_ ?_
    · exact (measurable_fst.comp measurable_fst).prodMk
        (measurable_coupledSeqFst.comp (measurable_snd.comp measurable_fst))
    · exact (measurable_fst.comp measurable_snd).prodMk
        (measurable_coupledSeqFst.comp (measurable_snd.comp measurable_snd))
  · refine Measurable.prod ?_ ?_
    · exact (measurable_fst.comp measurable_fst).prodMk
        (measurable_coupledSeqSnd.comp (measurable_snd.comp measurable_fst))
    · exact (measurable_fst.comp measurable_snd).prodMk
        (measurable_coupledSeqSnd.comp (measurable_snd.comp measurable_snd))

/-- The coupling measure of the two kernel-marked two-cloud laws built from a
coupling of the marked point laws. -/
noncomputable def coupledCloudPairLaw (q : ℕ) (R : ℝ≥0)
    (γs : Measure ((Fin q → ℝ) × (A × A)))
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γs]
    [IsProbabilityMeasure γt] :
    Measure (TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B) :=
  (coupledUnderlyingLaw (A := A) (B := B) q R γs γt).map
    (coupledCloudMap (q := q) (A := A) (B := B))

/-- **The first marginal of the coupling is the kernel-marked two-cloud law.** -/
theorem coupledCloudPairLaw_fst (q : ℕ) (R : ℝ≥0)
    (γs : Measure ((Fin q → ℝ) × (A × A)))
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γs]
    [IsProbabilityMeasure γt]
    {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    (hγs : γs.map (coupledMarkFst (q := q) (A := A)) = markedPointLaw q Ks)
    (hγt : γt.map (coupledMarkFst (q := q) (A := B)) = markedPointLaw q Kt) :
    (coupledCloudPairLaw (A := A) (B := B) q R γs γt).map Prod.fst =
      twoKernelMarkedCloudLaw q A B Ks Kt R := by
  have hstep : (coupledCloudPairLaw (A := A) (B := B) q R γs γt).map Prod.fst =
      (coupledUnderlyingLaw (A := A) (B := B) q R γs γt).map
        (Prod.map (countSeqFst (q := q) (A := A)) (countSeqFst (q := q) (A := B))) := by
    unfold coupledCloudPairLaw
    rw [Measure.map_map measurable_fst (measurable_coupledCloudMap (A := A) (B := B) q)]
    rfl
  rw [hstep]
  unfold coupledUnderlyingLaw twoKernelMarkedCloudLaw
  rw [← Measure.map_prod_map _ _
    (measurable_countSeqFst (q := q) (A := A)) (measurable_countSeqFst (q := q) (A := B))]
  rw [map_countSeqFst (A := A) q R γs hγs, map_countSeqFst (A := B) q R γt hγt]

/-- **The second marginal of the coupling is the kernel-marked two-cloud law.** -/
theorem coupledCloudPairLaw_snd (q : ℕ) (R : ℝ≥0)
    (γs : Measure ((Fin q → ℝ) × (A × A)))
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γs]
    [IsProbabilityMeasure γt]
    {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    (hγs : γs.map (coupledMarkSnd (q := q) (A := A)) = markedPointLaw q Ks)
    (hγt : γt.map (coupledMarkSnd (q := q) (A := B)) = markedPointLaw q Kt) :
    (coupledCloudPairLaw (A := A) (B := B) q R γs γt).map Prod.snd =
      twoKernelMarkedCloudLaw q A B Ks Kt R := by
  have hstep : (coupledCloudPairLaw (A := A) (B := B) q R γs γt).map Prod.snd =
      (coupledUnderlyingLaw (A := A) (B := B) q R γs γt).map
        (Prod.map (countSeqSnd (q := q) (A := A)) (countSeqSnd (q := q) (A := B))) := by
    unfold coupledCloudPairLaw
    rw [Measure.map_map measurable_snd (measurable_coupledCloudMap (A := A) (B := B) q)]
    rfl
  rw [hstep]
  unfold coupledUnderlyingLaw twoKernelMarkedCloudLaw
  rw [← Measure.map_prod_map _ _
    (measurable_countSeqSnd (q := q) (A := A)) (measurable_countSeqSnd (q := q) (A := B))]
  rw [map_countSeqSnd (A := A) q R γs hγs, map_countSeqSnd (A := B) q R γt hγt]

/-! ## Equal counts almost surely -/

/-- The set of pairs of clouds with equal source and target counts is measurable. -/
theorem measurableSet_counts_eq (q : ℕ) :
    MeasurableSet {z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B |
      mSourceCount (q := q) z.1 = mSourceCount (q := q) z.2 ∧
      mTargetCount (q := q) z.1 = mTargetCount (q := q) z.2} := by
  have hdiag : MeasurableSet {p : ℕ × ℕ | p.1 = p.2} := by
    have heq : {p : ℕ × ℕ | p.1 = p.2} = Set.range (fun n : ℕ => (n, n)) := by
      ext p
      constructor
      · intro h
        exact ⟨p.1, Prod.ext rfl h⟩
      · rintro ⟨n, rfl⟩
        rfl
    rw [heq]
    exact (Set.countable_range _).measurableSet
  have h1 : MeasurableSet {z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B |
      mSourceCount (q := q) z.1 = mSourceCount (q := q) z.2} :=
    hdiag.preimage (((measurable_mSourceCount q).comp measurable_fst).prodMk
      ((measurable_mSourceCount q).comp measurable_snd))
  have h2 : MeasurableSet {z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B |
      mTargetCount (q := q) z.1 = mTargetCount (q := q) z.2} :=
    hdiag.preimage (((measurable_mTargetCount q).comp measurable_fst).prodMk
      ((measurable_mTargetCount q).comp measurable_snd))
  exact h1.inter h2

/-- **The counts of the two clouds agree almost surely.** -/
theorem coupledCloudPairLaw_counts_eq (q : ℕ) (R : ℝ≥0)
    (γs : Measure ((Fin q → ℝ) × (A × A)))
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γs]
    [IsProbabilityMeasure γt] :
    ∀ᵐ z ∂(coupledCloudPairLaw (A := A) (B := B) q R γs γt),
      mSourceCount (q := q) z.1 = mSourceCount (q := q) z.2 ∧
        mTargetCount (q := q) z.1 = mTargetCount (q := q) z.2 := by
  unfold coupledCloudPairLaw
  refine (ae_map_iff (measurable_coupledCloudMap (A := A) (B := B) q).aemeasurable
    (measurableSet_counts_eq (A := A) (B := B) q)).mpr ?_
  exact Filter.Eventually.of_forall fun w => ⟨rfl, rfl⟩

/-! ## Pressure stability from a marked point law coupling -/

/-- **Kernel pressure stability from a marked point law coupling.**  Given a
position-preserving coupling of the marked point laws, the kernel-marked
pressure difference is bounded by the integral over the constructed coupling of
the minimum count times the uniform edge-error constant. -/
theorem abs_kernelMarkedPressure_sub_le_of_pointLawCoupling (q : ℕ) (R : ℝ≥0) {t C G : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {Ks Ks' : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks] [IsMarkovKernel Ks']
    {Kt Kt' : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt] [IsMarkovKernel Kt']
    (γs : Measure ((Fin q → ℝ) × (A × A))) [IsProbabilityMeasure γs]
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γt]
    (hγs1 : γs.map (coupledMarkFst (q := q) (A := A)) = markedPointLaw q Ks)
    (hγs2 : γs.map (coupledMarkSnd (q := q) (A := A)) = markedPointLaw q Ks')
    (hγt1 : γt.map (coupledMarkFst (q := q) (A := B)) = markedPointLaw q Kt)
    (hγt2 : γt.map (coupledMarkSnd (q := q) (A := B)) = markedPointLaw q Kt')
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hI1 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := (R : ℝ)) kin g t z.1)
      (coupledCloudPairLaw (A := A) (B := B) q R γs γt))
    (hI2 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := (R : ℝ)) kin g t z.2)
      (coupledCloudPairLaw (A := A) (B := B) q R γs γt))
    (hIB : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
        markedEdgeErrorBound q (R : ℝ) t C G)
      (coupledCloudPairLaw (A := A) (B := B) q R γs γt)) :
    |kernelMarkedPressure q A B Ks Kt R kin g t -
        kernelMarkedPressure q A B Ks' Kt' R kin g t| ≤
      ∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
        markedEdgeErrorBound q (R : ℝ) t C G
        ∂(coupledCloudPairLaw (A := A) (B := B) q R γs γt) := by
  have hf : Measurable (markedTilted (q := q) (r := (R : ℝ)) kin g t) :=
    measurable_markedTilted (q := q) (r := (R : ℝ)) (C := C) (G := G)
      (kin := kin) (g := g) R.coe_nonneg hC hG hkin hkin_bound hg hgb t
  have hH1 := coupledCloudPairLaw_fst (A := A) (B := B) q R γs γt hγs1 hγt1
  have hH2 := coupledCloudPairLaw_snd (A := A) (B := B) q R γs γt hγs2 hγt2
  have hsp : ∀ᵐ z ∂(coupledCloudPairLaw (A := A) (B := B) q R γs γt),
      mSourceCount (q := q) z.1 = mSourceCount (q := q) z.2 :=
    (coupledCloudPairLaw_counts_eq (A := A) (B := B) q R γs γt).mono fun z hz => hz.1
  have htp : ∀ᵐ z ∂(coupledCloudPairLaw (A := A) (B := B) q R γs γt),
      mTargetCount (q := q) z.1 = mTargetCount (q := q) z.2 :=
    (coupledCloudPairLaw_counts_eq (A := A) (B := B) q R γs γt).mono fun z hz => hz.2
  have hB : ∀ᵐ z ∂(coupledCloudPairLaw (A := A) (B := B) q R γs γt), ∀ i j : ℕ,
      |markedEdgeCost q (R : ℝ) kin g t z.1 i j -
        markedEdgeCost q (R : ℝ) kin g t z.2 i j| ≤
        markedEdgeErrorBound q (R : ℝ) t C G :=
    Filter.Eventually.of_forall fun z i j =>
      abs_markedEdgeCost_sub_le_of_uniform hkin_bound hgb hC hG z.1 z.2 i j
  exact abs_kernelMarkedPressure_sub_le_of_coupling (q := q) (R := R) (kin := kin)
    (g := g) (t := t) (coupledCloudPairLaw (A := A) (B := B) q R γs γt) hH1 hH2 hsp htp
    (fun _ => markedEdgeErrorBound q (R : ℝ) t C G) hB hf hI1 hI2 hIB

end OTSelector.Reconstruction

/-!
## The remaining producer steps

Gap (a) is closed by the construction above.  The inputs that the present module
still leaves to the lane are:

1. Existence of a position-preserving coupling of the two marked point laws.
   The coupling is a measure on the cube times the two mark spaces with the two
   marked point laws as marginals of the two coordinate projections.  Since both
   marked point laws have the same position marginal (the cube measure), such a
   coupling exists; the natural construction is the conditional-product law of
   the position and the two mark kernels, and its identification with the two
   marked point laws is the measure-algebra step of the producer.

2. The integrability hypotheses hI1, hI2 and hIB of the pressure stability
   theorem.  They follow from the Poisson moment bounds of the lane (the counts
   of the kernel-marked cloud are Poisson and the tilted value is bounded by the
   minimum count times the uniform edge bound); the corresponding lemmas are
   available for the independent-mark lane (integrable_mSourceCount,
   integrable_markedTilted) and have to be transferred to the kernel-marked law,
   whose point law only differs in the mark component.

Gap (b), the leaf-block law identification for kernel marks, is not proved here.
Its exact content is: the pushforward of the kernel-marked two-cloud law under
the block extraction map is the product over the leaf blocks of the
kernel-marked cloud laws with the block-rescaled kernels blockLocalKernel K c at
intensity R / m ^ q.  Proving it requires the Poisson thinning of the block
labels (which is independent of the marks, since the labels only see the
positions), the rescaling of the block-local positions, and the identification
of the mark law of a point in block c with blockLocalKernel K c, which is
definitional once the position is written in block-local coordinates.  Once that
identity is available, blockKernelComparison_of_blockwise_stability
(FinslerOriginalKernelPressureStability) converts blockwise pressure stability
into the aggregate BlockKernelComparison with error m ^ q * err, and the present
pressure stability theorem supplies the blockwise bound from the point-law
coupling.  The pairing-scale bookkeeping needed there is the block-rescaling
identity mKineticCost_eq_local_of_same_block of MarkedBlockValueIntegral: the
ambient kinetic cost at intensity r equals the block-local kinetic cost at
intensity r / m ^ q, so the kinetic part of the edge error is evaluated at the
pairing scale while the mark kernel is sampled at block-local positions.
-/
