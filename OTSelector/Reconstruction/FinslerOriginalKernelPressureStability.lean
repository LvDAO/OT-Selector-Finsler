import OTSelector.Probability.MarkedBlockValueIntegral
import OTSelector.Finite.MaxCardValueSigned
import OTSelector.Reconstruction.FinslerOriginalKernelModulusPressure

/-!
# Kernel pressure stability and the block-scale bookkeeping

This module supplies the two quantitative ingredients that the reduction in
FinslerOriginalKernelModulusPressure.lean isolated, at the strongest form that
is provable without redoing the leaf-block law computation:

* the tilted marked value of a two-cloud sample is a max-cardinality matrix
  value, so the entrywise stability of maxCardValue bounds its change under a
  perturbation of the edge costs by min-count times the uniform edge error;
* for any coupling measure of the two kernel-marked cloud laws, the pressure
  difference is bounded by the integral of min-count times the coupled edge
  error, which is the precise form in which a modulus of continuity of the mark
  kernel has to enter;
* the edge error itself is bounded by the kinetic amplitude of the matched pair
  plus the probe amplitude, and the kinetic amplitude is the ambient
  displacement, not the block-local displacement, by the block-rescaling
  identity of the block machinery.

The remaining producer steps are documented at the end of the file.
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

/-! ## The tilted marked value as a max-cardinality value -/

/-- The marked tilted value is the maximum-cardinality value of the matrix of
marked edge costs at the cloud counts. -/
theorem markedTilted_eq_cloudValueNat (q : ℕ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) :
    markedTilted (q := q) (r := r) kin g t =
      cloudValueNat (markedEdgeCost q r kin g t)
        (mSourceCount (q := q) (A := A) (B := B))
        (mTargetCount (q := q) (A := A) (B := B)) := rfl

/-! ## Entrywise stability of the tilted value -/

/-- Entrywise stability of the marked tilted value: two two-cloud samples with
the same source and target counts whose edge costs differ by at most Bnd
entrywise have tilted values differing by at most the minimum count times Bnd. -/
theorem abs_markedTilted_sub_le_of_entrywise {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {w1 w2 : TwoMarkedCloudSpace q A B}
    (hsp : mSourceCount (q := q) w1 = mSourceCount (q := q) w2)
    (htp : mTargetCount (q := q) w1 = mTargetCount (q := q) w2)
    {Bnd : ℝ}
    (hB : ∀ i j : ℕ,
      |markedEdgeCost q r kin g t w1 i j - markedEdgeCost q r kin g t w2 i j| ≤ Bnd) :
    |markedTilted (q := q) (r := r) kin g t w1 -
        markedTilted (q := q) (r := r) kin g t w2| ≤
      ((min (mSourceCount (q := q) w1) (mTargetCount (q := q) w1) : ℕ) : ℝ) * Bnd := by
  rw [markedTilted_eq_cloudValueNat]
  unfold cloudValueNat
  rw [← hsp, ← htp]
  refine PartialMatching.abs_maxCardValue_sub_le_of_entrywise _ _ ?_
  intro i j
  exact hB i j

/-- The uniform edge error in a marked cloud: two mark-coupled marked clouds
whose displacements agree entry by entry have edge costs differing by at most
the kinetic amplitude of the pair plus the probe amplitude. -/
theorem markedEdgeCost_sub_le {q : ℕ} {r t C G : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {w1 w2 : TwoMarkedCloudSpace q A B}
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G)
    (i j : ℕ)
    (hpos : mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j) =
      mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j)) :
    |markedEdgeCost q r kin g t w1 i j - markedEdgeCost q r kin g t w2 i j| ≤
      |r ^ (2 / (q : ℝ))| * (2 * C * ∑ l, mDisplacement (mSourcePoint w1 i)
        (mTargetPoint w1 j) l ^ 2) + |t| * (2 * G) := by
  have hveq : mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j) =
      mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j) := hpos.symm
  have h1 := hkin_bound (mSourceMark w1 i) (mTargetMark w1 j)
    (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))
  have h2 := hkin_bound (mSourceMark w2 i) (mTargetMark w2 j)
    (mDisplacement (mSourcePoint w2 i) (mTargetPoint w2 j))
  rw [hveq] at h2
  have hg1 := hgb (mSourceMark w1 i) (mTargetMark w1 j)
  have hg2 := hgb (mSourceMark w2 i) (mTargetMark w2 j)
  unfold markedEdgeCost mKineticCost mProbe
  rw [hveq]
  have htri1 : |kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
      kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| ≤
      |kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| +
      |kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)))
      (- kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)))
  have hsum0 : 0 ≤ ∑ l, mDisplacement (mSourcePoint w1 i)
      (mTargetPoint w1 j) l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hk : |r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
      r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| ≤
      |r ^ (2 / (q : ℝ))| * (2 * C *
        ∑ l, mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j) l ^ 2) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    obtain ⟨ht1, ht2⟩ := abs_le.mp htri1
    have hK : |kin (mSourceMark w1 i) (mTargetMark w1 j)
          (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| +
        |kin (mSourceMark w2 i) (mTargetMark w2 j)
          (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))| ≤
        2 * (C * ∑ l, mDisplacement (mSourcePoint w1 i)
          (mTargetPoint w1 j) l ^ 2) := by
      linarith
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have htri2 : |g (mSourceMark w1 i) (mTargetMark w1 j) -
      g (mSourceMark w2 i) (mTargetMark w2 j)| ≤
      |g (mSourceMark w1 i) (mTargetMark w1 j)| +
      |g (mSourceMark w2 i) (mTargetMark w2 j)| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (g (mSourceMark w1 i) (mTargetMark w1 j))
      (- g (mSourceMark w2 i) (mTargetMark w2 j))
  have hgd : |t * g (mSourceMark w1 i) (mTargetMark w1 j) -
      t * g (mSourceMark w2 i) (mTargetMark w2 j)| ≤ |t| * (2 * G) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    obtain ⟨ha1, ha2⟩ := abs_le.mp hg1
    obtain ⟨hb1, hb2⟩ := abs_le.mp hg2
    obtain ⟨ht1, ht2⟩ := abs_le.mp htri2
    rw [abs_le]
    constructor <;> linarith
  have hsplit : (r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) +
      t * g (mSourceMark w1 i) (mTargetMark w1 j)) -
      (r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) +
      t * g (mSourceMark w2 i) (mTargetMark w2 j)) =
      (r ^ (2 / (q : ℝ)) * kin (mSourceMark w1 i) (mTargetMark w1 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j)) -
      r ^ (2 / (q : ℝ)) * kin (mSourceMark w2 i) (mTargetMark w2 j)
        (mDisplacement (mSourcePoint w1 i) (mTargetPoint w1 j))) +
      (t * g (mSourceMark w1 i) (mTargetMark w1 j) -
      t * g (mSourceMark w2 i) (mTargetMark w2 j)) := by ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add hk hgd)


/-! ## Integral stability along a coupling -/

/-- Integral stability along a coupling: if a coupling measure H makes two
samples have the same counts and edge costs differing by at most Bnd, then the
expectation difference is at most the integral of the minimum count times Bnd. -/
theorem abs_integral_markedTilted_sub_le_of_coupling {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (H : Measure (TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B))
    (hsp : ∀ᵐ z ∂H, mSourceCount (q := q) z.1 = mSourceCount (q := q) z.2)
    (htp : ∀ᵐ z ∂H, mTargetCount (q := q) z.1 = mTargetCount (q := q) z.2)
    (Bnd : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B → ℝ)
    (hB : ∀ᵐ z ∂H, ∀ i j : ℕ,
      |markedEdgeCost q r kin g t z.1 i j - markedEdgeCost q r kin g t z.2 i j| ≤ Bnd z)
    (hI1 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := r) kin g t z.1) H)
    (hI2 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := r) kin g t z.2) H)
    (hIB : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) * Bnd z) H) :
    |∫ z, markedTilted (q := q) (r := r) kin g t z.1 ∂H -
        ∫ z, markedTilted (q := q) (r := r) kin g t z.2 ∂H| ≤
      ∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) * Bnd z ∂H := by
  have hae : ∀ᵐ z ∂H, |markedTilted (q := q) (r := r) kin g t z.1 -
      markedTilted (q := q) (r := r) kin g t z.2| ≤
      ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) * Bnd z := by
    filter_upwards [hsp, htp, hB] with z hs ht hb
    exact abs_markedTilted_sub_le_of_entrywise hs ht hb
  have hsub : ∫ z, (markedTilted (q := q) (r := r) kin g t z.1 -
      markedTilted (q := q) (r := r) kin g t z.2) ∂H =
      ∫ z, markedTilted (q := q) (r := r) kin g t z.1 ∂H -
        ∫ z, markedTilted (q := q) (r := r) kin g t z.2 ∂H :=
    integral_sub hI1 hI2
  rw [← hsub]
  calc |∫ z, (markedTilted (q := q) (r := r) kin g t z.1 -
        markedTilted (q := q) (r := r) kin g t z.2) ∂H|
      ≤ ∫ z, |markedTilted (q := q) (r := r) kin g t z.1 -
          markedTilted (q := q) (r := r) kin g t z.2| ∂H :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
          Bnd z ∂H := integral_mono_ae ((hI1.sub hI2).abs) hIB hae

/-! ## Pressure stability -/

/-- Extracting the first cloud out of a coupling measure. -/
theorem integral_fst_eq_of_map_fst_eq {q : ℕ}
    (H : Measure (TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B))
    (mu : Measure (TwoMarkedCloudSpace q A B))
    (hH : H.map Prod.fst = mu)
    (f : TwoMarkedCloudSpace q A B → ℝ) (hf : Measurable f) :
    ∫ z, f z.1 ∂H = ∫ w, f w ∂mu := by
  rw [← hH]
  rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]

/-- Extracting the second cloud out of a coupling measure. -/
theorem integral_snd_eq_of_map_snd_eq {q : ℕ}
    (H : Measure (TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B))
    (mu : Measure (TwoMarkedCloudSpace q A B))
    (hH : H.map Prod.snd = mu)
    (f : TwoMarkedCloudSpace q A B → ℝ) (hf : Measurable f) :
    ∫ z, f z.2 ∂H = ∫ w, f w ∂mu := by
  rw [← hH]
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]

/-- Pressure stability under a coupling of the kernel-marked cloud laws: for
any coupling measure of two kernel-marked two-cloud laws which pairs equal
counts and controls the edge error by Bnd, the kernel-marked pressures differ by
at most the integral of the minimum count times Bnd. -/
theorem abs_kernelMarkedPressure_sub_le_of_coupling {q : ℕ} {R : ℝ≥0} {t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {Ks Ks' : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks] [IsMarkovKernel Ks']
    {Kt Kt' : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt] [IsMarkovKernel Kt']
    (H : Measure (TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B))
    (hH1 : H.map Prod.fst = twoKernelMarkedCloudLaw q A B Ks Kt R)
    (hH2 : H.map Prod.snd = twoKernelMarkedCloudLaw q A B Ks' Kt' R)
    (hsp : ∀ᵐ z ∂H, mSourceCount (q := q) z.1 = mSourceCount (q := q) z.2)
    (htp : ∀ᵐ z ∂H, mTargetCount (q := q) z.1 = mTargetCount (q := q) z.2)
    (Bnd : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B → ℝ)
    (hB : ∀ᵐ z ∂H, ∀ i j : ℕ,
      |markedEdgeCost q (R : ℝ) kin g t z.1 i j - markedEdgeCost q (R : ℝ) kin g t z.2 i j| ≤ Bnd z)
    (hf : Measurable (markedTilted (q := q) (r := (R : ℝ)) kin g t))
    (hI1 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := (R : ℝ)) kin g t z.1) H)
    (hI2 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := (R : ℝ)) kin g t z.2) H)
    (hIB : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) * Bnd z) H) :
    |kernelMarkedPressure q A B Ks Kt R kin g t -
        kernelMarkedPressure q A B Ks' Kt' R kin g t| ≤
      ∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
        Bnd z ∂H := by
  have h1 : ∫ z, markedTilted (q := q) (r := (R : ℝ)) kin g t z.1 ∂H =
      ∫ w, markedTilted (q := q) (r := (R : ℝ)) kin g t w ∂
        twoKernelMarkedCloudLaw q A B Ks Kt R :=
    integral_fst_eq_of_map_fst_eq H _ hH1 _ hf
  have h2 : ∫ z, markedTilted (q := q) (r := (R : ℝ)) kin g t z.2 ∂H =
      ∫ w, markedTilted (q := q) (r := (R : ℝ)) kin g t w ∂
        twoKernelMarkedCloudLaw q A B Ks' Kt' R :=
    integral_snd_eq_of_map_snd_eq H _ hH2 _ hf
  have hmain := abs_integral_markedTilted_sub_le_of_coupling (H := H) hsp htp Bnd hB hI1 hI2 hIB
  rw [h1, h2] at hmain
  simpa only [kernelMarkedPressure] using hmain


/-! ## Turning blockwise pressure stability into the aggregate block comparison -/

/-- **Blockwise stability implies the aggregate block comparison.**  If each
block-rescaled pressure is within err of the reference pressure at every
intensity and tilt, then the aggregate block comparison of the kernel-marked
lane holds with error (m ^ q) * err. -/
theorem blockKernelComparison_of_blockwise_stability (q m : ℕ) {t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {err : ℝ}
    {Ks : Kernel (Fin q → ℝ) A} [IsMarkovKernel Ks]
    {Kt : Kernel (Fin q → ℝ) B} [IsMarkovKernel Kt]
    (hper : ∀ (c : Fin q → Fin m) (r : ℝ≥0) (t : ℝ),
      |kernelMarkedPressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
          r kin g t - kernelMarkedPressure q A B Ks Kt r kin g t| ≤ err) :
    BlockKernelComparison q m Ks Kt kin g (((m ^ q : ℕ) : ℝ) * err) := by
  intro r t
  have hsum : blockKernelPressureSum q m Ks Kt r kin g t ≤
      ∑ _c : Fin q → Fin m,
        (kernelMarkedPressure q A B Ks Kt r kin g t + err) := by
    refine Finset.sum_le_sum fun c _ => ?_
    have hc := hper c r t
    linarith [abs_le.mp hc]
  have hcard : ((Finset.univ : Finset (Fin q → Fin m)).card) = m ^ q := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp
  calc blockKernelPressureSum q m Ks Kt r kin g t
      ≤ ∑ _c : Fin q → Fin m,
          (kernelMarkedPressure q A B Ks Kt r kin g t + err) := hsum
    _ = ((m ^ q : ℕ) : ℝ) * kernelMarkedPressure q A B Ks Kt r kin g t +
          ((m ^ q : ℕ) : ℝ) * err := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, hcard]
        simp only [nsmul_eq_mul]

/-! ## The remaining producer steps

The two structural inputs that the present module does not supply, and that the
modulus-of-continuity route to the kernel-marked block comparison still needs,
are the following.

1. A coupling of the kernel-marked cloud laws.  The stability theorem above is
conditional on a coupling measure H of the two kernel-marked two-cloud laws with
equal counts and a controlled edge error.  The natural candidate is built from a
coupling of the marked point laws: a measure on the cube times A times A with
marginals the two marked point laws, transported to the iid sequence law and
combined with a common Poisson count.  Constructing that coupling and proving
its two marginals is a measure-algebra step (infinite products of a coupled
point law plus Poisson thinning) which is not done here.

2. The leaf-block law identification for kernel marks.  The kernel analogue of
integrals of the block-local tilted value against the kernel-marked cloud law
requires the block extraction map, the Poisson thinning over the m ^ q leaf
blocks, and the rescaling of the positions; the result is the product over the
blocks of the kernel-marked cloud laws with the block-rescaled kernels
blockLocalKernel K c at intensity R / m ^ q.  Once that identity is available,
blockKernelComparison_of_blockwise_stability converts blockwise pressure
stability into the aggregate block comparison with error (m ^ q) * err.

Two further quantitative points are worth recording about the edge error.

* The kinetic amplitude of a matched pair is the ambient displacement, not the
  block-local one: by mKineticCost_eq_local_of_same_block (in
  MarkedBlockValueIntegral) the ambient kinetic cost at intensity r equals the
  local kinetic cost at intensity r / m ^ q on a block.  A matched pair of the
  reference cloud has ambient separation of order R ^ (-1 / q); a matched pair
  inside a leaf block has the same ambient separation, so the kinetic part of
  the edge error is evaluated at the pairing scale, while the mark kernel of the
  block cloud is sampled at positions of the block, whose spread is the block
  scale 1 / m.  The modulus that the block comparison can absorb is therefore
  the kernel modulus at the larger of the block scale and the pairing scale,
  multiplied by the number of blocks.

* Bounding the kinetic part of the edge error needs a moment bound on the
  optimal matching: the edge difference is controlled by the squared
  displacement, and the lane hypotheses give only the upper bound
  |kin a b v| <= C * sum v l ^ 2, not a lower quadratic bound.  A quantitative
  stability estimate therefore also needs either a lower quadratic bound on kin
  or a separate integrability estimate for the total squared displacement of the
  optimal matching.  This is the analytic sub-gap behind the velocity factor in
  the stability bound.
-/

end OTSelector.Reconstruction