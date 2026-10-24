import OTSelector.Reconstruction.FinslerOriginalKernelCouplingConstruction
import OTSelector.Reconstruction.FinslerOriginalBlockPressureLimitIdentification
import OTSelector.Reconstruction.FinslerOriginalKernelModulusPressure

/-!
# Quantitative blockwise stabilization for position-dependent kernels

This module attacks the producer steps listed at the end of
`FinslerOriginalKernelPressureStability` / `FinslerOriginalKernelCouplingConstruction`
that block the block pressure limit identification of
`FinslerOriginalBlockPressureLimitIdentification`.

The unavailable analytic inputs are packaged in the predicate
`QuantitativeBlockwiseStabilization q m Ks Kt kin g t err`: for every block `c`,
at every scale `L`, the absolute difference between the block-rescaled scale
pressure and the reference scale pressure is eventually bounded by `err L`, with
`err L -> 0`.  From it the module derives, with no further analytic input:

* the blockwise stabilization hypothesis of the identification theorem
  (`tendsto_scalePressure_sub_of_error_bound`);
* the per-block normalized limits `p_c`, all equal to the reference limit `p`, and
  hence the numerical identity `(1 / m ^ q) * sum_c p_c = p`
  (`tendsto_blockScalePressure_and_identity`);
* the block-averaged identification `average -> p`
  (`tendsto_blockAverageScalePressure_of_error_bound`);
* the `hupper`-shaped upper readout bound
  (`eventually_kernelMarkedScalePressure_le_of_error_bound`).

The quantitative error is supplied by the coupling construction:
`blockScalePressureError_le_of_pointLawCoupling` instantiates
`abs_kernelMarkedPressure_sub_le_of_pointLawCoupling` at intensity
`Real.toNNReal (L ^ q)` and divides by `L ^ q`, producing

  error_c(L) <= (∫ min-count * markedEdgeErrorBound q (L ^ q) t C G) / L ^ q.

The constant kernels are the sharp case: the error vanishes identically
(`blockScalePressureError_const_eq_zero`), so the whole chain, including the
`hupper` readout, is unconditionally closed once the constant-kernel reference
limit is supplied (`eventually_kernelMarkedScalePressure_le_const`).

The exact remaining sub-gap is the analytic control of that integral for
genuinely position-dependent marks.  The available coupling construction pairs
the marked point laws coordinatewise through a coupling of the mark laws, and
the only available edge-error bound is the uniform constant
`markedEdgeErrorBound q r t C G` (a worst-case bound using only
`|kin| <= C * sum v ^ 2` and `|g| <= G`).  Two inputs are missing to turn the
integral bound into an `o (L ^ q)` estimate: (i) a *mark modulus* of the mark
kernel at the pairing scale, i.e. a coupling of the block marked point law with
the reference marked point law on which the mark distance is small, together
with a mark-Lipschitz bound on `kin` and `g`; (ii) a *matching moment bound* for
the optimal matching, i.e. a quantitative bound on the total squared matched
displacement of the block cloud (the lane's hypotheses give only the upper bound
`|kin| <= C * sum v ^ 2`, not a lower quadratic bound, so the matching moment is
not available).  Both are stated as hypotheses here, never assumed silently: the
predicate `QuantitativeBlockwiseStabilization` is the honest interface, and the
theorems below show exactly that it suffices.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators
open OTSelector OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The quantitative interface -/

/-- The absolute difference between the block-rescaled scale pressure and the
reference scale pressure at scale `L` and tilt `t`. -/
noncomputable def blockScalePressureError (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ)
    (c : Fin q → Fin m) (L t : ℝ) : ℝ :=
  |kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
      kin g L t -
    kernelMarkedScalePressure q A B Ks Kt kin g L t|

/-- **Quantitative blockwise stabilization.**  Uniform in the blocks, the
block-rescaled scale pressure differs from the reference scale pressure by a
quantity eventually bounded by `err`, with `err -> 0`. -/
def QuantitativeBlockwiseStabilization (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) (err : ℝ → ℝ) : Prop :=
  ∀ c : Fin q → Fin m,
    ∀ᶠ L : ℝ in atTop, blockScalePressureError q m Ks Kt kin g c L t ≤ err L

/-! ## From the quantitative bound to the blockwise stabilization -/

/-- **Quantitative error gives blockwise stabilization.** -/
theorem tendsto_scalePressure_sub_of_error_bound
    (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t : ℝ} {err : ℝ → ℝ}
    (herr : Tendsto err atTop (𝓝 0))
    (h : QuantitativeBlockwiseStabilization q m Ks Kt kin g t err) :
    ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) kin g L t -
          kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 0) := by
  intro c
  have habs : Tendsto (fun L : ℝ =>
      |kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) kin g L t -
          kernelMarkedScalePressure q A B Ks Kt kin g L t|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
      (Eventually.of_forall fun L => abs_nonneg _) (h c)
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

/-- **Per-block normalized limits.**  If the block pressure errors are uniformly
`o(1)` and the reference scale pressure tends to `p`, then every block-rescaled
scale pressure tends to `p`. -/
theorem tendsto_blockScalePressure_of_error_bound
    (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t p : ℝ} {err : ℝ → ℝ}
    (herr : Tendsto err atTop (𝓝 0))
    (h : QuantitativeBlockwiseStabilization q m Ks Kt kin g t err)
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 p) := by
  intro c
  have hsub := tendsto_scalePressure_sub_of_error_bound q m Ks Kt herr h c
  have hsum := href.add hsub
  have hfun : (fun L : ℝ =>
        kernelMarkedScalePressure q A B Ks Kt kin g L t +
          (kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
              (blockLocalKernel Kt c) kin g L t -
            kernelMarkedScalePressure q A B Ks Kt kin g L t)) =
      fun L : ℝ => kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
        (blockLocalKernel Kt c) kin g L t := by
    funext L
    ring
  rw [hfun] at hsum
  simpa only [add_zero] using hsum

/-- **The numerical identity.**  When all block limits equal `p`, the normalized
average of the block limits is `p`. -/
theorem blockAverage_limit_identity {q m : ℕ} (hm : 0 < m)
    (pc : (Fin q → Fin m) → ℝ) (p : ℝ)
    (hpc : ∀ c : Fin q → Fin m, pc c = p) :
    (1 / (((m ^ q : ℕ) : ℝ))) * ∑ c : Fin q → Fin m, pc c = p := by
  have hmq0 : (((m ^ q : ℕ) : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
    exact h.ne'
  rw [Finset.sum_congr rfl (fun c _ => hpc c), Finset.sum_const,
    card_blockIndex q m, nsmul_eq_mul]
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ hmq0, one_mul]

/-- **Per-block limits and the numerical identity.**  The quantitative error
bound yields the normalized block limits `p_c`, all equal to the reference
limit `p`, and the identity `(1 / m ^ q) * sum_c p_c = p`. -/
theorem tendsto_blockScalePressure_and_identity
    (q m : ℕ) (hm : 0 < m) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t p : ℝ} {err : ℝ → ℝ}
    (herr : Tendsto err atTop (𝓝 0))
    (h : QuantitativeBlockwiseStabilization q m Ks Kt kin g t err)
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    (∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 p)) ∧
      (1 / (((m ^ q : ℕ) : ℝ))) * ∑ _c : Fin q → Fin m, p = p :=
  ⟨tendsto_blockScalePressure_of_error_bound q m Ks Kt herr h href,
    blockAverage_limit_identity hm (fun _ => p) p (fun _ => rfl)⟩

/-! ## Block-averaged identification and the `hupper` readout -/

/-- **The block average converges to the reference limit.** -/
theorem tendsto_blockAverageScalePressure_of_error_bound
    (q m : ℕ) (hm : 0 < m) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t p : ℝ} {err : ℝ → ℝ}
    (herr : Tendsto err atTop (𝓝 0))
    (h : QuantitativeBlockwiseStabilization q m Ks Kt kin g t err)
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    Tendsto (blockAverageScalePressure q m Ks Kt kin g · t) atTop (𝓝 p) :=
  tendsto_blockAverageScalePressure_of_blockwise_stability (q := q) (m := m) hm
    Ks Kt (t := t) (fun c => tendsto_scalePressure_sub_of_error_bound q m Ks Kt herr h c)
    href

/-- **The `hupper`-shaped upper readout bound.**  The quantitative blockwise
stabilization supplies the last input of the aggregate upper bound: for every
`ε > 0` the reference scale pressure is eventually at most `p + ε`. -/
theorem eventually_kernelMarkedScalePressure_le_of_error_bound
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ} {err : ℝ → ℝ}
    (herr : Tendsto err atTop (𝓝 0))
    (h : QuantitativeBlockwiseStabilization q m Ks Kt kin g t err)
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      kernelMarkedScalePressure q A B Ks Kt kin g R t ≤ p + ε :=
  eventually_kernelMarkedScalePressure_le_of_blockwise_stability (q := q) (m := m)
    (J := J) hq hm hJ hJ2 Ks Kt (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound
    hkin_homog hg hgb (fun c => tendsto_scalePressure_sub_of_error_bound q m Ks Kt herr h c)
    href

/-! ## The coupling construction produces the quantitative error -/

/-- **Quantitative error bound from the marked point law coupling.**  This is
the scale form of `abs_kernelMarkedPressure_sub_le_of_pointLawCoupling`: the
block pressure error at scale `L` is bounded by the coupling integral at
intensity `Real.toNNReal (L ^ q)`, divided by `L ^ q`.  The remaining task is to
make this integral `o (L ^ q)`. -/
theorem blockScalePressureError_le_of_pointLawCoupling
    (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t C G : ℝ}
    (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (c : Fin q → Fin m) {L : ℝ} (hL : 0 < L)
    (γs : Measure ((Fin q → ℝ) × (A × A))) [IsProbabilityMeasure γs]
    (γt : Measure ((Fin q → ℝ) × (B × B))) [IsProbabilityMeasure γt]
    (hγs1 : γs.map (coupledMarkFst (q := q) (A := A)) =
      markedPointLaw q (blockLocalKernel Ks c))
    (hγs2 : γs.map (coupledMarkSnd (q := q) (A := A)) = markedPointLaw q Ks)
    (hγt1 : γt.map (coupledMarkFst (q := q) (A := B)) =
      markedPointLaw q (blockLocalKernel Kt c))
    (hγt2 : γt.map (coupledMarkSnd (q := q) (A := B)) = markedPointLaw q Kt)
    (hI1 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := ((Real.toNNReal (L ^ q) : ℝ≥0) : ℝ)) kin g t z.1)
      (coupledCloudPairLaw (A := A) (B := B) q (Real.toNNReal (L ^ q)) γs γt))
    (hI2 : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      markedTilted (q := q) (r := ((Real.toNNReal (L ^ q) : ℝ≥0) : ℝ)) kin g t z.2)
      (coupledCloudPairLaw (A := A) (B := B) q (Real.toNNReal (L ^ q)) γs γt))
    (hIB : Integrable (fun z : TwoMarkedCloudSpace q A B × TwoMarkedCloudSpace q A B =>
      ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
        markedEdgeErrorBound q ((Real.toNNReal (L ^ q) : ℝ≥0) : ℝ) t C G)
      (coupledCloudPairLaw (A := A) (B := B) q (Real.toNNReal (L ^ q)) γs γt)) :
    blockScalePressureError q m Ks Kt kin g c L t ≤
      (∫ z, ((min (mSourceCount (q := q) z.1) (mTargetCount (q := q) z.1) : ℕ) : ℝ) *
        markedEdgeErrorBound q ((Real.toNNReal (L ^ q) : ℝ≥0) : ℝ) t C G
        ∂(coupledCloudPairLaw (A := A) (B := B) q (Real.toNNReal (L ^ q)) γs γt)) /
        L ^ q := by
  have hLq : (0 : ℝ) < L ^ q := pow_pos hL q
  have hdiff := abs_kernelMarkedPressure_sub_le_of_pointLawCoupling (A := A) (B := B)
    (q := q) (R := Real.toNNReal (L ^ q)) (t := t) (C := C) (G := G)
    (kin := kin) (g := g) (Ks := blockLocalKernel Ks c) (Ks' := Ks)
    (Kt := blockLocalKernel Kt c) (Kt' := Kt) γs γt hγs1 hγs2 hγt1 hγt2
    hkin hkin_bound hg hgb hC0 hG0 hI1 hI2 hIB
  unfold blockScalePressureError
  rw [kernelMarkedScalePressure_of_pos q A B (blockLocalKernel Ks c)
      (blockLocalKernel Kt c) hL,
    kernelMarkedScalePressure_of_pos q A B Ks Kt hL]
  rw [← sub_div, abs_div, abs_of_pos hLq]
  exact div_le_div_of_nonneg_right hdiff hLq.le

/-! ## The constant-kernel sharp case -/

/-- At constant kernels the block and reference scale pressures coincide, so the
quantitative error is exactly zero. -/
theorem blockScalePressureError_const_eq_zero
    (q m : ℕ) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (c : Fin q → Fin m) (L t : ℝ) :
    blockScalePressureError q m (Kernel.const (Fin q → ℝ) α)
      (Kernel.const (Fin q → ℝ) β) kin g c L t = 0 := by
  unfold blockScalePressureError
  have h : kernelMarkedScalePressure q A B
        (blockLocalKernel (Kernel.const (Fin q → ℝ) α) c)
        (blockLocalKernel (Kernel.const (Fin q → ℝ) β) c) kin g L t =
      kernelMarkedScalePressure q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) kin g L t := by
    refine kernelMarkedScalePressure_eq_of_markedPointLaw q ?_ ?_
      (kin := kin) (g := g) (R := L) (t := t)
    · rw [blockLocalKernel_const]
    · rw [blockLocalKernel_const]
  rw [h, sub_self, abs_zero]

/-- **Constant-kernel `hupper` readout, unconditionally closed.**  At constant
kernels the quantitative error vanishes identically, so the blockwise
stabilization is exact and the upper readout bound follows from the
constant-kernel reference limit alone. -/
theorem eventually_kernelMarkedScalePressure_le_const
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ}
    (href : Tendsto (fun L : ℝ => kernelMarkedScalePressure q A B
      (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) kin g L t)
      atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      kernelMarkedScalePressure q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) kin g R t ≤ p + ε := by
  refine eventually_kernelMarkedScalePressure_le_of_error_bound (q := q) (m := m)
    (J := J) hq hm hJ hJ2 (Kernel.const (Fin q → ℝ) α)
    (Kernel.const (Fin q → ℝ) β) (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound
    hkin_homog hg hgb (err := fun _ => 0) tendsto_const_nhds ?_ href
  intro c
  exact Eventually.of_forall fun L => by
    rw [blockScalePressureError_const_eq_zero q m α β c L t]

end OTSelector.Reconstruction
