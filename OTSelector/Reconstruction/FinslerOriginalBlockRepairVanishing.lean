import OTSelector.Reconstruction.FinslerOriginalKernelBlockComparison
import OTSelector.Reconstruction.FinslerOriginalKernelModulusPressure
import OTSelector.Probability.GridRepairError
import OTSelector.Probability.GridRepairScaling

/-!
# Vanishing of the normalized block repair

The block comparison of `FinslerOriginalKernelBlockComparison.lean` carries the
intensity-dependent repair

  K_q (C + |t| G) R (rpow (R / m ^ q) (2 / q - 1 / 2) + rpow (R / m ^ q) (-1 / 2)).

After division by the intensity `R` this becomes the *repair rate*

  K_q (C + |t| G) (rpow (R / m ^ q) (2 / q - 1 / 2) + rpow (R / m ^ q) (-1 / 2)),

which only depends on the ratio `R / m ^ q`.  Since `q > 4` both exponents are
negative, so the rate vanishes as soon as `R / m ^ q -> infinity`, i.e. exactly
when the block scale satisfies `m ^ q = o(R)`.  (The condition `m ^ q ~ R` is
*not* enough: then the ratio stays bounded and the repair rate stays bounded away
from zero.  The paper's choice is the one that makes `m ^ q / R -> 0`.)

This module records the rate limit, the intrinsic vanishing statement for a
block count depending on the intensity, and the resulting normalized upper
pressure comparison.
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

/-! ## The repair rate -/

/-- The intensity-dependent repair of the kernel-marked block comparison, as a
function of the real intensity `R` and the block count `m`. -/
noncomputable def kernelBlockRepairExpr (q : ℕ) (C G t : ℝ) (R : ℝ) (m : ℕ) : ℝ :=
  gridRepairConstant q * (C + |t| * G) * R *
    (Real.rpow (R / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
      Real.rpow (R / ((m : ℝ) ^ q)) (-(1 / 2)))

/-- The repair *rate*: the repair divided by the intensity.  It only depends on
the ratio `R / m ^ q`. -/
noncomputable def kernelBlockRepairRate (q : ℕ) (C G t : ℝ) (x : ℝ) : ℝ :=
  gridRepairConstant q * (C + |t| * G) *
    (Real.rpow x (2 / (q : ℝ) - 1 / 2) + Real.rpow x (-(1 / 2)))

/-- The repair normalized by the intensity equals the repair rate at `R / m ^ q`. -/
theorem kernelBlockRepairExpr_div (q : ℕ) (C G t R : ℝ) (m : ℕ) (hR : R ≠ 0) :
    kernelBlockRepairExpr q C G t R m / R = kernelBlockRepairRate q C G t (R / ((m : ℝ) ^ q)) := by
  unfold kernelBlockRepairExpr kernelBlockRepairRate
  field_simp

/-! ## Vanishing of the repair rate -/

/-- For `q > 4` the repair rate vanishes at infinity: both exponents are negative. -/
theorem tendsto_kernelBlockRepairRate_zero (q : ℕ) (hq : 4 < q) (C G t : ℝ) :
    Tendsto (kernelBlockRepairRate q C G t) atTop (𝓝 0) := by
  have hqR : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hpos1 : (0 : ℝ) < 1 / 2 - 2 / (q : ℝ) := by
    have h : 2 / (q : ℝ) < 1 / 2 := by
      rw [div_lt_iff₀ hq0]
      linarith
    linarith
  have h1 : Tendsto (fun x : ℝ => Real.rpow x (2 / (q : ℝ) - 1 / 2)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop hpos1
    refine h.congr fun x => ?_
    congr 1
    ring
  have h2 : Tendsto (fun x : ℝ => Real.rpow x (-(1 / 2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hsum : Tendsto (fun x : ℝ => Real.rpow x (2 / (q : ℝ) - 1 / 2) +
      Real.rpow x (-(1 / 2))) atTop (𝓝 0) := by
    simpa only [add_zero] using h1.add h2
  unfold kernelBlockRepairRate
  simpa only [mul_assoc, mul_zero] using hsum.const_mul (gridRepairConstant q * (C + |t| * G))

/-- **The normalized repair vanishes.**  For a fixed positive block count the
repair divided by the intensity tends to zero. -/
theorem tendsto_kernelBlockRepairExpr_div_zero (q : ℕ) (hq : 4 < q) (C G t : ℝ)
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun R : ℝ => kernelBlockRepairExpr q C G t R m / R) atTop (𝓝 0) := by
  have hmq : (0 : ℝ) < (m : ℝ) ^ q := by positivity
  have hx : Tendsto (fun R : ℝ => R / ((m : ℝ) ^ q)) atTop atTop :=
    tendsto_id.atTop_div_const hmq
  have hlim := (tendsto_kernelBlockRepairRate_zero q hq C G t).comp hx
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
  exact (kernelBlockRepairExpr_div q C G t R m hR).symm

/-- **The normalized repair vanishes for an intensity-dependent block count.**
If the block count grows so slowly that `m R ^ q = o(R)` — equivalently the
ratio `R / m R ^ q` tends to infinity — then the normalized repair vanishes. -/
theorem tendsto_kernelBlockRepairExpr_div_zero_of_ratio (q : ℕ) (hq : 4 < q)
    (C G t : ℝ) (mfun : ℝ → ℕ)
    (hx : Tendsto (fun R : ℝ => R / ((mfun R : ℝ) ^ q)) atTop atTop) :
    Tendsto (fun R : ℝ => kernelBlockRepairExpr q C G t R (mfun R) / R) atTop (𝓝 0) := by
  have hlim := (tendsto_kernelBlockRepairRate_zero q hq C G t).comp hx
  refine hlim.congr' ?_
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))] with R hRpos
  have hR0 : R ≠ 0 := by
    rintro rfl
    have hzero : (0 : ℝ) / ((mfun 0 : ℝ) ^ q) = 0 := by simp
    rw [hzero] at hRpos
    exact lt_irrefl 0 hRpos
  exact (kernelBlockRepairExpr_div q C G t R (mfun R) hR0).symm


/-! ## The block comparison with the named repair -/

/-- The kernel-marked block comparison of `FinslerOriginalKernelBlockComparison.lean`
with the repair written as `kernelBlockRepairExpr`. -/
theorem kernelMarkedPressure_le_blockScale_add_repairExpr
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (R : ℝ≥0) {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    kernelMarkedPressure q A B Ks Kt R kin g t ≤
      blockKernelPressureSum q m Ks Kt (R / (m ^ q : ℝ≥0)) kin g t +
        kernelBlockRepairExpr q C G t (R : ℝ) m := by
  unfold kernelBlockRepairExpr
  exact kernelMarkedPressure_le_blockScale_add_repair q m J hq hm hJ hJ2 Ks Kt R
    (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb

/-! ## The normalized upper comparison -/

/-- **Normalized upper pressure comparison.**  After dividing the block
comparison by the intensity, the repair is the repair rate at `R / m ^ q`, which
vanishes as `R → ∞`.  Hence for every `ε > 0` the normalized reference pressure
is eventually bounded by the normalized aggregate block pressure plus `ε`. -/
theorem eventually_kernelMarkedPressure_div_le_blockSum_div_add
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop,
      kernelMarkedPressure q A B Ks Kt (Real.toNNReal R) kin g t / R ≤
        blockKernelPressureSum q m Ks Kt (Real.toNNReal R / (m ^ q : ℝ≥0)) kin g t / R
          + ε := by
  classical
  have hrep := tendsto_kernelBlockRepairExpr_div_zero q hq C G t m hm
  filter_upwards [hrep.eventually (Iio_mem_nhds hε), eventually_gt_atTop (0 : ℝ)]
    with R hR hRpos
  have hcmp := kernelMarkedPressure_le_blockScale_add_repairExpr q m J hq hm hJ hJ2
    Ks Kt (Real.toNNReal R) (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog
    hg hgb
  have hcoe : ((Real.toNNReal R : ℝ≥0) : ℝ) = R := Real.coe_toNNReal R (le_of_lt hRpos)
  rw [hcoe] at hcmp
  have hdiv := div_le_div_of_nonneg_right hcmp (le_of_lt hRpos)
  rw [add_div] at hdiv
  linarith

/-- The normalized upper comparison with an explicit vanishing remainder:
eventually, the difference of the normalized reference pressure and the
normalized aggregate block pressure is at most the repair rate. -/
theorem eventually_kernelMarkedPressure_div_sub_blockSum_div_le_repair
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    ∀ᶠ R : ℝ in atTop,
      kernelMarkedPressure q A B Ks Kt (Real.toNNReal R) kin g t / R -
          blockKernelPressureSum q m Ks Kt (Real.toNNReal R / (m ^ q : ℝ≥0)) kin g t / R
        ≤ kernelBlockRepairExpr q C G t R m / R := by
  classical
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
  have hcmp := kernelMarkedPressure_le_blockScale_add_repairExpr q m J hq hm hJ hJ2
    Ks Kt (Real.toNNReal R) (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog
    hg hgb
  have hcoe : ((Real.toNNReal R : ℝ≥0) : ℝ) = R := Real.coe_toNNReal R (le_of_lt hRpos)
  rw [hcoe] at hcmp
  have hdiv := div_le_div_of_nonneg_right hcmp (le_of_lt hRpos)
  rw [add_div] at hdiv
  linarith


/-! ## The normalized comparison at scale level -/

/-- **Scale-level block comparison with the aggregate block pressure.**  At
scale `L` the reference kernel-marked scale pressure at the larger scale
`m * L` is bounded by the average of the block-rescaled scale pressures at `L`
plus the (scale-only) repair error. -/
theorem kernelMarkedScalePressure_le_blockSum_add_gridRepairError
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
    {L : ℝ} (hL : 0 < L) :
    kernelMarkedScalePressure q A B Ks Kt kin g ((m : ℝ) * L) t ≤
      (1 / (((m ^ q : ℕ) : ℝ))) *
        (∑ c : Fin q → Fin m,
          kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
            kin g L t) +
        gridRepairError q (gridRepairConstant q) C G t L := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmL : (0 : ℝ) < (m : ℝ) * L := mul_pos hmR hL
  have hLq : (0 : ℝ) < L ^ q := pow_pos hL q
  have hred_eq : (Real.toNNReal (((m : ℝ) * L) ^ q) / ((m : ℝ≥0) ^ q)) =
      Real.toNNReal (L ^ q) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ hLq.le]
    push_cast
    exact mul_pow_div_pow q m hm L
  have hbase := kernelMarkedPressure_le_blockScale_add_repairExpr (q := q) (m := m)
    (J := J) hq hm hJ hJ2 Ks Kt (Real.toNNReal (((m : ℝ) * L) ^ q)) (t := t)
    hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb
  rw [hred_eq, Real.coe_toNNReal _ (by positivity)] at hbase
  unfold blockKernelPressureSum at hbase
  have hcongr : (∑ c : Fin q → Fin m,
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
          kin g L t) =
      ∑ c : Fin q → Fin m,
        kernelMarkedPressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
          (Real.toNNReal (L ^ q)) kin g t / L ^ q :=
    Finset.sum_congr rfl fun c _ =>
      kernelMarkedScalePressure_of_pos q A B (blockLocalKernel Ks c)
        (blockLocalKernel Kt c) (kin := kin) (g := g) (R := L) (t := t) hL
  have hsum : (∑ c : Fin q → Fin m,
        kernelMarkedPressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
          (Real.toNNReal (L ^ q)) kin g t) / (((m : ℝ) * L) ^ q) =
      (1 / (((m ^ q : ℕ) : ℝ))) *
        (∑ c : Fin q → Fin m,
          kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
            kin g L t) := by
    rw [hcongr, ← Finset.sum_div, mul_pow, Nat.cast_pow]
    have hmq0 : ((m : ℝ) ^ q) ≠ 0 := by positivity
    have hLq0 : L ^ q ≠ 0 := by positivity
    field_simp
  have hrepair : kernelBlockRepairExpr q C G t (((m : ℝ) * L) ^ q) m /
      (((m : ℝ) * L) ^ q) = gridRepairError q (gridRepairConstant q) C G t L := by
    have hmLq0 : (((m : ℝ) * L) ^ q) ≠ 0 := by positivity
    rw [kernelBlockRepairExpr_div q C G t _ m hmLq0]
    unfold kernelBlockRepairRate gridRepairError
    rw [rpow_div_mul_pow_kinetic q (by omega : 0 < q) hL m hm,
      rpow_div_mul_pow_probe q (by omega : 0 < q) hL m hm]
  rw [kernelMarkedScalePressure_of_pos q A B Ks Kt (kin := kin) (g := g)
    (R := (m : ℝ) * L) (t := t) hmL]
  have hbase' := div_le_div_of_nonneg_right hbase (le_of_lt (pow_pos hmL q))
  rw [add_div, hsum, hrepair] at hbase'
  exact hbase'

/-! ## The upper readout bound for the `hupper` input -/

/-- **Upper readout bound for the `hupper` interface.**  Assume the block
pressure limit identification: the average of the block-rescaled scale
pressures converges to a value `p` at the fixed probe and tilt.  Then the
reference kernel-marked scale pressure is eventually bounded by `p + ε` for
every `ε > 0`.  This is the `hupper`-shaped input of the expectation upper
bound, reduced to the identification of the block pressure limit. -/
theorem eventually_kernelMarkedScalePressure_le_of_blockPressureLimit
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
    {p : ℝ}
    (hlimit : Tendsto (fun L : ℝ =>
        (1 / (((m ^ q : ℕ) : ℝ))) * (∑ c : Fin q → Fin m,
          kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) kin g L t)) atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      kernelMarkedScalePressure q A B Ks Kt kin g R t ≤ p + ε := by
  intro ε hε
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hLtendsto : Tendsto (fun R : ℝ => R / (m : ℝ)) atTop atTop :=
    tendsto_id.atTop_div_const hmR
  have hrep : ∀ᶠ L : ℝ in atTop,
      gridRepairError q (gridRepairConstant q) C G t L ≤ ε / 2 :=
    (tendsto_gridRepairError_atTop hq (gridRepairConstant q) C G t).eventually
      (Iic_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  have hlim : ∀ᶠ L : ℝ in atTop,
      (1 / (((m ^ q : ℕ) : ℝ))) * (∑ c : Fin q → Fin m,
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) ≤ p + ε / 2 :=
    hlimit.eventually (Iic_mem_nhds (by linarith : p < p + ε / 2))
  filter_upwards [hLtendsto.eventually (hrep.and hlim), eventually_gt_atTop (0 : ℝ)]
    with R hRL hRpos
  obtain ⟨hrepR, hlimR⟩ := hRL
  have hLpos : (0 : ℝ) < R / (m : ℝ) := div_pos hRpos hmR
  have hscale := kernelMarkedScalePressure_le_blockSum_add_gridRepairError
    (q := q) (m := m) (J := J) hq hm hJ hJ2 Ks Kt (t := t) hC0 hG0
    hkin hkin_nonneg hkin_bound hkin_homog hg hgb (L := R / (m : ℝ)) hLpos
  have hmul : ((m : ℝ) * (R / (m : ℝ))) = R := by
    field_simp
  rw [hmul] at hscale
  linarith

end OTSelector.Reconstruction
