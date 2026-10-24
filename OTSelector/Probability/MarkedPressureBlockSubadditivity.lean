import OTSelector.Probability.MarkedPressureBlockComparison
import OTSelector.Probability.GridRepairArithmetic
import OTSelector.Probability.GridRepairError
import OTSelector.Probability.GridRepairScaling
import OTSelector.Probability.MarkedPressureLimit
import OTSelector.Probability.MarkedBlockValueIntegral

/-!
# Pressure block subadditivity

Integrating the deterministic grid comparison against the two-cloud marked
Poisson law expresses the pressure at intensity `R` through the pressure at the
reduced intensity `R / m ^ q`, plus the expected hierarchical repair cost.  The
leaf-block expectation identity

`E [sum_c leafBlockValue c] = m^q * pressure (R / m^q)`

is isolated as the hypothesis `hleaf` (it is proved in
`MarkedBlockValueIntegral`), together with the integrability of the leaf sum.
The repair expectation is bounded by `integral_gridRepair_le`, and the resulting
elementary sum by `grid_repair_sum_le`.
-/

open scoped BigOperators NNReal
open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

set_option maxHeartbeats 1600000 in
/-- **Pressure block subadditivity at a fixed intensity.**  The marked pressure
at intensity `R` is at most `m ^ q` times the pressure at intensity `R / m ^ q`,
plus a repair error of the sharp high-dimensional shape
`Kq (C + |t| G) R ((R / m^q) ^ (2/q - 1/2) + (R / m^q) ^ (-1/2))`.

The hypothesis `hleaf` is the integrated leaf-block identity and `hIntBlock` the
integrability of the leaf sum; both are supplied by the block-value module. -/
theorem markedPressure_le_blockScale_add_repair
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) {t C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) :
    markedPressure q A B α β R kin g t ≤
        (((m ^ q : ℕ) : ℝ)) *
            markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
          gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
            (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
              Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))) := by
  classical
  -- The leaf-block sum rewrites as a sum over the real blocks.
  have hblockSum_eq : (fun ω : TwoMarkedCloudSpace q A B =>
      ∑ c : Fin q → Fin (2 ^ J + 1),
        markedBlockValue q m J hm hJ (R : ℝ) t kin g ω c) =
      fun ω : TwoMarkedCloudSpace q A B =>
        ∑ b : Fin q → Fin m,
          markedBlockValue q m J hm hJ (R : ℝ) t kin g ω
            (blockLeafLabel q m J hJ b) := by
    funext ω
    exact markedBlockValue_sum_eq_realBlocks (q := q) (m := m) (J := J) hm hJ
      (R : ℝ) t (kin := kin) (g := g) ω
  -- Integrability of the leaf-block sum.
  have hIntBlock : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ∑ c : Fin q → Fin (2 ^ J + 1),
        markedBlockValue q m J hm hJ (R : ℝ) t kin g ω c)
      (twoMarkedCloudLaw (q := q) A B α β R) := by
    have hR : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
        ∑ b : Fin q → Fin m,
          markedBlockValue q m J hm hJ (R : ℝ) t kin g ω
            (blockLeafLabel q m J hJ b))
        (twoMarkedCloudLaw (q := q) A B α β R) := by
      apply integrable_finsetSum
      intro b _
      exact integrable_markedBlockValue (q := q) (m := m) (J := J) (hm := hm)
        (hJ := hJ) (hq := by omega) (α := α) (β := β) (R := R) (r := (R : ℝ))
        (hr := R.coe_nonneg) (hrR := rfl) (C := C) (G := G) (hC0 := hC0)
        (hG0 := hG0) (kin := kin) (hkin := hkin) (hkin_bound := hkin_bound)
        (hkin_homog := hkin_homog) (g := g) (hg := hg) (hgb := hgb) (b := b)
    exact hR.congr (Filter.Eventually.of_forall fun ω => (congrFun hblockSum_eq ω).symm)
  -- The integrated leaf-block identity.
  have hleaf : ∫ ω, (∑ c : Fin q → Fin (2 ^ J + 1),
        markedBlockValue q m J hm hJ (R : ℝ) t kin g ω c)
        ∂(twoMarkedCloudLaw (q := q) A B α β R) =
      (((m ^ q : ℕ) : ℝ)) *
        markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t :=
    integral_gridBlockSum_eq (q := q) (m := m) (J := J) (hm := hm) (hJ := hJ)
      (hq := by omega) (A := A) (B := B) (α := α) (β := β) (R := R)
      (r := (R : ℝ)) (hr := R.coe_nonneg) (hrR := rfl) (t := t) (C := C) (G := G)
      (kin := kin) (hkin := hkin) (hkin_bound := hkin_bound)
      (hkin_homog := hkin_homog) (g := g) (hg := hg) (hgb := hgb)
  -- Integrability of the repair term.
  have hDint : ∀ k, Integrable
      (fun ω : TwoMarkedCloudSpace q A B => markedGridDiscrepancy q m J k hm hJ ω)
      (twoMarkedCloudLaw (q := q) A B α β R) :=
    fun k => integrable_markedGridDiscrepancy q m J k hm hJ A B α β R
  have hIntRepair : Integrable (fun ω : TwoMarkedCloudSpace q A B =>
      ∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
          (markedGridDiscrepancy q m J k hm hJ ω -
            markedGridDiscrepancy q m J (k - 1) hm hJ ω))
      (twoMarkedCloudLaw (q := q) A B α β R) := by
    apply integrable_finsetSum
    intro k _
    exact ((hDint k).sub (hDint (k - 1))).const_mul _
  -- The deterministic comparison holds pointwise.
  have hpt : ∀ ω : TwoMarkedCloudSpace q A B,
      markedTilted q (R : ℝ) kin g t ω ≤
        (∑ c : Fin q → Fin (2 ^ J + 1),
          markedBlockValue q m J hm hJ (R : ℝ) t kin g ω c) +
        ∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy q m J k hm hJ ω -
              markedGridDiscrepancy q m J (k - 1) hm hJ ω) := by
    intro ω
    exact markedTilted_le_gridBlockSum_add_repair (q := q) (m := m) (J := J)
      hm hJ hJ2 (r := (R : ℝ)) (t := t) (C := C) (G := G)
      R.coe_nonneg hC0 hG0 hkin_nonneg hkin_bound hgb ω
  -- The ambient marked pressure is integrable.
  have hIntT : Integrable (markedTilted q (R : ℝ) kin g t)
      (twoMarkedCloudLaw (q := q) A B α β R) :=
    integrable_markedTilted q α β R R.coe_nonneg hC0 hG0 hkin hkin_bound hg hgb t
  -- Integrate the pointwise comparison.
  have hmono : ∫ ω, markedTilted q (R : ℝ) kin g t ω
        ∂(twoMarkedCloudLaw (q := q) A B α β R) ≤
      ∫ ω, ((∑ c : Fin q → Fin (2 ^ J + 1),
          markedBlockValue q m J hm hJ (R : ℝ) t kin g ω c) +
        ∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy q m J k hm hJ ω -
              markedGridDiscrepancy q m J (k - 1) hm hJ ω))
        ∂(twoMarkedCloudLaw (q := q) A B α β R) :=
    integral_mono hIntT (hIntBlock.add hIntRepair) hpt
  rw [integral_add hIntBlock hIntRepair, hleaf] at hmono
  -- Bound the expected repair.
  have hrep := integral_gridRepair_le (q := q) (m := m) (J := J) hm hJ
    (A := A) (B := B) α β R (r := (R : ℝ)) (t := t) (C := C) (G := G)
    R.coe_nonneg hC0 hG0
  -- The elementary repair sum is dominated by the sharp expression.
  obtain ⟨hKq0, hKq⟩ := grid_repair_sum_le q J hq m hm hJ2
    (R := (R : ℝ)) (C := C) (G := G) (t := t) R.coe_nonneg hC0 hG0
  refine hmono.trans ?_
  -- Match the repair-bound summands on `Icc 1 J`.
  have hsum_eq : (∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ))) =
      (1 / 2) * (∑ k ∈ Finset.Icc 1 J,
        (16 * ((R : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
            2 * |t| * G) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    unfold markedGridRepairBound markedGridRepairWeight
    rw [if_neg (by omega : k ≠ 0)]
    ring
  calc (((m ^ q : ℕ) : ℝ)) *
        markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
        ∫ ω, (∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
            (markedGridDiscrepancy q m J k hm hJ ω -
              markedGridDiscrepancy q m J (k - 1) hm hJ ω))
          ∂(twoMarkedCloudLaw (q := q) A B α β R)
      ≤ (((m ^ q : ℕ) : ℝ)) *
          markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
        ∑ k ∈ Finset.Icc 1 J,
          markedGridRepairBound q (R : ℝ) C t G k * (1 / 2 : ℝ) *
            Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
        linarith [hrep]
    _ = (((m ^ q : ℕ) : ℝ)) *
          markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
        (1 / 2) * (∑ k ∈ Finset.Icc 1 J,
          (16 * ((R : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) +
              2 * |t| * G) *
            Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ))) := by
        rw [hsum_eq]
    _ ≤ (((m ^ q : ℕ) : ℝ)) *
          markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
        gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
          (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
            Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))) := by
        linarith [hKq]

/-! ## The scale form of the block comparison -/

/-- The explicit repair constant is nonnegative when `q > 4`. -/
theorem gridRepairConstant_nonneg {q : ℕ} (hq : 4 < q) : 0 ≤ gridRepairConstant q := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hq4R : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h2lt : (2 : ℝ) < (q : ℝ) / 2 := by linarith
  have hS_pos : 0 < (2 : ℝ) ^ ((q : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hS_gt4 : (4 : ℝ) < (2 : ℝ) ^ ((q : ℝ) / 2) := by
    have h2sq : (2 : ℝ) ^ ((2 : ℝ)) = 4 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num) h2lt
    rwa [h2sq] at h
  have hr_gt1 : (1 : ℝ) < (2 : ℝ) ^ ((q : ℝ) / 2) / 4 := by linarith
  have hc_nonneg : 0 ≤ (q : ℝ) / 2 - 2 := by linarith
  have hKdef : gridRepairConstant q =
      32 * (q : ℝ) * Real.sqrt 2 * (2 : ℝ) ^ ((q : ℝ) / 2) *
          ((2 : ℝ) ^ ((q : ℝ) / 2) / 4) /
          ((2 : ℝ) ^ ((q : ℝ) / 2) / 4 - 1) * (2 : ℝ) ^ ((q : ℝ) / 2 - 2) +
        Real.sqrt 2 * ((2 : ℝ) ^ ((q : ℝ) / 2)) ^ 3 /
          ((2 : ℝ) ^ ((q : ℝ) / 2) - 1) := by
    simp only [gridRepairConstant]
  rw [hKdef]
  have h1 : 0 ≤ 32 * (q : ℝ) * Real.sqrt 2 * (2 : ℝ) ^ ((q : ℝ) / 2) *
      ((2 : ℝ) ^ ((q : ℝ) / 2) / 4) /
      ((2 : ℝ) ^ ((q : ℝ) / 2) / 4 - 1) * (2 : ℝ) ^ ((q : ℝ) / 2 - 2) := by
    apply mul_nonneg
    · apply div_nonneg
      · positivity
      · linarith
    · positivity
  have h2 : 0 ≤ Real.sqrt 2 * ((2 : ℝ) ^ ((q : ℝ) / 2)) ^ 3 /
      ((2 : ℝ) ^ ((q : ℝ) / 2) - 1) := by
    apply div_nonneg
    · positivity
    · linarith
  linarith

set_option maxHeartbeats 1600000 in
/-- **Scale form of the pressure block comparison.**  If the pressure at every
intensity satisfies the block comparison with the explicit constant, then at the
scale level the pressure is block-subadditive with the error term
`gridRepairError`. -/
theorem markedScalePressure_block_le
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G t : ℝ} {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hpressure : ∀ R : ℝ≥0,
      markedPressure q A B α β R kin g t ≤
        (((m ^ q : ℕ) : ℝ)) *
            markedPressure q A B α β (R / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
          gridRepairConstant q * (C + |t| * G) * (R : ℝ) *
            (Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (2 / (q : ℝ) - 1 / 2) +
              Real.rpow ((R : ℝ) / ((m : ℝ) ^ q)) (-(1 / 2))))
    {L : ℝ} (hL : 0 < L) :
    markedScalePressure q A B α β kin g ((m : ℝ) * L) t ≤
      markedScalePressure q A B α β kin g L t +
        gridRepairError q (gridRepairConstant q) C G t L := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmL : (0 : ℝ) < (m : ℝ) * L := mul_pos hmR hL
  have hLq : (0 : ℝ) < L ^ q := pow_pos hL q
  rw [markedScalePressure_of_pos q α β hmL, markedScalePressure_of_pos q α β hL]
  -- The reduced intensity is `L ^ q`.
  have hred : ((Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) = L ^ q := by
    rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity)]
    push_cast
    exact mul_pow_div_pow q m hm L
  have hred_eq : (Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0)) =
      Real.toNNReal (L ^ q) := by
    apply NNReal.coe_injective
    rw [hred, Real.coe_toNNReal _ hLq.le]
  -- Rewrite the pressure comparison at intensity `(m L) ^ q` in plain real form.
  have hbase := hpressure (Real.toNNReal (((m : ℝ) * L) ^ q))
  have hcoe : ((Real.toNNReal (((m : ℝ) * L) ^ q) : ℝ≥0) : ℝ) = ((m : ℝ) * L) ^ q :=
    Real.coe_toNNReal _ (by positivity)
  rw [hcoe, mul_pow_div_pow q m hm L] at hbase
  -- The first term simplifies to the pressure at scale `L`.
  have hfirst : ((((m ^ q : ℕ) : ℝ)) *
        markedPressure q A B α β
          (Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0)) kin g t) /
        (((m : ℝ) * L) ^ q) =
      markedPressure q A B α β (Real.toNNReal (L ^ q)) kin g t / L ^ q := by
    rw [hred_eq, mul_pow]
    field_simp
    rw [Nat.cast_pow]
    ring
  -- The error term simplifies to `gridRepairError` at scale `L`.
  have hLrpow : ∀ a : ℝ, Real.rpow (L ^ q) a = L ^ ((q : ℝ) * a) := by
    intro a
    rw [← Real.rpow_natCast L q]
    exact (Real.rpow_mul hL.le (q : ℝ) a).symm
  have herr : (gridRepairConstant q * (C + |t| * G) * (((m : ℝ) * L) ^ q) *
        (Real.rpow (L ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow (L ^ q) (-(1 / 2)))) /
        (((m : ℝ) * L) ^ q) =
      gridRepairError q (gridRepairConstant q) C G t L := by
    rw [hLrpow, hLrpow]
    have h1 : (q : ℝ) * (2 / (q : ℝ) - 1 / 2) = 2 - (q : ℝ) / 2 := by
      field_simp
    have h2 : (q : ℝ) * (-(1 / 2)) = -((q : ℝ) / 2) := by ring
    rw [h1, h2]
    unfold gridRepairError
    rw [mul_pow]
    field_simp
    rfl
  calc markedPressure q A B α β (Real.toNNReal (((m : ℝ) * L) ^ q)) kin g t /
        (((m : ℝ) * L) ^ q)
      ≤ ((((m ^ q : ℕ) : ℝ)) *
          markedPressure q A B α β
            (Real.toNNReal (((m : ℝ) * L) ^ q) / ((m ^ q : ℕ) : ℝ≥0)) kin g t +
        gridRepairConstant q * (C + |t| * G) * (((m : ℝ) * L) ^ q) *
          (Real.rpow (L ^ q) (2 / (q : ℝ) - 1 / 2) +
            Real.rpow (L ^ q) (-(1 / 2)))) /
        (((m : ℝ) * L) ^ q) :=
        div_le_div_of_nonneg_right hbase (le_of_lt (pow_pos hmL q))
    _ = markedPressure q A B α β (Real.toNNReal (L ^ q)) kin g t / L ^ q +
          gridRepairError q (gridRepairConstant q) C G t L := by
        rw [add_div, hfirst, herr]

end OTSelector.Probability
