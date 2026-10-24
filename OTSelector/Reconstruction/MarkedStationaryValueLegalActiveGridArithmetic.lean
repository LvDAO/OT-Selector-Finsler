import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveExpectation
import OTSelector.Reconstruction.MarkedStationaryValueLegalGridArithmetic
import OTSelector.Probability.MicroscopicGridScale

/-! Parent-scale repair for original binomial active subclouds in arbitrary
measurable shapes. Only domination by the enclosing box mass is used. -/
open Filter
open scoped BigOperators Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The original per-sample parent repair budget, expressed in the enclosing
box density and the true mass of a microscopic grid cell. -/
def activeGridRepairError (q : ℕ) (K C G t density mass : ℝ) : ℝ :=
  K * (C + |t| * G) * density *
    (Real.rpow (density * mass) (2 / (q : ℝ) - 1 / 2) +
      Real.rpow (density * mass) (-(1 / 2 : ℝ)))

/-- The repair budget is continuous at the actual positive fixed-scale count
intensity, even when the retained measurable shape has arbitrarily small mass. -/
theorem continuousAt_activeGridRepairError (q : ℕ) (K C G t : ℝ)
    {density mass : ℝ} (hd : 0 < density) (hm : 0 < mass) :
    ContinuousAt (activeGridRepairError q K C G t density) mass := by
  have hx : ContinuousAt (fun x : ℝ ↦ density * x) mass := continuousAt_const.mul continuousAt_id
  have h1 := (Real.continuousAt_rpow_const (density * mass)
    (2 / (q : ℝ) - 1 / 2) (Or.inl (mul_pos hd hm).ne')).comp hx
  have h2 := (Real.continuousAt_rpow_const (density * mass)
    (-(1 / 2 : ℝ)) (Or.inl (mul_pos hd hm).ne')).comp hx
  exact (h1.add h2).const_mul _

/-- In dimension q>4 the actual per-sample hierarchical repair cost vanishes
as the microscopic cell mass grows. -/
theorem tendsto_activeGridRepairError_atTop {q : ℕ} (hq : 4 < q)
    (K C G t : ℝ) {density : ℝ} (hd : 0 < density) :
    Tendsto (activeGridRepairError q K C G t density) atTop (𝓝 0) := by
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hpow : 0 < (q : ℝ) := by linarith
  have he : 0 < 1 / 2 - 2 / (q : ℝ) := by
    have h : 2 / (q : ℝ) < 1 / 2 := (div_lt_iff₀ hpow).mpr (by linarith)
    linarith
  have hx : Tendsto (fun x : ℝ ↦ density * x) atTop atTop :=
    tendsto_id.const_mul_atTop hd
  have h1 := (tendsto_rpow_neg_atTop he).comp hx
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hx
  have h := (h1.add h2).const_mul (K * (C + |t| * G) * density)
  unfold activeGridRepairError
  convert h using 1 <;>
    simp only [Function.comp_def, neg_sub, add_zero, mul_zero, Real.rpow_eq_pow]

/-- At each fixed microscopic side, the original rounded integer grids have
the required repair-budget limit. This takes the sample limit first. -/
theorem tendsto_activeGridRepairError_microscopicGrid {q : ℕ} (hq : 0 < q)
    (K C G t : ℝ) {density L : ℝ} (hd : 0 < density) (hL : 0 < L) :
    Tendsto (fun N : ℝ ↦ activeGridRepairError q K C G t density
      (N * OTSelector.Probability.microscopicGridSide q L N ^ q)) atTop
      (𝓝 (activeGridRepairError q K C G t density (L ^ q))) :=
  (continuousAt_activeGridRepairError q K C G t hd (pow_pos hL q)).tendsto.comp
    (OTSelector.Probability.tendsto_microscopicGrid_mass hq hL)

/-- Only after the original sample limit is taken, the fixed microscopic side
may grow. Its repair error then tends to zero for q>4. -/
theorem tendsto_activeGridRepairError_microscopicSide {q : ℕ} (hq : 4 < q)
    (K C G t : ℝ) {density : ℝ} (hd : 0 < density) :
    Tendsto (fun L : ℝ ↦ activeGridRepairError q K C G t density (L ^ q))
      atTop (𝓝 0) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply (tendsto_activeGridRepairError_atTop hq K C G t hd).comp
  simpa only [Real.rpow_natCast] using tendsto_rpow_atTop hqR

/-- The actual active mass may be smaller than its enclosing box mass. The
original binomial fluctuations remain bounded by the box-rate grid error,
without a positive lower bound on the shape mass or equal child masses. -/
theorem active_legal_grid_repair_sum_le
    (q depth bins types N : ℕ) (hq : 4 < q)
    (m : ℕ) (hm : 0 < m) (hdepth2 : 2 ^ depth ≤ 2 * m)
    (typeCount : ℕ → ℕ)
    (htypes : ∀ k, k < depth → typeCount k ≤ (2 ^ (k + 1) + 1) ^ q * types)
    {p r C G t : ℝ} (hr : 0 ≤ r) (hmass : (N : ℝ) * p ≤ r)
    (hC : 0 ≤ C) (hG : 0 ≤ G) :
    (∑ k ∈ Finset.range depth,
      Real.sqrt (2 * (N : ℝ) * typeCount k * p) *
        (2 * ((bins : ℝ) + 1) * legalGridEdgeBound q r C G t k)) ≤
      legalGridRepairConstant q bins types * (C + |t| * G) * r *
        (Real.rpow (r / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow (r / (m : ℝ) ^ q) (-(1 / 2))) := by
  refine (Finset.sum_le_sum (fun k hk ↦ ?_)).trans
    (legal_grid_repair_sum_le q depth bins types hq m hm hdepth2 hr hC hG).2
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (by positivity) (legalGridEdgeBound_nonneg q k hr hC hG))
  apply Real.sqrt_le_sqrt
  have hcard : (typeCount k : ℝ) ≤ (((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ) * types := by
    exact_mod_cast htypes k (Finset.mem_range.mp hk)
  calc
    2 * (N : ℝ) * typeCount k * p = 2 * ((N : ℝ) * p) * typeCount k := by ring
    _ ≤ 2 * r * typeCount k := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by norm_num)) (Nat.cast_nonneg _)
    _ ≤ 2 * r * (((((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ)) * types) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)

/-- Dividing by the original sample size leaves the actual enclosing-box
density error, with no inverse retained-shape mass. -/
theorem active_legal_grid_repair_sum_div_le
    (q depth bins types N : ℕ) (hq : 4 < q) (hN : 0 < N)
    (m : ℕ) (hm : 0 < m) (hdepth2 : 2 ^ depth ≤ 2 * m)
    (typeCount : ℕ → ℕ)
    (htypes : ∀ k, k < depth → typeCount k ≤ (2 ^ (k + 1) + 1) ^ q * types)
    {p density C G t : ℝ} (hd : 0 ≤ density) (hmass : p ≤ density)
    (hC : 0 ≤ C) (hG : 0 ≤ G) :
    (∑ k ∈ Finset.range depth,
      Real.sqrt (2 * (N : ℝ) * typeCount k * p) *
        (2 * ((bins : ℝ) + 1) * legalGridEdgeBound q ((N : ℝ) * density) C G t k)) / N ≤
      activeGridRepairError q (legalGridRepairConstant q bins types) C G t density
        ((N : ℝ) / (m : ℝ) ^ q) := by
  have hNp : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have h := active_legal_grid_repair_sum_le q depth bins types N hq m hm hdepth2 (t := t)
    typeCount htypes (mul_nonneg hNp hd) (mul_le_mul_of_nonneg_left hmass hNp) hC hG
  have hdiv := div_le_div_of_nonneg_right h hNp
  convert hdiv using 1 <;> try rfl
  unfold activeGridRepairError
  have hratio : (N : ℝ) * density / (m : ℝ) ^ q = density * ((N : ℝ) / (m : ℝ) ^ q) := by ring
  rw [hratio]
  have hN0 : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp

end OTSelector.Reconstruction
