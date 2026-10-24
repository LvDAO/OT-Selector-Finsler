import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineBinomialLaw

/-! Exact original finite-binomial shape errors sum by filling volume. The
normalization retains the original sample size; changing microfamilies require
no independence between different cells and no boundary regularity. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B J : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Literal finite-prefix physical expectation on an original binomial shape.
The physical normalization and the original full-box probability are separate. -/
def affineBinomialShapeExpectation (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) (r side : ℝ) (origin : Fin q → ℝ) (S : Set (Fin q → ℝ))
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ) : ℝ :=
  ∫ d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B),
    unclampedBlockLegalTilted q source target r kin probe t
      (mapBlockData (affineMarkedPoint origin side) d.1)
      (mapBlockData (affineMarkedPoint origin side) d.2)
    ∂(binomialShapeBlockLaw q α N p S).prod (binomialShapeBlockLaw q β N p S)

/-- Finite errors with the actual binomial mean normalize to original filling
volume. A cap on the full-box probability is sufficient, including p=0 or 1. -/
theorem normalized_binomial_shape_sum_sub_le (cells : Finset J)
    {N : ℕ} (hN : 0 < N) {p density volume edge : ℝ}
    (hp : p ≤ density * volume) (hedge : 0 ≤ edge)
    (hole value model : J → ℝ) (hhole : ∀ j ∈ cells, 0 ≤ hole j)
    (hcell : ∀ j ∈ cells,
      |value j - model j| ≤ (2 * ((N : ℝ) * p) * hole j) * edge) :
    |(∑ j ∈ cells, value j) / N - (∑ j ∈ cells, model j) / N| ≤
      (2 * density * edge) * (volume * ∑ j ∈ cells, hole j) := by
  classical
  have hNReal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsum : |∑ j ∈ cells, (value j - model j)| ≤
      (2 * ((N : ℝ) * p) * edge) * ∑ j ∈ cells, hole j := by
    calc
      _ ≤ ∑ j ∈ cells, |value j - model j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ cells, (2 * ((N : ℝ) * p) * hole j) * edge :=
        Finset.sum_le_sum fun j hj ↦ hcell j hj
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have heq : (∑ j ∈ cells, value j) / (N : ℝ) -
      (∑ j ∈ cells, model j) / (N : ℝ) =
        (∑ j ∈ cells, (value j - model j)) / (N : ℝ) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq, abs_div, abs_of_pos hNReal]
  calc
    _ ≤ ((2 * ((N : ℝ) * p) * edge) * ∑ j ∈ cells, hole j) / N :=
      div_le_div_of_nonneg_right hsum hNReal.le
    _ = (2 * p * edge) * ∑ j ∈ cells, hole j := by field_simp
    _ ≤ (2 * (density * volume) * edge) * ∑ j ∈ cells, hole j := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg hhole)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hedge
    _ = _ := by ring

/-- The literal original shape-prefix cost has its normalized finite-family
bound against the same full-box binomial means. No Poissonization of a changing
shape is used. Integrability of each actual physical observable is proved. -/
theorem FiniteScalarBins.normalized_affine_binomialShape_sum_sub_le
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap) (hgap : 0 < gap)
    (q : ℕ) (hq : 0 < q) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (hN : 0 < N) (p : I) (density side : ℝ≥0) (hd : 0 < density)
    (hp : (p : ℝ) ≤ (density : ℝ) * (side : ℝ) ^ q)
    (cells : Finset J) (origin : J → Fin q → ℝ) (S : J → Set (Fin q → ℝ))
    (hS : ∀ j ∈ cells, MeasurableSet (S j))
    (hsource : ∀ᵐ a ∂α, source a ∈ clockSet)
    (hsep : ∀ᵐ ab ∂α.prod β, gap ≤ |target ab.2 - source ab.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun ab : A × B ↦ kin ab.1 ab.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    let intensity := (N : ℝ) * density * side ^ q
    let scaledKin := fun a b v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * kin a b v
    let model := ∫ sample, legalMarkedTilted q source target intensity scaledKin g t sample
      ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)
    (∀ j ∈ cells, Integrable
      (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
        unclampedBlockLegalTilted q source target N kin g t
          (mapBlockData (affineMarkedPoint (origin j) side) d.1)
          (mapBlockData (affineMarkedPoint (origin j) side) d.2))
      ((binomialShapeBlockLaw q α N p (S j)).prod (binomialShapeBlockLaw q β N p (S j)))) ∧
    |(∑ j ∈ cells, affineBinomialShapeExpectation q source target α β N p N side
        (origin j) (S j) kin g t) / N - (cells.card : ℝ) * model / N| ≤
      (2 * (density : ℝ) * (2 * ((D.count : ℝ) + 1) *
        (intensity ^ (2 / (q : ℝ)) *
          (((density : ℝ) ^ (-(2 / (q : ℝ))) * C) * q) + |t| * G))) *
        ((side : ℝ) ^ q * ∑ j ∈ cells, ((cubeMeasure (Fin q) 1) (S j)ᶜ).toReal) := by
  dsimp only
  have hcell (j) (hj : j ∈ cells) :=
    D.integrable_density_affine_binomialShapeLaw_compare hgap q hq hs ht α β
      N p (N : ℝ≥0) density side hd (origin j) (hS j hj) hsource hsep
      hC hG hk hkb hhom hg hgb t
  refine ⟨fun j hj ↦ (hcell j hj).1, ?_⟩
  let model := ∫ sample, legalMarkedTilted q source target ((N : ℝ) * density * side ^ q)
    (fun a b v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * kin a b v) g t sample
      ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)
  let edge := 2 * ((D.count : ℝ) + 1) *
    (((N : ℝ) * density * side ^ q) ^ (2 / (q : ℝ)) *
      (((density : ℝ) ^ (-(2 / (q : ℝ))) * C) * q) + |t| * G)
  have hedge : 0 ≤ edge := by dsimp [edge]; positivity
  have hraw := normalized_binomial_shape_sum_sub_le cells hN hp hedge
    (fun j ↦ ((cubeMeasure (Fin q) 1) (S j)ᶜ).toReal)
    (fun j ↦ affineBinomialShapeExpectation q source target α β N p N side
      (origin j) (S j) kin g t) (fun _ ↦ model)
    (fun _ _ ↦ ENNReal.toReal_nonneg) (fun j hj ↦ (hcell j hj).2)
  simpa only [Finset.sum_const, nsmul_eq_mul] using hraw

/-- A single finite-scale coefficient controls every original binomial shape
error on a bounded tilt interval. It is independent of the microcell family. -/
def FiniteScalarBins.affineShapeFillingConstant
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap)
    (q : ℕ) (density countBound : ℝ≥0) (C G T : ℝ) : ℝ :=
  2 * (density : ℝ) * (2 * ((D.count : ℝ) + 1) *
    ((countBound : ℝ) ^ (2 / (q : ℝ)) *
      (((density : ℝ) ^ (-(2 / (q : ℝ))) * C) * q) + T * G))

theorem FiniteScalarBins.affineShapeFillingConstant_nonneg
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap)
    (q : ℕ) (density countBound : ℝ≥0) {C G T : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hT : 0 ≤ T) :
    0 ≤ D.affineShapeFillingConstant q density countBound C G T := by
  unfold affineShapeFillingConstant
  positivity

/-- The actual physical finite-scale factor is controlled before any shape or
microfamily is chosen. The bound keeps the original density power. -/
theorem FiniteScalarBins.affine_shape_error_coefficient_le
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap)
    (q : ℕ) (density countBound : ℝ≥0) {C G intensity t T : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hi : 0 ≤ intensity)
    (hcount : intensity ≤ countBound) (ht : |t| ≤ T) :
    2 * (density : ℝ) * (2 * ((D.count : ℝ) + 1) *
      (intensity ^ (2 / (q : ℝ)) *
        (((density : ℝ) ^ (-(2 / (q : ℝ))) * C) * q) + |t| * G)) ≤
      D.affineShapeFillingConstant q density countBound C G T := by
  unfold affineShapeFillingConstant
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) density.coe_nonneg)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hi hcount (div_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (by positivity)
  · exact mul_le_mul_of_nonneg_right ht hG

/-- A uniform per-volume bound makes changing finite-family shape errors vanish
on a compact tilt interval. Only their actual summed filling volume must vanish. -/
theorem tendstoUniformlyOn_binomial_shape_error_of_filling
    {ι : Type*} {l : Filter ι} {error : ι → ℝ → ℝ} {filling : ι → ℝ} {K T : ℝ}
    (hfill : Tendsto filling l (𝓝 0))
    (hbound : ∀ᶠ n in l, ∀ t ∈ Icc (-T) T, |error n t| ≤ K * filling n) :
    TendstoUniformlyOn error (fun _ ↦ 0) l (Icc (-T) T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall : Tendsto (fun n ↦ K * filling n) l (𝓝 0) := by
    simpa only [mul_zero] using hfill.const_mul K
  filter_upwards [hbound, hsmall.eventually (gt_mem_nhds hε)] with n hn hsmalln
  intro t ht
  simpa only [Real.dist_eq, zero_sub, abs_neg] using (hn t ht).trans_lt hsmalln

end OTSelector.Reconstruction
