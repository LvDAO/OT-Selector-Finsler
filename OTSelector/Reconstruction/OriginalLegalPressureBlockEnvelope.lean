import OTSelector.Reconstruction.MarkedStationaryValueLegalFiniteClassLimit

/-! Algebraic scale normalization and fixed-box upper envelopes for the actual
original legal pressure, preserving its explicit parent repair. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Normalize the actual original intensity parent comparison without
changing the original graph or marked iid law. -/
theorem finiteClassLegalScalePressure_block_le_of_intensity_bound
    (q m : ℕ) (hq : 0 < q) (hm : 0 < m)
    (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (C G t K : ℝ)
    (hpressure : ∀ r : ℝ≥0, finiteClassLegalPressure q allowed α β r kin probe t ≤
      ((m ^ q : ℕ) : ℝ) * finiteClassLegalPressure q allowed α β (r / (m ^ q : ℝ≥0)) kin probe t +
      K * (C + |t| * G) * (r : ℝ) *
        (Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow ((r : ℝ) / (m : ℝ) ^ q) (-(1 / 2)))) {L : ℝ} (hL : 0 < L) :
    finiteClassLegalScalePressure q allowed α β kin probe ((m : ℝ) * L) t ≤
      finiteClassLegalScalePressure q allowed α β kin probe L t + gridRepairError q K C G t L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmL : 0 < (m : ℝ) * L := mul_pos hmR hL
  have hLq : 0 < L ^ q := pow_pos hL q
  simp only [finiteClassLegalScalePressure, hmL, hL, ↓reduceIte]
  have hred : ((Real.toNNReal (((m : ℝ) * L) ^ q) / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) = L ^ q := by
    rw [NNReal.coe_div, Real.coe_toNNReal _ (by positivity)]
    push_cast
    exact mul_pow_div_pow q m hm L
  have hred_eq : Real.toNNReal (((m : ℝ) * L) ^ q) / (m ^ q : ℝ≥0) = Real.toNNReal (L ^ q) := by
    apply NNReal.coe_injective
    rw [hred, Real.coe_toNNReal _ hLq.le]
  have hbase := hpressure (Real.toNNReal (((m : ℝ) * L) ^ q))
  rw [hred_eq, Real.coe_toNNReal _ (pow_nonneg hmL.le q),
    rpow_div_mul_pow_kinetic q hq hL m hm, rpow_div_mul_pow_probe q hq hL m hm] at hbase
  apply (div_le_iff₀ (pow_pos hmL q)).mpr
  have hcoef : ((m ^ q : ℕ) : ℝ) * finiteClassLegalPressure q allowed α β
      (Real.toNNReal (L ^ q)) kin probe t =
      (finiteClassLegalPressure q allowed α β (Real.toNNReal (L ^ q)) kin probe t / L ^ q) *
        ((m : ℝ) * L) ^ q := by
    rw [mul_pow]
    push_cast
    field_simp
  rw [gridRepairError, add_mul, ← hcoef]
  nlinarith [hbase]


/-- A genuine original real-scale pressure limit is bounded by each fixed box
and its actual uniform legal parent repair. -/
theorem finiteClassLegalScalePressure_limit_le_of_block_bound
    (q : ℕ) (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    (C G t K p : ℝ)
    (hp : Tendsto (fun R ↦ finiteClassLegalScalePressure q allowed α β kin probe R t)
      atTop (𝓝 p))
    (hblock : ∀ m : ℕ, 0 < m → ∀ L : ℝ, 0 < L →
      finiteClassLegalScalePressure q allowed α β kin probe ((m : ℝ) * L) t ≤
        finiteClassLegalScalePressure q allowed α β kin probe L t + gridRepairError q K C G t L)
    {L : ℝ} (hL : 0 < L) :
    p ≤ finiteClassLegalScalePressure q allowed α β kin probe L t + gridRepairError q K C G t L := by
  have hscale : Tendsto (fun m : ℕ ↦ (m : ℝ) * L) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hL
  apply le_of_tendsto (hp.comp hscale)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  exact hblock m (by omega) L hL

end OTSelector.Reconstruction
