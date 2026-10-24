import OTSelector.Probability.MarkedTileModel
import OTSelector.Probability.MarkedPressureLimitBlock
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Zero-intensity pressure and per-tile pressure limits

A finite family of tiles is encoded in one marked cloud whose label weights are
`w c`.  The contribution of tile `c` to the global pressure at scale `R` is the
pressure of the local model at intensity `R ^ q * w c`.  This module records the
two elementary facts needed to normalize those contributions by `R ^ q`:

* the marked pressure vanishes at intensity zero (the cloud is empty);
* for every weight `w c`, the normalized local contribution tends to
  `w c * p c t`, where `p c` is the local pressure limit.

The second statement is the composition of the local pressure limit with the
intensity rescaling `R ↦ R ^ q * w c`; the case `w c = 0` is handled separately
because the intensity stays at zero.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

noncomputable section
namespace OTSelector.Probability

/-- The Poisson law of rate zero is concentrated at zero. -/
theorem poissonMeasure_zero : poissonMeasure (0 : ℝ≥0) = Measure.dirac 0 := by
  ext s hs
  rw [poissonMeasure, Measure.sum_apply _ hs, tsum_eq_single 0]
  · simp
  · intro n hn
    have hz : (0 : ℝ) ^ n = 0 := zero_pow hn
    simp [hz]

/-- The marked tilted value vanishes when both clouds are empty. -/
theorem markedTilted_eq_zero_of_counts
    {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {r t : ℝ}
    (ω : TwoMarkedCloudSpace q A B) (hS : mSourceCount ω = 0)
    (hT : mTargetCount ω = 0) :
    markedTilted q r kin g t ω = 0 := by
  unfold markedTilted tiltedCloudValue
  rw [hS, hT]
  have hset : {v : ℝ | ∃ σ : PartialMatching 0 0, σ.card = min 0 0 ∧
      v = σ.cost (fun i : Fin 0 => fun j : Fin 0 =>
        mKineticCost q r kin ω (i : ℕ) (j : ℕ) + t * mProbe g ω (i : ℕ) (j : ℕ))} =
      {0} := by
    ext v
    constructor
    · rintro ⟨σ, -, rfl⟩
      have hedge : σ.edges = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e _
        exact Fin.elim0 e.1
      simp [PartialMatching.cost, hedge]
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨⟨∅, by simp, by simp⟩, by simp, by simp [PartialMatching.cost]⟩
  unfold PartialMatching.maxCardValue
  rw [hset, csInf_singleton]

/-- Almost surely, the source count of a marked cloud of intensity zero is zero. -/
theorem ae_mSourceCount_eq_zero_of_zero
    {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B)
    [IsProbabilityMeasure β] :
    ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β 0, mSourceCount ω = 0 := by
  have hsrc : ∀ᵐ z ∂markedPoissonLaw q A α (0 : ℝ≥0), z.1 = 0 := by
    unfold markedPoissonLaw
    rw [poissonMeasure_zero, Measure.dirac_prod]
    exact (ae_map_iff (f := Prod.mk (0 : ℕ))
      (measurable_const.prodMk measurable_id).aemeasurable
      (measurable_fst (measurableSet_singleton 0))).mpr
      (Eventually.of_forall fun _ => rfl)
  unfold twoMarkedCloudLaw
  have h := ae_of_ae_map
    (μ := (markedPoissonLaw q A α (0 : ℝ≥0)).prod (markedPoissonLaw q B β (0 : ℝ≥0)))
    measurable_fst.aemeasurable (p := fun z : MarkedCloudSpace q A => z.1 = 0) (by simpa using hsrc)
  simpa [mSourceCount] using h

/-- Almost surely, the target count of a marked cloud of intensity zero is zero. -/
theorem ae_mTargetCount_eq_zero_of_zero
    {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B)
    [IsProbabilityMeasure β] :
    ∀ᵐ ω ∂twoMarkedCloudLaw q A B α β 0, mTargetCount ω = 0 := by
  have htgt : ∀ᵐ z ∂markedPoissonLaw q B β (0 : ℝ≥0), z.1 = 0 := by
    unfold markedPoissonLaw
    rw [poissonMeasure_zero, Measure.dirac_prod]
    exact (ae_map_iff (f := Prod.mk (0 : ℕ))
      (measurable_const.prodMk measurable_id).aemeasurable
      (measurable_fst (measurableSet_singleton 0))).mpr
      (Eventually.of_forall fun _ => rfl)
  unfold twoMarkedCloudLaw
  have h := ae_of_ae_map
    (μ := (markedPoissonLaw q A α (0 : ℝ≥0)).prod (markedPoissonLaw q B β (0 : ℝ≥0)))
    measurable_snd.aemeasurable (p := fun z : MarkedCloudSpace q B => z.1 = 0) (by simpa using htgt)
  simpa [mTargetCount] using h

/-- The marked pressure vanishes at intensity zero. -/
theorem markedPressure_zero
    (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t : ℝ) :
    markedPressure q A B α β 0 kin g t = 0 := by
  unfold markedPressure
  rw [integral_eq_zero_of_ae]
  filter_upwards [ae_mSourceCount_eq_zero_of_zero (q := q) α β,
    ae_mTargetCount_eq_zero_of_zero (q := q) α β] with ω hS hT
  exact markedTilted_eq_zero_of_counts ω hS hT

/-- **Per-tile pressure limit.**  After normalization by the ambient intensity
`R ^ q`, the local pressure contribution of a tile of weight `w c` tends to
`w c` times the local pressure limit. -/
theorem tendsto_markedPressure_scaled_div
    (q : ℕ) (hq : 0 < q)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
      atTop (𝓝 (p t)))
    (c : ℝ≥0) (t : ℝ) :
    Tendsto (fun R : ℝ =>
      markedPressure q A B α β (Real.toNNReal (R ^ q * (c : ℝ))) kin g t / R ^ q)
      atTop (𝓝 ((c : ℝ) * p t)) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ (c : ℝ) from c.coe_nonneg) with hc | hc
  · have hc0 : (c : ℝ) = 0 := hc.symm
    have hfun : (fun R : ℝ =>
        markedPressure q A B α β (Real.toNNReal (R ^ q * (c : ℝ))) kin g t / R ^ q)
        =ᶠ[atTop] fun _ => (0 : ℝ) := by
      apply Eventually.of_forall
      intro R
      simp only [hc0, mul_zero, Real.toNNReal_zero, markedPressure_zero, zero_div]
    have hzero : (c : ℝ) * p t = 0 := by rw [hc0, zero_mul]
    rw [hzero]
    exact tendsto_const_nhds.congr' hfun.symm
  · have hcR : (0 : ℝ) < (c : ℝ) := hc
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hrpow : Tendsto (fun R : ℝ => R ^ q) atTop atTop := by
      simpa [Real.rpow_natCast] using tendsto_rpow_atTop hq0
    have hscale : Tendsto (fun R : ℝ => R ^ q * (c : ℝ)) atTop atTop :=
      hrpow.atTop_mul_const hcR
    have hbase := (tendsto_markedPressure_div q hq (kin := kin) (g := g)
      α β p hp t).comp hscale
    have hmul : Tendsto (fun R : ℝ => (c : ℝ) *
        (markedPressure q A B α β (Real.toNNReal (R ^ q * (c : ℝ))) kin g t /
          (R ^ q * (c : ℝ)))) atTop (𝓝 ((c : ℝ) * p t)) :=
      hbase.const_mul (c : ℝ)
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hcne : (c : ℝ) ≠ 0 := hcR.ne'
    have hRne : R ≠ 0 := hR.ne'
    have hRq : R ^ q ≠ 0 := pow_ne_zero _ hRne
    field_simp


/-- **Per-tile pressure limit, NNReal-intensity form.**  The local intensity is
written as `Real.toNNReal (R ^ q) * w c`, matching the output of the finite-tile
pressure bound. -/
theorem tendsto_markedPressure_scaled_div' {q : ℕ} (hq : 0 < q)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
      atTop (𝓝 (p t)))
    (c : ℝ≥0) (t : ℝ) :
    Tendsto (fun R : ℝ =>
      markedPressure q A B α β (Real.toNNReal (R ^ q) * c) kin g t / R ^ q)
      atTop (𝓝 ((c : ℝ) * p t)) := by
  refine (tendsto_markedPressure_scaled_div q hq α β p hp c t).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hRq : (0 : ℝ) ≤ R ^ q := pow_nonneg hR.le q
  have h : Real.toNNReal (R ^ q * (c : ℝ)) = Real.toNNReal (R ^ q) * c := by
    rw [Real.toNNReal_mul hRq, Real.toNNReal_coe]
  rw [h]


end OTSelector.Probability
