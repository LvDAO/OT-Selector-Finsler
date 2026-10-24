import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveUniformPrefixes

/-! Strict and closed original reserve tails retain their literal finite-sample counts. -/
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Complementary actual prefix counts partition the original used indices. -/
theorem originalReserveClockCount_add_compl (q : ℕ) (U : Set ℝ)
    (z : MarkedCloudSpace q ℝ) :
    originalReserveClockCount q U z + originalReserveClockCount q Uᶜ z = z.1 := by
  simpa only [originalReserveClockCount, mem_compl_iff, Finset.card_univ,
    Fintype.card_fin] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin z.1 ↦ (z.2 i).2 ∈ U))

/-- Complement error is bounded by the original total-count and prefix errors. -/
theorem originalReserveClockCount_compl_error_le
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] (r : ℝ≥0)
    {U : Set ℝ} (hU : MeasurableSet U) (z : MarkedCloudSpace q ℝ) :
    |(originalReserveClockCount q Uᶜ z : ℝ) - (r : ℝ) * α.real Uᶜ| ≤
      |(z.1 : ℝ) - (r : ℝ)| +
        |(originalReserveClockCount q U z : ℝ) - (r : ℝ) * α.real U| := by
  have hc := congrArg (fun n : ℕ ↦ (n : ℝ)) (originalReserveClockCount_add_compl q U z)
  simp only [Nat.cast_add] at hc
  rw [probReal_compl_eq_one_sub hU]
  have heq : (originalReserveClockCount q Uᶜ z : ℝ) - (r : ℝ) * (1 - α.real U) =
      ((z.1 : ℝ) - (r : ℝ)) -
        ((originalReserveClockCount q U z : ℝ) - (r : ℝ) * α.real U) := by linarith
  rw [heq]
  exact abs_sub _ _

/-- A continuum complement bad event reduces to an actual total-count error
and the corresponding actual prefix bad event. -/
theorem originalReserveUniformComplementBad_subset
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] (r : ℝ≥0)
    (U : ℝ → Set ℝ) (hU : ∀ c, MeasurableSet (U c)) (K : Set ℝ) (ε : ℝ) :
    originalReserveUniformPrefixBad q α r (fun c ↦ (U c)ᶜ) K ε ⊆
      {z | (r : ℝ) * (ε / 2) ≤ originalReserveFiniteDeviation q α r
        (fun _ : Unit ↦ univ) z} ∪
      originalReserveUniformPrefixBad q α r U K (ε / 2) := by
  intro z hz
  obtain ⟨c, hc, hbad⟩ := hz
  by_cases hp : (r : ℝ) * (ε / 2) <
      |(originalReserveClockCount q (U c) z : ℝ) - (r : ℝ) * α.real (U c)|
  · exact Or.inr ⟨c, hc, hp⟩
  · left
    have hb := originalReserveClockCount_compl_error_le q α r (hU c) z
    change (r : ℝ) * ε <
      |(originalReserveClockCount q (U c)ᶜ z : ℝ) - (r : ℝ) * α.real (U c)ᶜ| at hbad
    have ht : (r : ℝ) * (ε / 2) ≤ |(z.1 : ℝ) - (r : ℝ)| := by linarith
    simpa [originalReserveFiniteDeviation, originalReserveClockCount] using ht

/-- The total-count identity preserves the square-root probability rate when
passing from prefixes to complementary strict or closed tails. -/
theorem exists_originalReserveUniformComplementBad_sqrtRate
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (U : ℝ → Set ℝ) (hU : ∀ c, MeasurableSet (U c)) (K : Set ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hprefix : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0, 0 < r →
      (markedPoissonLaw q ℝ α r).real
        (originalReserveUniformPrefixBad q α r U K (ε / 2)) ≤ C / Real.sqrt (r : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0, 0 < r →
      (markedPoissonLaw q ℝ α r).real
        (originalReserveUniformPrefixBad q α r (fun c ↦ (U c)ᶜ) K ε) ≤
          C / Real.sqrt (r : ℝ) := by
  obtain ⟨C, hC, hprefix⟩ := hprefix
  refine ⟨1 / (ε / 2) + C, by positivity, ?_⟩
  intro r hr
  have ht := originalReserveFiniteDeviation_failure_bound q α r hr (half_pos hε)
    (fun _ : Unit ↦ (univ : Set ℝ)) (fun _ ↦ MeasurableSet.univ)
  simp only [Fintype.card_unique, Nat.cast_one] at ht
  calc
    _ ≤ (markedPoissonLaw q ℝ α r).real
        ({z | (r : ℝ) * (ε / 2) ≤ originalReserveFiniteDeviation q α r
          (fun _ : Unit ↦ univ) z} ∪ originalReserveUniformPrefixBad q α r U K (ε / 2)) :=
      measureReal_mono (originalReserveUniformComplementBad_subset q α r U hU K ε)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 1 / ((ε / 2) * Real.sqrt (r : ℝ)) + C / Real.sqrt (r : ℝ) :=
      add_le_add ht (hprefix r hr)
    _ = _ := by rw [add_div, div_div]

/-- Both kinds of actual tail have uniform square-root deviation bounds, with
constants chosen before the original Poisson volume. -/
theorem exists_originalReserveUniformTails_sqrtRate
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] [NullSingletonClass α]
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0, 0 < r →
      (markedPoissonLaw q ℝ α r).real
        (originalReserveUniformPrefixBad q α r Ioi K ε) ≤ C / Real.sqrt (r : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0, 0 < r →
      (markedPoissonLaw q ℝ α r).real
        (originalReserveUniformPrefixBad q α r Ici K ε) ≤ C / Real.sqrt (r : ℝ)) := by
  constructor
  · simpa only [compl_Iic] using exists_originalReserveUniformComplementBad_sqrtRate
      q α Iic (fun _ ↦ measurableSet_Iic) K hε
      (exists_originalReserveUniformPrefixBad_sqrtRate q α Iic (fun _ ↦ measurableSet_Iic)
        (fun _ _ h ↦ Iic_subset_Iic.mpr h) (fun _ ↦ rfl) K hK (half_pos hε))
  · have hmass (c : ℝ) : α.real (Iio c) = α.real (Iic c) :=
      congrArg ENNReal.toReal (measure_congr (Iio_ae_eq_Iic (μ := α) (a := c)))
    simpa only [compl_Iio] using exists_originalReserveUniformComplementBad_sqrtRate
      q α Iio (fun _ ↦ measurableSet_Iio) K hε
      (exists_originalReserveUniformPrefixBad_sqrtRate q α Iio (fun _ ↦ measurableSet_Iio)
        (fun _ _ h ↦ Iio_subset_Iio h) hmass K hK (half_pos hε))

/-- Uniform prefix concentration implies uniform complementary-tail concentration,
without discarding points equal to a selected threshold. -/
theorem tendsto_originalReserveUniformComplementBad_zero
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (U : ℝ → Set ℝ) (hU : ∀ c, MeasurableSet (U c)) (K : Set ℝ)
    (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {ε : ℝ} (hε : 0 < ε)
    (hprefix : Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      (originalReserveUniformPrefixBad q α (r n) U K (ε / 2))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      (originalReserveUniformPrefixBad q α (r n) (fun c ↦ (U c)ᶜ) K ε))
      atTop (𝓝 0) := by
  have htotal := tendsto_originalReserveFiniteDeviation_failure_zero q α r hr hrtop
    (half_pos hε) (fun _ : Unit ↦ (univ : Set ℝ)) (fun _ ↦ MeasurableSet.univ)
  have hsum := htotal.add hprefix
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ ENNReal.toReal_nonneg)
  intro n
  exact (measureReal_mono (originalReserveUniformComplementBad_subset q α (r n)
    U hU K ε)).trans (measureReal_union_le _ _)

/-- Uniform concentration for literal strict tail counts of the original reserve. -/
theorem tendsto_originalReserveIoi_bad_zero
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] [NullSingletonClass α]
    (K : Set ℝ) (hK : IsCompact K) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      (originalReserveUniformPrefixBad q α (r n) Ioi K ε)) atTop (𝓝 0) := by
  simpa only [compl_Iic] using tendsto_originalReserveUniformComplementBad_zero q α Iic
    (fun _ ↦ measurableSet_Iic) K r hr hrtop hε
    (tendsto_originalReserveIic_bad_zero q α K hK r hr hrtop (half_pos hε))

/-- Uniform concentration for literal closed tail counts of the original reserve. -/
theorem tendsto_originalReserveIci_bad_zero
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] [NullSingletonClass α]
    (K : Set ℝ) (hK : IsCompact K) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      (originalReserveUniformPrefixBad q α (r n) Ici K ε)) atTop (𝓝 0) := by
  simpa only [compl_Iio] using tendsto_originalReserveUniformComplementBad_zero q α Iio
    (fun _ ↦ measurableSet_Iio) K r hr hrtop hε
    (tendsto_originalReserveIio_bad_zero q α K hK r hr hrtop (half_pos hε))

end OTSelector.Reconstruction
