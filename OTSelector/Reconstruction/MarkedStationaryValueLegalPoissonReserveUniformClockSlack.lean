import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveUniformTails

/-!
# Uniform strict reserve slack on the unchanged original two-color Poisson input

The deviation statement has no population ordering assumption.  When a compact
set of relevant thresholds has a positive population slack, it supplies the
corresponding actual strict-tail reserve capacity uniformly in that threshold.
-/
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Failure of a one-color event on the original two-color input reads only that
original color.  Product outer probabilities agree even for an arbitrary event. -/
theorem twoMarkedCloudLaw_real_fst_preimage
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) (S : Set (MarkedCloudSpace q ℝ)) :
    (twoMarkedCloudLaw q ℝ ℝ α β r).real (Prod.fst ⁻¹' S) =
      (markedPoissonLaw q ℝ α r).real S := by
  rw [show Prod.fst ⁻¹' S = S ×ˢ (univ : Set (MarkedCloudSpace q ℝ)) by ext; simp]
  unfold twoMarkedCloudLaw
  rw [measureReal_prod_prod, probReal_univ, mul_one]

theorem twoMarkedCloudLaw_real_snd_preimage
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) (S : Set (MarkedCloudSpace q ℝ)) :
    (twoMarkedCloudLaw q ℝ ℝ α β r).real (Prod.snd ⁻¹' S) =
      (markedPoissonLaw q ℝ β r).real S := by
  rw [show Prod.snd ⁻¹' S = (univ : Set (MarkedCloudSpace q ℝ)) ×ˢ S by ext; simp]
  unfold twoMarkedCloudLaw
  rw [measureReal_prod_prod, probReal_univ, one_mul]

/-- A fixed deterministic clock mesh yields a rate for both original colors
simultaneously, independent of their later Poisson volume. -/
theorem exists_originalReserveUniformTailBad_sqrtRate
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    [NullSingletonClass α] [NullSingletonClass β]
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0, 0 < r →
      (twoMarkedCloudLaw q ℝ ℝ α β r).real
        ((Prod.fst ⁻¹' originalReserveUniformPrefixBad q α r Ici K ε) ∪
          (Prod.snd ⁻¹' originalReserveUniformPrefixBad q β r Ioi K ε)) ≤
            C / Real.sqrt (r : ℝ) := by
  obtain ⟨Ca, hCa, ha⟩ := (exists_originalReserveUniformTails_sqrtRate q α K hK hε).2
  obtain ⟨Cb, hCb, hb⟩ := (exists_originalReserveUniformTails_sqrtRate q β K hK hε).1
  refine ⟨Ca + Cb, add_nonneg hCa hCb, ?_⟩
  intro r hr
  have hu := measureReal_union_le (μ := twoMarkedCloudLaw q ℝ ℝ α β r)
    (Prod.fst ⁻¹' originalReserveUniformPrefixBad q α r Ici K ε)
    (Prod.snd ⁻¹' originalReserveUniformPrefixBad q β r Ioi K ε)
  rw [twoMarkedCloudLaw_real_fst_preimage, twoMarkedCloudLaw_real_snd_preimage] at hu
  exact hu.trans ((add_le_add (ha r hr) (hb r hr)).trans_eq (add_div _ _ _).symm)

/-- Actual source-closed and target-strict tail deviations vanish uniformly
on every compact threshold carrier in the original two-color experiment. -/
theorem tendsto_originalReserveUniformTailBad_zero
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    [NullSingletonClass α] [NullSingletonClass β]
    (K : Set ℝ) (hK : IsCompact K) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (twoMarkedCloudLaw q ℝ ℝ α β (r n)).real
      ((Prod.fst ⁻¹' originalReserveUniformPrefixBad q α (r n) Ici K ε) ∪
        (Prod.snd ⁻¹' originalReserveUniformPrefixBad q β (r n) Ioi K ε)))
      atTop (𝓝 0) := by
  have hα := tendsto_originalReserveIci_bad_zero q α K hK r hr hrtop hε
  have hβ := tendsto_originalReserveIoi_bad_zero q β K hK r hr hrtop hε
  have hb := hα.add hβ
  simp only [add_zero] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ ↦ ENNReal.toReal_nonneg)
  intro n
  have hu := measureReal_union_le (μ := twoMarkedCloudLaw q ℝ ℝ α β (r n))
    (Prod.fst ⁻¹' originalReserveUniformPrefixBad q α (r n) Ici K ε)
    (Prod.snd ⁻¹' originalReserveUniformPrefixBad q β (r n) Ioi K ε)
  rw [twoMarkedCloudLaw_real_fst_preimage, twoMarkedCloudLaw_real_snd_preimage] at hu
  exact hu

/-- The strict reserve inequality is stated at every actual threshold, including
thresholds selected from the observed original source clocks. -/
def originalReserveUniformClockSlackEvent
    (q : ℕ) (r : ℝ≥0) (η : ℝ) (K : Set ℝ) : Set (TwoMarkedCloudSpace q ℝ ℝ) :=
  {ω | ∀ c ∈ K, (r : ℝ) * η / 2 ≤
    (originalReserveClockCount q (Ioi c) ω.2 : ℝ) -
      (originalReserveClockCount q (Ici c) ω.1 : ℝ)}

/-- Positive original population slack turns failures into actual uniform
source or target count deviations, without a law for adaptive endpoints. -/
theorem originalReserveUniformClockSlack_compl_subset
    (q : ℕ) (α β : Measure ℝ) (r : ℝ≥0) (η : ℝ) (K : Set ℝ)
    (hslack : ∀ c ∈ K, α.real (Ici c) + η ≤ β.real (Ioi c)) :
    (originalReserveUniformClockSlackEvent q r η K)ᶜ ⊆
      (Prod.fst ⁻¹' originalReserveUniformPrefixBad q α r Ici K (η / 4)) ∪
        (Prod.snd ⁻¹' originalReserveUniformPrefixBad q β r Ioi K (η / 4)) := by
  intro ω hω
  obtain ⟨c, hc⟩ := not_forall.mp hω
  obtain ⟨hc, hfail⟩ := not_imp.mp hc
  have hf : (originalReserveClockCount q (Ioi c) ω.2 : ℝ) -
      (originalReserveClockCount q (Ici c) ω.1 : ℝ) < (r : ℝ) * η / 2 :=
    lt_of_not_ge hfail
  by_cases hα : (r : ℝ) * (η / 4) <
      |(originalReserveClockCount q (Ici c) ω.1 : ℝ) - (r : ℝ) * α.real (Ici c)|
  · exact Or.inl ⟨c, hc, hα⟩
  · right
    refine ⟨c, hc, ?_⟩
    have hm := mul_le_mul_of_nonneg_left (hslack c hc) r.coe_nonneg
    have hs := le_abs_self ((originalReserveClockCount q (Ici c) ω.1 : ℝ) -
      (r : ℝ) * α.real (Ici c))
    have ht := neg_le_abs ((originalReserveClockCount q (Ioi c) ω.2 : ℝ) -
      (r : ℝ) * β.real (Ioi c))
    push Not at hα
    change (r : ℝ) * (η / 4) <
      |(originalReserveClockCount q (Ioi c) ω.2 : ℝ) - (r : ℝ) * β.real (Ioi c)|
    nlinarith

/-- Uniform strict reserve slack has the same square-root failure rate. -/
theorem exists_originalReserveUniformClockSlack_failure_sqrtRate
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    [NullSingletonClass α] [NullSingletonClass β]
    (K : Set ℝ) (hK : IsCompact K) {η : ℝ} (hη : 0 < η)
    (hslack : ∀ c ∈ K, α.real (Ici c) + η ≤ β.real (Ioi c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ≥0, 0 < r →
      (twoMarkedCloudLaw q ℝ ℝ α β r).real
        (originalReserveUniformClockSlackEvent q r η K)ᶜ ≤ C / Real.sqrt (r : ℝ) := by
  have hquarter : 0 < η / 4 := by positivity
  obtain ⟨C, hC, hB⟩ := exists_originalReserveUniformTailBad_sqrtRate q α β K hK hquarter
  refine ⟨C, hC, fun r hr ↦ ?_⟩
  exact (measureReal_mono
    (originalReserveUniformClockSlack_compl_subset q α β r η K hslack)).trans (hB r hr)

/-- Uniform strict-tail reserve capacity holds outside an event of vanishing
outer probability whenever its original population slack is positive. -/
theorem tendsto_originalReserveUniformClockSlack_failure_zero
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    [NullSingletonClass α] [NullSingletonClass β]
    (K : Set ℝ) (hK : IsCompact K) (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop) {η : ℝ} (hη : 0 < η)
    (hslack : ∀ c ∈ K, α.real (Ici c) + η ≤ β.real (Ioi c)) :
    Tendsto (fun n ↦ (twoMarkedCloudLaw q ℝ ℝ α β (r n)).real
      (originalReserveUniformClockSlackEvent q (r n) η K)ᶜ) atTop (𝓝 0) := by
  have hquarter : 0 < η / 4 := by positivity
  have hb := tendsto_originalReserveUniformTailBad_zero q α β K hK r hr hrtop hquarter
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ ↦ ENNReal.toReal_nonneg)
    (fun n ↦ measureReal_mono
      (originalReserveUniformClockSlack_compl_subset q α β (r n) η K hslack))

end OTSelector.Reconstruction
