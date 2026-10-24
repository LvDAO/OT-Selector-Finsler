import OTSelector.MeasureTheory.IntegrableMarginalRestriction
import OTSelector.Reconstruction.OriginalLegalWeightedBoundaryRecovery
import OTSelector.Reconstruction.OriginalLegalWeightedWindowCoreRecovery
import OTSelector.Reconstruction.OriginalLegalWeightedClockGapExhaustion

/-! Original clock carriers recover actual weighted Palm mass and signed cost.
The discarded mass is controlled in the original clock law, without I2. -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- Any original source-clock sets of vanishing mass have vanishing actual
weighted Palm loss, including both density and absolute signed energy. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_sourceClock_removedWeight_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (S : ℕ → Set ℝ) (hS : ∀ n, MeasurableSet (S n))
    (hsmall : Tendsto (fun n ↦ α (S n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ m in (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹' S n,
      legalWeightedGridRecoveryWeight kin g t m ∂legalMarkedJointPalm q M.law)
      atTop (𝓝 0) :=
  tendsto_setIntegral_preimage_zero_of_marginal_mass_zero
    (legalMarkedJointPalm q M.law) α _ measurable_fst.fst M.source_clock _
    (M.integrable_gridRecoveryWeight t) S hS atTop hsmall

/-- The same original target-clock identity pays its actual weighted losses. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_targetClock_removedWeight_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (S : ℕ → Set ℝ) (hS : ∀ n, MeasurableSet (S n))
    (hsmall : Tendsto (fun n ↦ β (S n)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ m in (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2) ⁻¹' S n,
      legalWeightedGridRecoveryWeight kin g t m ∂legalMarkedJointPalm q M.law)
      atTop (𝓝 0) :=
  tendsto_setIntegral_preimage_zero_of_marginal_mass_zero
    (legalMarkedJointPalm q M.law) β _ measurable_fst.snd M.target_clock _
    (M.integrable_gridRecoveryWeight t) S hS atTop hsmall

/-- The actual signed value on source-clock carriers converges to the original
value when only their original source marginal complements tend to zero. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_sourceClock_retainedValue
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (K : ℕ → Set ℝ) (hK : ∀ n, MeasurableSet (K n))
    (hsmall : Tendsto (fun n ↦ α (K n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ m in (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹' K n,
      (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) ∂legalMarkedJointPalm q M.law)
      atTop (𝓝 (M.value t)) := by
  let cost : PhysicalPairPalmMark (Fin q) → ℝ :=
    fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
  have hi : Integrable cost (legalMarkedJointPalm q M.law) :=
    M.kinetic_integrable.add (M.probe_integrable.const_mul t)
  have hzero := tendsto_setIntegral_preimage_zero_of_marginal_mass_zero
    (legalMarkedJointPalm q M.law) α _ measurable_fst.fst M.source_clock cost hi
    (fun n ↦ (K n)ᶜ) (fun n ↦ (hK n).compl) atTop hsmall
  have heq (n : ℕ) :
      (∫ m in (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹' K n,
        cost m ∂legalMarkedJointPalm q M.law) = M.value t -
      ∫ m in (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹' (K n)ᶜ,
        cost m ∂legalMarkedJointPalm q M.law := by
    have hsplit := integral_add_compl ((hK n).preimage measurable_fst.fst) hi
    have hvalue : (∫ m, cost m ∂legalMarkedJointPalm q M.law) = M.value t := by
      dsimp only [cost]
      rw [integral_add M.kinetic_integrable (M.probe_integrable.const_mul t),
        integral_const_mul]
      rfl
    rw [hvalue] at hsplit
    simpa only [preimage_compl] using (eq_sub_iff_add_eq.mpr hsplit)
  have ht := (tendsto_const_nhds (x := M.value t)).sub hzero
  simp only [sub_zero] at ht
  change Tendsto (fun n ↦ ∫ m in
    (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹' K n,
      cost m ∂legalMarkedJointPalm q M.law) atTop (𝓝 (M.value t))
  simpa only [heq] using ht

/-- The actual normalized source-cube loss is the same Palm loss at every
positive radius, even when the radii and clock sets vary without nesting. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_normalizedSourceWindow_clockLoss_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (w : PhysicalPairPalmMark (Fin q) → ℝ) (hw : Measurable w)
    (hi : Integrable w (legalMarkedJointPalm q M.law))
    (S : ℕ → Set ℝ) (hS : ∀ n, MeasurableSet (S n))
    (hsmall : Tendsto (fun n ↦ α (S n)) atTop (𝓝 0))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) :
    Tendsto (fun n ↦ ∫ e,
      ((fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹' S n).indicator w
        (physicalPairAnchor e).2 ∂legalWeightedNormalizedSourceWindowPlan M (R n))
      atTop (𝓝 0) := by
  have ht := tendsto_setIntegral_preimage_zero_of_marginal_mass_zero
    (legalMarkedJointPalm q M.law) α _ measurable_fst.fst M.source_clock w hi
    S hS atTop hsmall
  have heq (n : ℕ) := integral_normalizedSourceWindowPlan_palm_readout M (hR n)
    (((fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹' S n).indicator w)
    (hw.indicator ((hS n).preimage measurable_fst.fst))
  simp only [integral_indicator ((hS _).preimage measurable_fst.fst)] at heq
  simpa only [heq] using ht

/-- The reserve's actual positive-gap carriers recover the retained candidate's
full original value and weighted mass. Candidate and reserve may use different
kinetic kernels while retaining exactly the same original clock laws. -/
theorem LegalWeightedStationaryPoissonMatching.exists_clockGapCarriers_weighted_recovery
    [NullSingletonClass α] [NullSingletonClass β]
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {kinN : ℝ → ℝ → (Fin q → ℝ) → ℝ} {gN : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kinN gN) (t : ℝ) :
    ∃ (η : ℕ → ℝ) (D : ℕ → Set ℝ),
      (∀ n, 0 < η n) ∧ (∀ n, IsCompact (D n)) ∧
      (∀ n, IsCompact (legalOriginalClockGapCarrier α β (D n) (η n))) ∧
      Tendsto (fun n ↦ α (legalOriginalClockGapCarrier α β (D n) (η n))ᶜ)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ m in (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹'
        (legalOriginalClockGapCarrier α β (D n) (η n))ᶜ,
        legalWeightedGridRecoveryWeight kin g t m ∂legalMarkedJointPalm q M.law)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ m in (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) ⁻¹'
        legalOriginalClockGapCarrier α β (D n) (η n),
        (kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2) ∂legalMarkedJointPalm q M.law)
        atTop (𝓝 (M.value t)) := by
  obtain ⟨η,D,hη,hD,hK,_hsmall,ht⟩ := N.exists_originalClockGapCarriers_exhaust_source
  refine ⟨η,D,hη,hD,hK,ht,?_,?_⟩
  · exact M.tendsto_sourceClock_removedWeight_zero t _
      (fun n ↦ (hK n).measurableSet.compl) ht
  · exact M.tendsto_sourceClock_retainedValue t _ (fun n ↦ (hK n).measurableSet) ht

end OTSelector.Reconstruction
