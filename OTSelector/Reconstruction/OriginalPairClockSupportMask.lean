import OTSelector.Reconstruction.MarkedStationaryValueLegalFullPathNonnegativeCampbell

/-! The original two clock-support indicator is deterministic and Borel.
It equals one on the same true Palm by the original clock marginals, so it
can enforce literal node eligibility without changing any original traffic. -/
open Set Function MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The actual source and target clocks belong to their unchanged original supports. -/
def originalPairClockSupportMask (q : ℕ) (α β : Measure ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) : ℝ≥0∞ :=
  {z | z.1.1.1 ∈ α.support ∧ z.1.1.2 ∈ β.support}.indicator 1 z

theorem measurable_originalPairClockSupportMask (q : ℕ) (α β : Measure ℝ) :
    Measurable (originalPairClockSupportMask q α β) :=
  measurable_const.indicator
    ((α.isClosed_support.measurableSet.preimage measurable_fst.fst.fst).inter
      (β.isClosed_support.measurableSet.preimage measurable_fst.fst.snd))

theorem originalPairClockSupportMask_le_one (q : ℕ) (α β : Measure ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) : originalPairClockSupportMask q α β z ≤ 1 := by
  classical
  by_cases hz : z.1.1.1 ∈ α.support ∧ z.1.1.2 ∈ β.support <;>
    simp [originalPairClockSupportMask, hz]

theorem originalPairClockSupportMask_ne_zero_iff (q : ℕ) (α β : Measure ℝ)
    (z : PhysicalPairPalmMark (Fin q) × ℝ) :
    originalPairClockSupportMask q α β z ≠ 0 ↔ z.1.1.1 ∈ α.support ∧ z.1.1.2 ∈ β.support := by
  classical
  by_cases hz : z.1.1.1 ∈ α.support ∧ z.1.1.2 ∈ β.support <;>
    simp [originalPairClockSupportMask, hz]

/-- Original source/target clock marginals internally make the deterministic
support filter equal one for true-Palm almost every original pair, at every clock. -/
theorem LegalWeightedStationaryPoissonMatching.ae_originalPairClockSupportMask_eq_one
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ m ∂legalMarkedJointPalm q Q.law, ∀ c : ℝ, originalPairClockSupportMask q α β (m, c) = 1 := by
  have ha : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.1 ∈ α.support :=
    ae_of_ae_map measurable_fst.fst.aemeasurable (by rw [Q.source_clock]; exact α.support_mem_ae)
  have hb : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1.2 ∈ β.support :=
    ae_of_ae_map measurable_fst.snd.aemeasurable (by rw [Q.target_clock]; exact β.support_mem_ae)
  filter_upwards [ha, hb] with m ham hbm c
  have hm : (m, c) ∈ {z : PhysicalPairPalmMark (Fin q) × ℝ |
      z.1.1.1 ∈ α.support ∧ z.1.1.2 ∈ β.support} := ⟨ham, hbm⟩
  exact indicator_of_mem hm _

end OTSelector.Reconstruction
