import OTSelector.Reconstruction.OriginalReserveFullUnitInputReserveDeviationLimit
import OTSelector.Reconstruction.OriginalReservePositiveBlockCapacityUnion

/-! Simultaneous concentration of the true half-open original reserve prefixes on the actual finite clock grid. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

/-- A true source-Ico or target-Ioc original reserve prefix deviates from its
actual theta-volume mean. Every grid cut is included, including zero Hall cuts. -/
def originalReserveClockGridPrefixDeviationFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (θ R : ℝ)
    (G : OriginalStageClockGrid) (r : ℝ) :
    Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
  {p | ∃ k : Fin (G.count + 1),
    r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
      |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2)
          (Ico (G.cut 0) (G.cut k)) : ℝ) -
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          α.real (Ico (G.cut 0) (G.cut k))| ∨
    r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
      |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2)
          (Ioc (G.cut 0) (G.cut k)) : ℝ) -
        θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) *
          β.real (Ioc (G.cut 0) (G.cut k))|}

/-- The actual finite-grid reserve fluctuation event is Borel and reads only
original counts and marks, before conditioning on own spatial coordinates. -/
theorem measurableSet_originalReserveClockGridPrefixDeviationFailure {q : ℕ} (α β : Measure ℝ)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (θ R : ℝ)
    (G : OriginalStageClockGrid) (r : ℝ) :
    MeasurableSet (originalReserveClockGridPrefixDeviationFailure α β b θ R G r) := by
  have h (k : Fin (G.count+1)) : MeasurableSet
      {p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ |
        r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) (Ico (G.cut 0) (G.cut k)) : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real (Ico (G.cut 0) (G.cut k))| ∨
        r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
          |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) (Ioc (G.cut 0) (G.cut k)) : ℝ) -
            θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real (Ioc (G.cut 0) (G.cut k))|} := by
    apply MeasurableSet.union
    · exact measurableSet_lt measurable_const
        (((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
          (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ico)).sub measurable_const).abs
    · exact measurableSet_lt measurable_const
        (((measurable_from_nat : Measurable (Nat.cast : ℕ → ℝ)).comp
          (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) measurableSet_Ioc)).sub measurable_const).abs
  simpa only [originalReserveClockGridPrefixDeviationFailure, Set.ofPred_exists] using MeasurableSet.iUnion h

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}

/-- All actual finite-grid source-Ico/target-Ioc reserve prefixes simultaneously
have sublinear deviations outside a quadratically negligible event on the same
full joining. No count balance at zero Hall cuts or spatial iid callback is used. -/
theorem tendsto_clockGridPrefixDeviationFailure_probability (hq : 4 < q)
    (X : ∀ R : ℝ, 0 < R → OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)
    (G : OriginalStageClockGrid) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦ if hR : 0 < R then
      R^2 * ((X R hR).fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
        (originalReserveClockGridPrefixDeviationFailure α β b θ R G r) else 0) atTop (𝓝 0) := by
  let I := Fin (G.count+1)
  let P : ℝ → Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
    fun R ↦ if hR : 0 < R then ((X R hR).fullLaw : Measure _) else 0
  let bad : I ⊕ I → ℝ → Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) :=
    fun i R ↦ i.elim
      (fun k : I ↦ {p | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
        |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) (Ico (G.cut 0) (G.cut k)) : ℝ) -
          θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * α.real (Ico (G.cut 0) (G.cut k))|})
      (fun k : I ↦ {p | r * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) <
        |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) (Ioc (G.cut 0) (G.cut k)) : ℝ) -
          θ * volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) * β.real (Ioc (G.cut 0) (G.cut k))|})
  have hi (i : I ⊕ I) : Tendsto (fun R ↦ R^2 * (P R).real (bad i R)) atTop (𝓝 0) := by
    cases i with
    | inl k =>
      have hh := tendsto_sourceReserveBlockCount_deviation_probability hq X
        (C := Ico (G.cut 0) (G.cut k)) measurableSet_Ico hr
      convert hh using 1
      funext R
      by_cases hR : 0 < R
      · simp only [P, bad, Sum.elim_inl, dite_eq_left hR]
      · simp [P, hR]
    | inr k =>
      have hh := tendsto_targetReserveBlockCount_deviation_probability hq X
        (C := Ioc (G.cut 0) (G.cut k)) measurableSet_Ioc hr
      convert hh using 1
      funext R
      by_cases hR : 0 < R
      · simp only [P, bad, Sum.elim_inr, dite_eq_left hR]
      · simp [P, hR]
  have hu := tendsto_quadratic_finite_union_measureReal_zero P bad hi
  convert hu using 1
  funext R
  by_cases hR : 0 < R
  · simp only [P, dite_eq_left hR]
    apply congrArg (fun A : Set (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ) ↦
      R^2 * ((X R hR).fullLaw : Measure _).real A)
    ext p
    constructor
    · rintro ⟨k, hs | ht⟩
      · exact ⟨Sum.inl k, hs⟩
      · exact ⟨Sum.inr k, ht⟩
    · rintro ⟨i, hp⟩
      cases i with
      | inl k => exact ⟨k, Or.inl hp⟩
      | inr k => exact ⟨k, Or.inr hp⟩
  · simp [P, hR]

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
