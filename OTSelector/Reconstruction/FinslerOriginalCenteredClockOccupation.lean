import OTSelector.Reconstruction.FinslerOriginalMomentumBorelCentering
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalFocalPathMoment

/-!
# Original minimizing laws have centered clock occupation traffic

At each deterministic original clock, the half-open crossing set is exactly
the difference of the closed source and target prefixes on forward pairs.
Actual Borel-clock first variation centers both prefixes. The true original
momentum and its actual compliance velocity are therefore integrable and
centered on that same crossing event, without a displacement second moment.
-/
open Set Function MeasureTheory Manifold Matrix Module
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- Original forward edges occupying clock c, with an exact half-open
endpoint convention that allows atoms in either original clock marginal. -/
def originalClockCrossingSet (q : ℕ) (c : ℝ) : Set (PhysicalPairPalmMark (Fin q)) :=
  {m | m.1.1 ≤ c ∧ c < m.1.2}

theorem measurableSet_originalClockCrossingSet (q : ℕ) (c : ℝ) :
    MeasurableSet (originalClockCrossingSet q c) :=
  (measurableSet_le measurable_fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst.snd)

/-- The actual crossing integral equals the difference of the two original
closed prefix integrals. Forward order is used only on the same Palm. -/
theorem setIntegral_originalClockCrossing_eq_prefix_sub
    {q : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (η : Measure (PhysicalPairPalmMark (Fin q)))
    {p : PhysicalPairPalmMark (Fin q) → V} (hp : Integrable p η)
    (hforward : ∀ᵐ m ∂η, m.1.1 < m.1.2) (c : ℝ) :
    (∫ m in originalClockCrossingSet q c, p m ∂η) =
      (∫ m in {m | m.1.1 ≤ c}, p m ∂η) -
        ∫ m in {m | m.1.2 ≤ c}, p m ∂η := by
  have hS : MeasurableSet {m : PhysicalPairPalmMark (Fin q) | m.1.1 ≤ c} :=
    measurableSet_le measurable_fst.fst measurable_const
  have hT : MeasurableSet {m : PhysicalPairPalmMark (Fin q) | m.1.2 ≤ c} :=
    measurableSet_le measurable_fst.snd measurable_const
  rw [← integral_indicator (measurableSet_originalClockCrossingSet q c),
    ← integral_indicator hS, ← integral_indicator hT,
    ← integral_sub (hp.indicator hS) (hp.indicator hT)]
  apply integral_congr_ae
  filter_upwards [hforward] with m hm
  by_cases ha : m.1.1 ≤ c
  · by_cases hb : m.1.2 ≤ c
    · simp [originalClockCrossingSet, ha, hb, not_lt.mpr hb]
    · simp [originalClockCrossingSet, ha, hb, lt_of_not_ge hb]
  · have hb : ¬ m.1.2 ≤ c := by linarith
    simp [originalClockCrossingSet, ha, hb]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The unchanged original momentum carried by actual edges crossing c. -/
def originalSeedCrossingMomentum (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (c : ℝ) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  (originalClockCrossingSet (finrank ℝ S.covector.ker) c).indicator
    (originalSeedPairMomentum S w) m

/-- Actual compliance path velocity occupying the original physical clock c.
The original kernel is evaluated at its unchanged relative clock c−level. -/
def originalSeedClockOccupation (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (c : ℝ) (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
    Fin (finrank ℝ S.covector.ker) → ℝ :=
  originalSeedKernel S w (c - S.level) *ᵥ originalSeedCrossingMomentum S w c m

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original crossing momentum is integrable for every
clock, using only the existing original weighted-energy momentum estimate. -/
theorem integrable_original_crossingMomentum
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (c : ℝ) :
    Integrable (originalSeedCrossingMomentum S w c)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
  (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).1.indicator
    (measurableSet_originalClockCrossingSet _ c)

/-- Original value minimality forces zero momentum in each actual crossing
component, via source and target Borel prefix centering on the same true Palm. -/
theorem setIntegral_original_crossingMomentum_component_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t)
    (c : ℝ) (i : Fin (finrank ℝ S.covector.ker)) :
    (∫ m in originalClockCrossingSet (finrank ℝ S.covector.ker) c,
      originalSeedPairMomentum S w m i
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 := by
  have hp := (D.integrable_original_pair_momentum_of_weighted_stationary
    hF hw hgap hbounds Q).1.eval i
  have he := setIntegral_originalClockCrossing_eq_prefix_sub _ hp Q.ae_palm_forward c
  obtain ⟨hs, ht⟩ := D.setIntegral_original_momentum_clock_eq_zero_of_minimal_value
    hF hw hgap hbounds Q t hmin i (Iic c) measurableSet_Iic
  simp only [mem_Iic] at hs ht
  rw [hs, ht, sub_self] at he
  exact he

/-- The entire original crossing momentum has zero vector mean. The
original minimization class and original true Palm are unchanged. -/
theorem integral_original_crossingMomentum_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t) (c : ℝ) :
    (∫ m, originalSeedCrossingMomentum S w c m
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 := by
  have hp := D.integrable_original_crossingMomentum hF hw hgap hbounds Q c
  ext i
  let L : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have he := L.integral_comp_comm hp
  change (∫ m, originalSeedCrossingMomentum S w c m i
    ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) =
    (∫ m, originalSeedCrossingMomentum S w c m
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) i at he
  rw [← he]
  have he' (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :
      originalSeedCrossingMomentum S w c m i =
      (originalClockCrossingSet (finrank ℝ S.covector.ker) c).indicator
        (fun m ↦ originalSeedPairMomentum S w m i) m := by
    by_cases hm : m ∈ originalClockCrossingSet (finrank ℝ S.covector.ker) c <;>
      simp [originalSeedCrossingMomentum, hm]
  simp_rw [he']
  rw [integral_indicator (measurableSet_originalClockCrossingSet _ c)]
  exact D.setIntegral_original_crossingMomentum_component_eq_zero_of_minimal_value
    hF hw hgap hbounds Q t hmin c i

/-- The genuine original path velocity at each occupied clock has a finite
first moment, without an unweighted displacement second moment. -/
theorem integrable_original_clockOccupation
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (c : ℝ) :
    Integrable (originalSeedClockOccupation S w c)
      (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  let L : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ) :=
    (originalSeedKernel S w (c - S.level)).mulVecLin.toContinuousLinearMap
  exact L.integrable_comp (D.integrable_original_crossingMomentum hF hw hgap hbounds Q c)

/-- The actual original compliance-path traffic is centered at every
deterministic original clock. Centering is derived from actual value minimality. -/
theorem integral_original_clockOccupation_eq_zero_of_minimal_value
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ R.value t) (c : ℝ) :
    (∫ m, originalSeedClockOccupation S w c m
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0 := by
  let L : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ) :=
    (originalSeedKernel S w (c - S.level)).mulVecLin.toContinuousLinearMap
  change (∫ m, L (originalSeedCrossingMomentum S w c m)
    ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) = 0
  rw [L.integral_comp_comm (D.integrable_original_crossingMomentum hF hw hgap hbounds Q c),
    D.integral_original_crossingMomentum_eq_zero_of_minimal_value hF hw hgap hbounds Q t hmin c,
    _root_.map_zero]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
