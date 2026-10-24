import OTSelector.Analysis.CanonicalUnitCurve
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Canonical unit-clock curve measurability from mobility regularity only on that clock window. -/
open Set Function MeasureTheory
open scoped Classical NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Only the actual unit-clock mobility must be Lipschitz; its values outside that
window need not be measurable. Its literal zero extension is Borel. -/
theorem measurable_unitPhaseMobility_of_lipschitzOn
    (R : ℝ → V →L[ℝ] V) {A : ℝ} (hA : 0 ≤ A)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|) :
    Measurable (unitPhaseMobility R) := by
  have hLip : LipschitzOnWith (Real.toNNReal A) R (Icc (0 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro r hr s hs
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hA]
    exact hRLip r hr s hs
  have hz : ContinuousOn (0 : ℝ → V →L[ℝ] V) (Icc (0 : ℝ) 1)ᶜ := continuousOn_const
  have hm := hLip.continuousOn.measurable_piecewise hz measurableSet_Icc
  rw [Set.piecewise_eq_indicator] at hm
  exact hm

/-- Reapplying the original unit-clock zero extension leaves it unchanged. -/
theorem unitPhaseMobility_idempotent (R : ℝ → V →L[ℝ] V) :
    unitPhaseMobility (unitPhaseMobility R) = unitPhaseMobility R := by
  funext r
  by_cases hr : r ∈ Icc (0 : ℝ) 1
  · simp only [unitPhaseMobility, indicator_of_mem hr]
  · simp only [unitPhaseMobility, indicator_of_notMem hr]

/-- The literal canonical inverse uses only the once-clipped actual mobility. -/
theorem canonicalUnitPhasePosition_unitPhaseMobility
    (P : V → V) {L : ℝ} (hP : ∀ z y, ‖P z - P y‖ ≤ L * ‖z - y‖)
    (R : ℝ → V →L[ℝ] V)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) (r : ℝ) :
    canonicalUnitPhasePosition P hP (unitPhaseMobility R)
      (fun r _ ↦ unitPhaseMobility_small R hsmall r) r =
      canonicalUnitPhasePosition P hP R hsmall r := by
  simp only [canonicalUnitPhasePosition, unitPhaseMobility_idempotent]

/-- Joint Borel measurability of the same canonical inverse needs regularity
only on the actual unit interval. No measurable extension of raw mobility is supplied. -/
theorem measurable_canonicalUnitPhasePosition_of_lipschitzOn
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {Ω : Type*} [MeasurableSpace Ω] {P : Ω → V → V} {L : ℝ}
    (hP : Measurable (uncurry P))
    (hLip : ∀ ω z y, ‖P ω z - P ω y‖ ≤ L * ‖z - y‖)
    (R : ℝ → V →L[ℝ] V) {A : ℝ} (hA : 0 ≤ A)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : Ω × ℝ ↦ canonicalUnitPhasePosition (P a.1) (hLip a.1) R hsmall a.2) := by
  have hm := measurable_canonicalUnitPhasePosition hP hLip (unitPhaseMobility R)
    (measurable_unitPhaseMobility_of_lipschitzOn R hA hRLip)
    (fun r _ ↦ unitPhaseMobility_small R hsmall r)
  simpa only [canonicalUnitPhasePosition, unitPhaseMobility_idempotent] using hm

variable {q : ℕ}

/-- The actual paired position-momentum curve is unchanged by repeated unit clipping. -/
theorem canonicalUnitPhasePair_unitPhaseMobility
    (P : (Fin q → ℝ) → Fin q → ℝ) {L : ℝ}
    (hP : ∀ z y, ‖P z - P y‖ ≤ L * ‖z - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) (r : ℝ) :
    canonicalUnitPhasePair P hP (unitPhaseMobility R)
      (fun r _ ↦ unitPhaseMobility_small R hsmall r) r =
      canonicalUnitPhasePair P hP R hsmall r := by
  simp only [canonicalUnitPhasePair, canonicalUnitPhasePosition, unitPhaseMobility_idempotent]

/-- The same canonical paired curve is jointly Borel under actual on-window mobility bounds. -/
theorem measurable_canonicalUnitPhasePair_of_lipschitzOn
    {Ω : Type*} [MeasurableSpace Ω] {P : Ω → (Fin q → ℝ) → Fin q → ℝ} {L : ℝ}
    (hP : Measurable (uncurry P))
    (hLip : ∀ ω z y, ‖P ω z - P ω y‖ ≤ L * ‖z - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)) {A : ℝ} (hA : 0 ≤ A)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) :
    Measurable (fun a : Ω × ℝ ↦ canonicalUnitPhasePair (P a.1) (hLip a.1) R hsmall a.2) := by
  have hm := measurable_canonicalUnitPhasePair hP hLip (unitPhaseMobility R)
    (measurable_unitPhaseMobility_of_lipschitzOn R hA hRLip)
    (fun r _ ↦ unitPhaseMobility_small R hsmall r)
  simpa only [canonicalUnitPhasePair, canonicalUnitPhasePosition,
    unitPhaseMobility_idempotent] using hm

end OTSelector.Reconstruction
