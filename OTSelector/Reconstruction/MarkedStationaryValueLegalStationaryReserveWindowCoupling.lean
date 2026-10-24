import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowCoupling
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReserveInput

/-!
# Literal original Poisson windows for a retained partial scene with reserve

The two genuine original laws are independently dilated and superposed at
actual intensities summing to one. Exact original compact Laplace readouts
identify their complete input restriction and couple literal finite Poisson
arrays with the retained partial scene. No full-matching claim is made for
that scene, and no law is imposed on adaptively retained endpoints.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance reserveInputWindowLawInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance reserveInputWindowLawPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual retained-plan/reserve-input scene has the unchanged original
unit-intensity colored Poisson window law, including clock labels. -/
theorem map_originalDilatedReserve_inputRestriction_eq_originalPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (legalMarkedReserveInputLaw q
        (legalMarkedInputDilationLaw q c hc M.law)
        (legalMarkedInputDilationLaw q d hd N.law) :
          Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)).restrict U) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) := by
  exact map_inputRestriction_eq_originalPoisson_of_laplace
    (legalMarkedReserveInputLaw q (legalMarkedInputDilationLaw q c hc M.law)
      (legalMarkedInputDilationLaw q d hd N.law))
    (original_dilated_reserve_input_laplace M N c d hc hd hunit) hU

/-- The same original input restriction equality on the locally finite
carrier used by disintegration and the finite-array readout. -/
theorem map_originalDilatedReserve_inputRestrictionLocal_eq_originalPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (legalMarkedReserveInputLaw q
        (legalMarkedInputDilationLaw q c hc M.law)
        (legalMarkedInputDilationLaw q d hd N.law) :
          Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ legalInputRestrictionLocal U s.2) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)) := by
  exact map_inputRestrictionLocal_eq_originalPoisson_of_laplace
    (legalMarkedReserveInputLaw q (legalMarkedInputDilationLaw q c hc M.law)
      (legalMarkedInputDilationLaw q d hd N.law))
    (original_dilated_reserve_input_laplace M N c d hc hd hunit) hU

/-- Literal original finite Poisson arrays and the actual retained partial
scene admit one joining. Both complete marginals are unchanged and their
colored input window measures coincide almost surely. -/
theorem exists_originalDilatedReserve_originalPoisson_windowCoupling
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0, ∃ R : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
        Prod.fst =
        (legalMarkedReserveInputLaw q
          (legalMarkedInputDilationLaw q c hc M.law)
          (legalMarkedInputDilationLaw q d hd N.law) :
            Measure (LegalMarkedOptimalInputScene q)) ∧
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
        Prod.snd = legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        legalInputRestrictionLocal U p.1.2 =
        legalInputRestrictionLocal U (legalInputTwoBlockLocal q p.2) := by
  exact exists_originalPoisson_windowCoupling_of_laplace
    (legalMarkedReserveInputLaw q (legalMarkedInputDilationLaw q c hc M.law)
      (legalMarkedInputDilationLaw q d hd N.law))
    (original_dilated_reserve_input_laplace M N c d hc hd hunit) hU

end OTSelector.Reconstruction
