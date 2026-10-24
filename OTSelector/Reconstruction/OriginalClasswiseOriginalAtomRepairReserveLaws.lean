import OTSelector.Transport.Coupling.FiniteAtomicSourceDisintegration
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingPhysical

/-! Actual reserve spreading supplies unit-mass laws for the unchanged original
reserve labels, with an exact total endpoint-energy identity. -/
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
variable {q n : ℕ}

/-- The real population law assigned by RN disintegration to one original reserve atom. -/
def originalPhysicalReserveAtomLaw (μ : Measure (DyadicUnitCube q))
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (x : Fin n → DyadicUnitCube q) :
    Fin n → Measure (EuclideanSpace ℝ (Fin q)) :=
  originalAtomPopulationLaw (fun i ↦ originalIIDCubePhysicalMap z L (x i))
    (originalIIDPhysicalCubePopulationCoupling μ z L x)

/-- The actual reserve endpoint laws sum to the full constant-population target
and their true endpoint energies equal the real reserve spreading cost. -/
theorem originalPhysicalReserveAtomLaw_spec
    (μ : Measure (DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (x : Fin n → DyadicUnitCube q) :
    (∀ i, IsProbabilityMeasure (originalPhysicalReserveAtomLaw μ z L x i)) ∧
      (∑ i, originalPhysicalReserveAtomLaw μ z L x i) =
        (n : ℝ≥0∞) • μ.map (originalIIDCubePhysicalMap z L) ∧
      (∀ i, Integrable (fun v ↦ ‖originalIIDCubePhysicalMap z L (x i) - v‖ ^ 2)
        (originalPhysicalReserveAtomLaw μ z L x i)) ∧
      (∑ i, ∫ v, ‖originalIIDCubePhysicalMap z L (x i) - v‖ ^ 2
        ∂originalPhysicalReserveAtomLaw μ z L x i) =
        ∫ p, ‖p.1 - p.2‖ ^ 2 ∂originalIIDPhysicalCubePopulationCoupling μ z L x := by
  have hΓ := originalIIDPhysicalCubePopulationCoupling_marginals μ z L x
  have : IsFiniteMeasure (originalIIDPhysicalCubePopulationCoupling μ z L x) := hΓ.1
  have hcost : Integrable (fun p ↦ dist p.1 p.2 ^ 2)
      (originalIIDPhysicalCubePopulationCoupling μ z L x) := by
    simpa only [dist_eq_norm] using
      (originalIIDPhysicalCubePopulationCoupling_squareCost_le μ z L x).1
  obtain ⟨hprob, hsum, hI, henergy⟩ := originalAtomPopulationLaw_spec
    (fun i ↦ originalIIDCubePhysicalMap z L (x i))
    (originalIIDPhysicalCubePopulationCoupling μ z L x) hΓ.2.1 hcost
  exact ⟨hprob, hsum.trans hΓ.2.2,
    by simpa only [dist_eq_norm, originalPhysicalReserveAtomLaw] using hI,
    by simpa only [dist_eq_norm, originalPhysicalReserveAtomLaw] using henergy⟩

end OTSelector.Reconstruction
