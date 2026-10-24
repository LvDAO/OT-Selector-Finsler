import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingRawCube
import OTSelector.Transport.Coupling.FiniteAtomicSourceDisintegration

/-! Probability smoothing laws for unchanged actual raw reserve observations. -/

open MeasureTheory Set
open OTSelector.Probability
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The actual target law assigned to each unchanged original raw reserve atom
by RN disintegration of its genuine raw empirical-to-population plan. -/
def originalRawCubeAtomPopulationLaw {q n : ℕ}
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (x : Fin n → (Fin q → ℝ)) (i : Fin n) :
    Measure (EuclideanSpace ℝ (Fin q)) :=
  originalAtomPopulationLaw (fun i ↦ originalRawCubePhysicalMap z L (x i))
    (originalRawCubePopulationCoupling z L x) i

/-- Every actual original raw atom yields a probability law. Their sum is
exactly the population target and their actual endpoint energies recover the
same plan's physical energy. No energy or law estimate is an input. -/
theorem originalRawCubeAtomPopulationLaw_spec {q n : ℕ}
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ) (x : Fin n → (Fin q → ℝ))
    (hx : ∀ i, x i ∈ unitCube q) :
    (∀ i, IsProbabilityMeasure (originalRawCubeAtomPopulationLaw z L x i)) ∧
      (∑ i, originalRawCubeAtomPopulationLaw z L x i) =
        (n : ℝ≥0∞) • (cubeMeasure (Fin q) 1).map (originalRawCubePhysicalMap z L) ∧
      (∀ i, Integrable (fun v ↦ dist (originalRawCubePhysicalMap z L (x i)) v ^ 2)
        (originalRawCubeAtomPopulationLaw z L x i)) ∧
      (∑ i, ∫ v, dist (originalRawCubePhysicalMap z L (x i)) v ^ 2
        ∂originalRawCubeAtomPopulationLaw z L x i) =
          ∫ p, ‖p.1 - p.2‖ ^ 2 ∂originalRawCubePopulationCoupling z L x := by
  have hΓ := (originalRawCubePopulationCoupling_spec z L).2 x hx
  have : IsFiniteMeasure (originalRawCubePopulationCoupling z L x) := hΓ.1
  have hcost : Integrable (fun p ↦ dist p.1 p.2 ^ 2)
      (originalRawCubePopulationCoupling z L x) := by
    simpa only [dist_eq_norm, originalRawCubePopulationCoupling] using
      (originalIIDPhysicalCubePopulationCoupling_squareCost_le
      (originalNormalizedCubeLaw q) z L (fun i ↦ originalUnitCubeNormalization (x i))).1
  have h := originalAtomPopulationLaw_spec (fun i ↦ originalRawCubePhysicalMap z L (x i))
    (originalRawCubePopulationCoupling z L x) hΓ.2.1 hcost
  refine ⟨h.1, h.2.1.trans hΓ.2.2, h.2.2.1, ?_⟩
  simpa only [dist_eq_norm, originalRawCubeAtomPopulationLaw] using h.2.2.2

end OTSelector.Reconstruction
