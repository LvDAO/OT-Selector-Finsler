import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedPopulationEnergy
import OTSelector.Transport.Coupling.FiniteAtomicSourceDisintegration

/-! Each genuinely selected original fine-class label carries its own RN
probability law, with literal h_D/V density on the same physical oriented cube. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- The unchanged physical point of an actual original selected reserve label. -/
def originalReserveBlockClassOrientedAtomPoint
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) (S T C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (i : Fin (originalReserveBlockClassCount (originalCenteredPhysicalCubeRegion frame (2*R))
      own other S T C D p)) : EuclideanSpace ℝ (Fin q) :=
  (EuclideanSpace.equiv (Fin q) ℝ).symm (originalOrientedRawCubePhysicalMap frame R
    ((originalReserveBlockClassInputReadout (originalCenteredPhysicalCubeRegion frame (2*R))
      own other S T C D (originalReserveBlockClassCount (originalCenteredPhysicalCubeRegion frame (2*R))
        own other S T C D p) p).2 i))

/-- The actual RN population law attached to this unchanged original atom. -/
def originalReserveBlockClassOrientedAtomLaw
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) (S T C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (i : Fin (originalReserveBlockClassCount (originalCenteredPhysicalCubeRegion frame (2*R))
      own other S T C D p)) : Measure (EuclideanSpace ℝ (Fin q)) :=
  originalAtomPopulationLaw (originalReserveBlockClassOrientedAtomPoint frame R own other S T C D p)
    (originalReserveBlockClassOrientedPopulationRandom frame R own other S T C D p) i

/-- Sum the genuine endpoint deviation energies over all original h_D labels. -/
def originalReserveBlockClassOrientedAtomEnergy
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) (S T C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : ℝ :=
  ∑ i, ∫ v, dist (originalReserveBlockClassOrientedAtomPoint frame R own other S T C D p i) v ^ 2
    ∂originalReserveBlockClassOrientedAtomLaw frame R own other S T C D p i

/-- This fine class's original-label probability laws sum to literal h_D/V
physical density and retain their exact original indices, marks and plan energy. -/
def OriginalReserveBlockClassOrientedAtomSpec
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) (S T C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : Prop :=
  let K := originalCenteredPhysicalCubeRegion frame (2*R)
  let N := originalReserveBlockClassCount K own other S T C D p
  let x := originalReserveBlockClassOrientedAtomPoint frame R own other S T C D p
  let κ := originalReserveBlockClassOrientedAtomLaw frame R own other S T C D p
  (∀ i, IsProbabilityMeasure (κ i)) ∧
    (∑ i, κ i) = ((volume.restrict K).withDensity
      (fun _ ↦ ENNReal.ofReal ((N : ℝ) / volume.real K))).map (EuclideanSpace.equiv (Fin q) ℝ).symm ∧
    (∀ i, Integrable (fun v ↦ dist (x i) v ^ 2) (κ i)) ∧
    originalReserveBlockClassOrientedAtomEnergy frame R own other S T C D p =
      ∫ v, ‖v.1-v.2‖^2 ∂originalReserveBlockClassOrientedPopulationRandom frame R own other S T C D p ∧
    ∀ i : Fin N,
      let a := originalReserveBlockClassSelection K own other S T C D N (originalReserveExcessInputAux p) i
      a < p.2.1 ∧ (p.2.2 a).2 ∈ D

/-- Independent original auxiliary data and the own original Poisson reserve
construct every actual fine-class RN law and its full expected endpoint energy.
This applies equally to a genuine complementary-dilation main law. -/
theorem originalReserveBlockClassOrientedAtomLaws
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 < R)
    (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) (hq : 4 < q) :
    let M := P.prod (markedPoissonLaw q ℝ μ rate)
    let E := originalReserveBlockClassOrientedAtomEnergy frame R own other S T C D
    (∀ᵐ p ∂M, OriginalReserveBlockClassOrientedAtomSpec frame R own other S T C D p) ∧
      Integrable E M ∧ (∫ p, E p ∂M) ≤
        ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  let K := originalCenteredPhysicalCubeRegion frame (2*R)
  let M := P.prod (markedPoissonLaw q ℝ μ rate)
  let N := originalReserveBlockClassCount K own other S T C D
  have he := originalReserveBlockClassOrientedPopulation_random_spec_and_energy P μ rate frame hR
    own other hS hT hC hD hq
  have hs : ∀ᵐ p ∂M, OriginalReserveBlockClassOrientedAtomSpec frame R own other S T C D p := by
    filter_upwards [he.1] with p hp
    let Γ := originalReserveBlockClassOrientedPopulationRandom frame R own other S T C D p
    let x := originalReserveBlockClassOrientedAtomPoint frame R own other S T C D p
    have : IsFiniteMeasure Γ := hp.1
    have hcost : Integrable (fun v ↦ dist v.1 v.2 ^ 2) Γ := by simpa only [dist_eq_norm] using hp.2.1
    have hsource : Γ.fst = ∑ i, Measure.dirac (x i) := hp.2.2.1
    have h := originalAtomPopulationLaw_spec x Γ hsource hcost
    refine ⟨h.1, h.2.1.trans hp.2.2.2, h.2.2.1, ?_, ?_⟩
    · simpa only [originalReserveBlockClassOrientedAtomEnergy, originalReserveBlockClassOrientedAtomLaw,
        dist_eq_norm] using h.2.2.2
    · intro i
      exact originalReserveBlockClassSelection_observed_mark K own other S T C D (N p)
        (originalReserveExcessInputAux p) rfl i
  have hEq : originalReserveBlockClassOrientedAtomEnergy frame R own other S T C D =ᵐ[M]
      (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂originalReserveBlockClassOrientedPopulationRandom frame R own other S T C D p) :=
    hs.mono fun _ hp ↦ hp.2.2.2.1
  exact ⟨hs, he.2.1.congr hEq.symm, (integral_congr_ae hEq).trans_le he.2.2⟩

end OTSelector.Reconstruction
