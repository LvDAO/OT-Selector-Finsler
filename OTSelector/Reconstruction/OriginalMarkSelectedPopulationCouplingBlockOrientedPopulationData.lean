import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockClassSelection
import OTSelector.Reconstruction.OriginalReserveFullUnitInputBlockClassSelection
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolumeDensity
import OTSelector.MeasureTheory.CountFiberIntegration
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts

/-! Actual fine-class original reserve coordinates after blockwise deletion,
and their concrete same-frame Euclidean population plan at the actual count. -/

open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}

private theorem measurable_blockPopulationAux :
    Measurable (originalReserveExcessInputAux (q := q)) := by
  unfold originalReserveExcessInputAux
  fun_prop

/-- The actual h_D is the number of observed original reserve indices in fine
class D after this block's true excess deletion. -/
def originalReserveBlockClassCount (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : ℕ :=
  (originalReserveBlockClassKept K own other S T C D (originalReserveExcessInputAux p)).card

theorem measurable_originalReserveBlockClassCount {K : Set (Fin q → ℝ)} (hK : MeasurableSet K)
    (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Measurable (originalReserveBlockClassCount K own other S T C D) :=
  (measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
    ((measurable_originalReserveBlockClassKept hK own other hS hT hC hD).comp measurable_blockPopulationAux)

/-- The true selected fine-class count is bounded by the actual own Poisson
prefix count, without any successful-deletion or capacity premise. -/
theorem originalReserveBlockClassCount_le (K : Set (Fin q → ℝ)) (own other : Fin 2)
    (S T C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    originalReserveBlockClassCount K own other S T C D p ≤ p.2.1 := by
  classical
  have hsub : originalReserveBlockClassKept K own other S T C D (originalReserveExcessInputAux p) ⊆
      Finset.range p.2.1 := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1).1).1
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

/-- A separate genuine population coupling is built for this fine class D in
the same fixed physical frame, rather than spreading the whole balanced block. -/
def originalReserveBlockClassOrientedPopulation
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) (S T C D : Set ℝ) (k : ℕ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)) :=
  originalOrientedEuclideanCubePopulationCoupling frame R
    (originalReserveBlockClassInputReadout (originalCenteredPhysicalCubeRegion frame (2*R))
      own other S T C D k p).2

/-- The concrete same-class plan uses its actual random surviving count h_D. -/
def originalReserveBlockClassOrientedPopulationRandom
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) (S T C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin q)) :=
  originalReserveBlockClassOrientedPopulation frame R own other S T C D
    (originalReserveBlockClassCount (originalCenteredPhysicalCubeRegion frame (2*R)) own other S T C D p) p

theorem measurable_originalReserveBlockClassOrientedPopulationRandom
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (own other : Fin 2) {S T C D : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Measurable (originalReserveBlockClassOrientedPopulationRandom frame R own other S T C D) := by
  let K := originalCenteredPhysicalCubeRegion frame (2*R)
  have hK := (isCompact_originalStagePhysicalCube frame (2*R)).measurableSet
  exact measurable_count_diagonal (originalReserveBlockClassCount K own other S T C D)
    (measurable_originalReserveBlockClassCount hK own other hS hT hC hD)
    (fun k p ↦ originalReserveBlockClassOrientedPopulation frame R own other S T C D k p)
    (fun k ↦ (measurable_originalOrientedEuclideanCubePopulationCoupling frame R).comp
      (measurable_originalReserveBlockClassInputReadout hK own other hS hT hC hD k).snd)

end OTSelector.Reconstruction
