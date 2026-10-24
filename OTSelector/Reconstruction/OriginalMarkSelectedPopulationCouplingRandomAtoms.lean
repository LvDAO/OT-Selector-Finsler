import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingRandomCount
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOriginalAtomDensityCentered

/-! Actual random original reserve atom laws, their literal cube density, and energy. -/

open MeasureTheory Set Function
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q : ℕ}

/-- The unchanged physical position of one actual selected original reserve index. -/
def originalReserveExcessClassRandomAtomPoint (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (i : Fin (originalReserveExcessClassCount R own other C D p)) : EuclideanSpace ℝ (Fin q) :=
  originalRawCubePhysicalMap z L
    ((originalReserveExcessClassInputReadout R own other C D
      (originalReserveExcessClassCount R own other C D p) p).2 i)

/-- The actual RN population law belonging to that unchanged original reserve atom. -/
def originalReserveExcessClassRandomAtomLaw (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (i : Fin (originalReserveExcessClassCount R own other C D p)) :
    Measure (EuclideanSpace ℝ (Fin q)) :=
  originalAtomPopulationLaw (originalReserveExcessClassRandomAtomPoint R own other C D z L p)
    (originalReserveExcessClassPopulationCouplingRandom R own other C D z L p) i

/-- Sum of the true endpoint deviation energies of all actual retained class atoms. -/
def originalReserveExcessClassRandomAtomEnergy (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (z : EuclideanSpace ℝ (Fin q)) (L : ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : ℝ :=
  ∑ i, ∫ v, dist (originalReserveExcessClassRandomAtomPoint R own other C D z L p i) v ^ 2
    ∂originalReserveExcessClassRandomAtomLaw R own other C D z L p i

/-- Concrete probability laws on the centered physical cube, with literal count/V
target density, exact energy, and unchanged observed indices carrying their actual marks. -/
def OriginalReserveExcessClassRandomAtomSpec (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : Prop :=
  let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
  let x := originalReserveExcessClassRandomAtomPoint R own other C D z (2*R) p
  let κ := originalReserveExcessClassRandomAtomLaw R own other C D z (2*R) p
  let N := originalReserveExcessClassCount R own other C D p
  (∀ i, IsProbabilityMeasure (κ i)) ∧
    (∑ i, κ i) = ((volume.restrict (haarRootCube (Fin q) R)).withDensity
      (fun _ ↦ ENNReal.ofReal ((N : ℝ) / volume.real (haarRootCube (Fin q) R)))).map
        (EuclideanSpace.equiv (Fin q) ℝ).symm ∧
    (∀ i, Integrable (fun v ↦ dist (x i) v ^ 2) (κ i)) ∧
    originalReserveExcessClassRandomAtomEnergy R own other C D z (2*R) p =
      ∫ v, ‖v.1-v.2‖^2 ∂originalReserveExcessClassPopulationCouplingRandom R own other C D z (2*R) p ∧
    ∀ i : Fin N,
      let a := originalReserveSceneExcessClassSelection R own other C D N (originalReserveExcessInputAux p) i
      a < p.2.1 ∧ (p.2.2 a).2 ∈ D

private theorem randomAtomLaws_of_actual_count_fibres
    {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω)
    (view : Ω → (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (R : ℝ) (hR : 0 < R) (own other : Fin 2) (C D : Set ℝ) (B : ℝ)
    (hfibre : ∀ k,
      let Mk := M.restrict {p | originalReserveExcessClassCount R own other C D (view p) = k}
      let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
      let read := originalReserveExcessClassInputReadout R own other C D k ∘ view
      let Γ := fun p ↦ originalReserveExcessClassPopulationCoupling R own other C D k z (2*R) (view p)
      ∀ᵐ p ∂Mk, IsFiniteMeasure (Γ p) ∧ Integrable (fun v ↦ ‖v.1-v.2‖^2) (Γ p) ∧
        (Γ p).map Prod.fst = ∑ i, Measure.dirac (originalRawCubePhysicalMap z (2*R) ((read p).2 i)) ∧
        (Γ p).map Prod.snd = (k : ℝ≥0∞) • (cubeMeasure (Fin q) 1).map
          (originalRawCubePhysicalMap z (2*R)))
    (henergy : let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
      let Γ := originalReserveExcessClassPopulationCouplingRandom R own other C D z (2*R) ∘ view
      Integrable (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂Γ p) M ∧
        (∫ p, ∫ v, ‖v.1-v.2‖^2 ∂Γ p ∂M) ≤ B) :
    let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
    let E := originalReserveExcessClassRandomAtomEnergy R own other C D z (2*R) ∘ view
    (∀ᵐ p ∂M, OriginalReserveExcessClassRandomAtomSpec R own other C D (view p)) ∧
      Integrable E M ∧ (∫ p, E p ∂M) ≤ B := by
  let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
  let N := originalReserveExcessClassCount R own other C D ∘ view
  have hΓ := randomCount_ae_of_restrict M N _ hfibre
  have hs : ∀ᵐ p ∂M, OriginalReserveExcessClassRandomAtomSpec R own other C D (view p) := by
    filter_upwards [hΓ] with p hp
    let v := view p
    let Γ := originalReserveExcessClassPopulationCouplingRandom R own other C D z (2*R) v
    let x := originalReserveExcessClassRandomAtomPoint R own other C D z (2*R) v
    have : IsFiniteMeasure Γ := hp.1
    have hcost : Integrable (fun u ↦ ‖u.1-u.2‖^2) Γ := hp.2.1
    have hc : Integrable (fun u ↦ dist u.1 u.2 ^ 2) Γ := by
      simpa only [dist_eq_norm] using hcost
    have hx : Γ.fst = ∑ i, Measure.dirac (x i) := hp.2.2.1
    have h := originalAtomPopulationLaw_spec x Γ hx hc
    refine ⟨h.1, h.2.1.trans (hp.2.2.2.trans
      (originalRawCubePopulationTarget_eq_centered_density q (N p) hR)), h.2.2.1, ?_, ?_⟩
    · simpa only [originalReserveExcessClassRandomAtomEnergy, originalReserveExcessClassRandomAtomLaw,
        dist_eq_norm] using h.2.2.2
    · intro i
      exact originalReserveSceneExcessClassSelection_observed_mark R own other C D
        (N p) (originalReserveExcessInputAux v) rfl i
  have hEq : (originalReserveExcessClassRandomAtomEnergy R own other C D z (2*R) ∘ view) =ᵐ[M]
      (fun p ↦ ∫ v, ‖v.1-v.2‖^2 ∂originalReserveExcessClassPopulationCouplingRandom
        R own other C D z (2*R) (view p)) := hs.mono fun p hp ↦ hp.2.2.2.1
  exact ⟨hs, henergy.1.congr hEq.symm, (integral_congr_ae hEq).trans_le henergy.2⟩

variable {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- All actual source retained-class atom laws under the same experiment satisfy
the true density identity and full fractional reserve energy rate. -/
theorem LegalWeightedStationaryPoissonMatching.original_sourceReserveClass_randomAtomLaws
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    {R : ℝ} (hR : 0 < R) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hq : 4 < q) :
    let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
    let E := originalReserveExcessClassRandomAtomEnergy R 0 1 C D z (2*R) ∘ originalSourceReserveExperimentSplice
    (∀ᵐ p ∂originalMainReserveExperimentLaw Q rate,
      OriginalReserveExcessClassRandomAtomSpec R 0 1 C D (originalSourceReserveExperimentSplice p)) ∧
      Integrable E (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, E p ∂originalMainReserveExperimentLaw Q rate) ≤
        ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
  exact randomAtomLaws_of_actual_count_fibres _ _ R hR 0 1 C D _
    (fun k ↦ (Q.original_sourceReserveClass_populationCoupling rate R hC hD k hq z (2*R)).2.1)
    (Q.original_sourceReserveClass_randomPopulationCoupling rate R hC hD hq z (2*R)).2.2

/-- The target laws use the identical joined original observations and satisfy
the same literal density and complete expected endpoint energy bound. -/
theorem LegalWeightedStationaryPoissonMatching.original_targetReserveClass_randomAtomLaws
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    {R : ℝ} (hR : 0 < R) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hq : 4 < q) :
    let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
    let E := originalReserveExcessClassRandomAtomEnergy R 1 0 C D z (2*R) ∘ originalTargetReserveExperimentSplice
    (∀ᵐ p ∂originalMainReserveExperimentLaw Q rate,
      OriginalReserveExcessClassRandomAtomSpec R 1 0 C D (originalTargetReserveExperimentSplice p)) ∧
      Integrable E (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, E p ∂originalMainReserveExperimentLaw Q rate) ≤
        ((q : ℝ)*(2*R)^2)*dyadicMatchingConstant q*(rate : ℝ)^(1-2/(q : ℝ)) := by
  let z := (EuclideanSpace.equiv (Fin q) ℝ).symm (fun _ ↦ -R)
  exact randomAtomLaws_of_actual_count_fibres _ _ R hR 1 0 C D _
    (fun k ↦ (Q.original_targetReserveClass_populationCoupling rate R hC hD k hq z (2*R)).2.1)
    (Q.original_targetReserveClass_randomPopulationCoupling rate R hC hD hq z (2*R)).2.2

end OTSelector.Reconstruction
