import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawJoinedExperiment
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawActualClass

/-! Classwise selected original reserve spatial laws in the same joined experiment. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Actual original observed positions at the measurable mark-selected original indices. -/
def originalReserveExcessClassInputReadout (R : ℝ) (own other : Fin 2) (C D : Set ℝ) (k : ℕ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    OriginalReserveSceneAux q × (Fin k → (Fin q → ℝ)) :=
  (originalReserveExcessInputAux p, fun j ↦
    (p.2.2 (originalReserveSceneExcessClassSelection R own other C D k (originalReserveExcessInputAux p) j)).1)

/-- The actual selected readout is measurable from the same original observations. -/
theorem measurable_originalReserveExcessClassInputReadout (R : ℝ) (own other : Fin 2)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    Measurable (originalReserveExcessClassInputReadout (q := q) R own other C D k) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hpositions : Measurable (fun p :
      (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ ↦
      fun i ↦ (p.2.2 i).1) := by fun_prop
  have heval : Measurable (fun p : ℕ × (ℕ → (Fin q → ℝ)) ↦ p.2 p.1) :=
    measurable_from_prod_countable_right (fun i ↦ measurable_pi_apply i)
  exact haux.prodMk (measurable_pi_lambda _ (fun j ↦ heval.comp
    (((measurable_originalReserveSceneExcessClassSelection_apply R own other hC hD k j).comp haux).prodMk hpositions)))

variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The actual source reserve selected by the actual same-scene full excess has its exact
finite iid spatial law on each actual kept-count fibre of the single joined experiment. -/
theorem LegalWeightedStationaryPoissonMatching.original_sourceReserveExcessClassSelection_jointLaw
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    (R : ℝ) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    ((originalMainReserveExperimentLaw Q rate).restrict
      {p | (originalReserveSceneExcessClassKept R 0 1 C D
        (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p))).card = k}).map
      (originalReserveExcessClassInputReadout R 0 1 C D k ∘ originalSourceReserveExperimentSplice) =
      ((((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ β rate)).prod
        (originalReserveCountMarkLaw α rate)).restrict
          {z | (originalReserveSceneExcessClassKept R 0 1 C D z).card = k}).prod
        (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  have hsplice : Measurable (originalSourceReserveExperimentSplice (q := q)) := by
    unfold originalSourceReserveExperimentSplice
    fun_prop
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hE : MeasurableSet {p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ |
      (originalReserveSceneExcessClassKept R 0 1 C D (originalReserveExcessInputAux p)).card = k} :=
    (measurableSet_originalReserveSceneExcessClassKept_card (q := q) R 0 1 hC hD k).preimage haux
  change ((originalMainReserveExperimentLaw Q rate).restrict
    (originalSourceReserveExperimentSplice ⁻¹' {p | (originalReserveSceneExcessClassKept R 0 1 C D
      (originalReserveExcessInputAux p)).card = k})).map
        (originalReserveExcessClassInputReadout R 0 1 C D k ∘ originalSourceReserveExperimentSplice) = _
  rw [← Measure.map_map (measurable_originalReserveExcessClassInputReadout R 0 1 hC hD k) hsplice,
    ← Measure.restrict_map hsplice hE, map_originalSourceReserveExperimentSplice]
  exact map_originalReserveSceneExcessClassSelection_actual_jointLaw _ α rate R 0 1 hC hD k

/-- The target law is obtained by reordering this same joined experiment, preserving the
same original main scene, both reserve observations and all their original indices. -/
theorem LegalWeightedStationaryPoissonMatching.original_targetReserveExcessClassSelection_jointLaw
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    (R : ℝ) {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) (k : ℕ) :
    ((originalMainReserveExperimentLaw Q rate).restrict
      {p | (originalReserveSceneExcessClassKept R 1 0 C D
        (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p))).card = k}).map
      (originalReserveExcessClassInputReadout R 1 0 C D k ∘ originalTargetReserveExperimentSplice) =
      ((((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ α rate)).prod
        (originalReserveCountMarkLaw β rate)).restrict
          {z | (originalReserveSceneExcessClassKept R 1 0 C D z).card = k}).prod
        (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  have hsplice : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hE : MeasurableSet {p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ |
      (originalReserveSceneExcessClassKept R 1 0 C D (originalReserveExcessInputAux p)).card = k} :=
    (measurableSet_originalReserveSceneExcessClassKept_card (q := q) R 1 0 hC hD k).preimage haux
  change ((originalMainReserveExperimentLaw Q rate).restrict
    (originalTargetReserveExperimentSplice ⁻¹' {p | (originalReserveSceneExcessClassKept R 1 0 C D
      (originalReserveExcessInputAux p)).card = k})).map
        (originalReserveExcessClassInputReadout R 1 0 C D k ∘ originalTargetReserveExperimentSplice) = _
  rw [← Measure.map_map (measurable_originalReserveExcessClassInputReadout R 1 0 hC hD k) hsplice,
    ← Measure.restrict_map hsplice hE, map_originalTargetReserveExperimentSplice]
  exact map_originalReserveSceneExcessClassSelection_actual_jointLaw _ β rate R 1 0 hC hD k

end OTSelector.Reconstruction
