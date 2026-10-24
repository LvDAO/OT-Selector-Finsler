import OTSelector.Reconstruction.OriginalStageReserveJoinedExperiment

/-! Both actual excess-selected reserve spatial laws come from one original joined experiment. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The original main scene, other reserve, own observed count and all own original marks. -/
def originalReserveExcessInputAux
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    OriginalReserveSceneAux q := (p.1, p.2.1, fun i ↦ (p.2.2 i).2)

/-- Actual original observed positions at the measurable mark-selected original indices. -/
def originalReserveExcessInputReadout (R : ℝ) (own other : Fin 2) (C : Set ℝ) (k : ℕ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    OriginalReserveSceneAux q × (Fin k → (Fin q → ℝ)) :=
  (originalReserveExcessInputAux p, fun j ↦
    (p.2.2 (originalReserveSceneExcessSelection R own other C k (originalReserveExcessInputAux p) j)).1)

/-- The actual selected readout is measurable from the same original observations. -/
theorem measurable_originalReserveExcessInputReadout (R : ℝ) (own other : Fin 2)
    {C : Set ℝ} (hC : MeasurableSet C) (k : ℕ) :
    Measurable (originalReserveExcessInputReadout (q := q) R own other C k) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hpositions : Measurable (fun p :
      (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ ↦
      fun i ↦ (p.2.2 i).1) := by fun_prop
  have heval : Measurable (fun p : ℕ × (ℕ → (Fin q → ℝ)) ↦ p.2 p.1) :=
    measurable_from_prod_countable_right (fun i ↦ measurable_pi_apply i)
  exact haux.prodMk (measurable_pi_lambda _ (fun j ↦ heval.comp
    (((measurable_originalReserveSceneExcessSelection_apply R own other hC k j).comp haux).prodMk hpositions)))

variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- The actual source reserve selected by the actual same-scene full excess has its exact
finite iid spatial law on each actual kept-count fibre of the single joined experiment. -/
theorem LegalWeightedStationaryPoissonMatching.original_sourceReserveExcessSelection_jointLaw
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C) (k : ℕ) :
    ((originalMainReserveExperimentLaw Q rate).restrict
      {p | (originalReserveSceneExcessKept R 0 1 C
        (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p))).card = k}).map
      (originalReserveExcessInputReadout R 0 1 C k ∘ originalSourceReserveExperimentSplice) =
      ((((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ β rate)).prod
        (originalReserveCountMarkLaw α rate)).restrict
          {z | (originalReserveSceneExcessKept R 0 1 C z).card = k}).prod
        (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  have hsplice : Measurable (originalSourceReserveExperimentSplice (q := q)) := by
    unfold originalSourceReserveExperimentSplice
    fun_prop
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hE : MeasurableSet {p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ |
      (originalReserveSceneExcessKept R 0 1 C (originalReserveExcessInputAux p)).card = k} :=
    (measurableSet_originalReserveSceneExcessKept_card (q := q) R 0 1 hC k).preimage haux
  change ((originalMainReserveExperimentLaw Q rate).restrict
    (originalSourceReserveExperimentSplice ⁻¹' {p | (originalReserveSceneExcessKept R 0 1 C
      (originalReserveExcessInputAux p)).card = k})).map
        (originalReserveExcessInputReadout R 0 1 C k ∘ originalSourceReserveExperimentSplice) = _
  rw [← Measure.map_map (measurable_originalReserveExcessInputReadout R 0 1 hC k) hsplice,
    ← Measure.restrict_map hsplice hE, map_originalSourceReserveExperimentSplice]
  exact map_originalReserveSceneExcessSelection_actual_jointLaw _ α rate R 0 1 hC k

/-- The target law is obtained by reordering this same joined experiment, preserving the
same original main scene, both reserve observations and all their original indices. -/
theorem LegalWeightedStationaryPoissonMatching.original_targetReserveExcessSelection_jointLaw
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    (R : ℝ) {C : Set ℝ} (hC : MeasurableSet C) (k : ℕ) :
    ((originalMainReserveExperimentLaw Q rate).restrict
      {p | (originalReserveSceneExcessKept R 1 0 C
        (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p))).card = k}).map
      (originalReserveExcessInputReadout R 1 0 C k ∘ originalTargetReserveExperimentSplice) =
      ((((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ α rate)).prod
        (originalReserveCountMarkLaw β rate)).restrict
          {z | (originalReserveSceneExcessKept R 1 0 C z).card = k}).prod
        (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  have hsplice : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hE : MeasurableSet {p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ |
      (originalReserveSceneExcessKept R 1 0 C (originalReserveExcessInputAux p)).card = k} :=
    (measurableSet_originalReserveSceneExcessKept_card (q := q) R 1 0 hC k).preimage haux
  change ((originalMainReserveExperimentLaw Q rate).restrict
    (originalTargetReserveExperimentSplice ⁻¹' {p | (originalReserveSceneExcessKept R 1 0 C
      (originalReserveExcessInputAux p)).card = k})).map
        (originalReserveExcessInputReadout R 1 0 C k ∘ originalTargetReserveExperimentSplice) = _
  rw [← Measure.map_map (measurable_originalReserveExcessInputReadout R 1 0 hC k) hsplice,
    ← Measure.restrict_map hsplice hE, map_originalTargetReserveExperimentSplice]
  exact map_originalReserveSceneExcessSelection_actual_jointLaw _ β rate R 1 0 hC k

end OTSelector.Reconstruction
