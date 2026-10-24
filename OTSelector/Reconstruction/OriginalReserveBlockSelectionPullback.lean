import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockSelection
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawJoinedExperiment

/-! Exact block-selected spatial laws pull back along the actual sampler marginal. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Read the actual marks-only block selector at unchanged original iid coordinates. -/
def originalReserveBlockInputReadout {q : ℕ} (K : Set (Fin q → ℝ))
    (own other : Fin 2) (S T C : Set ℝ) (k : ℕ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) :
    OriginalReserveSceneAux q × (Fin k → (Fin q → ℝ)) :=
  (originalReserveExcessInputAux p, fun j ↦
    (p.2.2 (originalReserveBlockSelection K own other S T C k (originalReserveExcessInputAux p) j)).1)

/-- Measurability is produced from the actual block counts, marks and original indices. -/
theorem measurable_originalReserveBlockInputReadout {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (own other : Fin 2) {S T C : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (k : ℕ) :
    Measurable (originalReserveBlockInputReadout K own other S T C k) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hpositions : Measurable (fun p :
      (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ ↦
      fun i ↦ (p.2.2 i).1) := by fun_prop
  have heval : Measurable (fun p : ℕ × (ℕ → (Fin q → ℝ)) ↦ p.2 p.1) :=
    measurable_from_prod_countable_right (fun i ↦ measurable_pi_apply i)
  exact haux.prodMk (measurable_pi_lambda _ (fun j ↦ heval.comp
    (((measurable_originalReserveBlockSelection_apply hK own other hS hT hC k j).comp haux).prodMk hpositions)))

/-- The true kept-count event uses no own reserve positions. -/
theorem measurableSet_originalReserveBlockKept_card {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (own other : Fin 2) {S T C : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (k : ℕ) :
    MeasurableSet {z : OriginalReserveSceneAux q | (originalReserveBlockKept K own other S T C z).card = k} :=
  (measurableSet_singleton k).preimage ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
    (measurable_originalReserveBlockKept hK own other hS hT hC))

/-- Reordering a genuine main/two-reserve product retains the exact source marginal. -/
theorem map_originalSourceReserveExperimentSplice_product {q : ℕ}
    (P : Measure (LegalMarkedOptimalInputScene q)) [IsFiniteMeasure P]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0) :
    (P.prod (twoMarkedCloudLaw q ℝ ℝ α β rate)).map originalSourceReserveExperimentSplice =
      (P.prod (markedPoissonLaw q ℝ β rate)).prod (markedPoissonLaw q ℝ α rate) := by
  unfold twoMarkedCloudLaw
  rw [show originalSourceReserveExperimentSplice =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap from rfl,
    ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      (measurable_id.prodMap measurable_swap),
    ← Measure.map_prod_map _ _ measurable_id measurable_swap, Measure.map_id, Measure.prod_swap]
  have h := Measure.prodAssoc_prod (μ := P)
    (ν := markedPoissonLaw q ℝ β rate) (τ := markedPoissonLaw q ℝ α rate)
  conv_lhs => rw [← h]
  rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable MeasurableEquiv.prodAssoc.measurable]
  simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]

/-- The target view reorders the same sampler and does not introduce a new experiment. -/
theorem map_originalTargetReserveExperimentSplice_product {q : ℕ}
    (P : Measure (LegalMarkedOptimalInputScene q)) [IsFiniteMeasure P]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0) :
    (P.prod (twoMarkedCloudLaw q ℝ ℝ α β rate)).map originalTargetReserveExperimentSplice =
      (P.prod (markedPoissonLaw q ℝ α rate)).prod (markedPoissonLaw q ℝ β rate) := by
  have h := Measure.prodAssoc_prod (μ := P)
    (ν := markedPoissonLaw q ℝ α rate) (τ := markedPoissonLaw q ℝ β rate)
  unfold twoMarkedCloudLaw
  have hm : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  rw [← h, Measure.map_map hm MeasurableEquiv.prodAssoc.measurable]
  change Measure.map id ((P.prod (markedPoissonLaw q ℝ α rate)).prod (markedPoissonLaw q ℝ β rate)) = _
  exact Measure.map_id

/-- An established sampler marginal gives the actual block-kept iid law on the
same original experiment, including the zero-count fibre. No joint law of
whole-input or full-array witnesses with own positions is imposed. -/
theorem map_originalReserveBlockSelection_pullback {q : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (J : Measure Ω)
    (P : Measure (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ)) [IsFiniteMeasure P]
    (α : Measure ℝ) [IsProbabilityMeasure α] (rate : ℝ≥0)
    (f : Ω → (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ)
    (hf : Measurable f) (hlaw : J.map f = P.prod (markedPoissonLaw q ℝ α rate))
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (own other : Fin 2)
    {S T C : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (hC : MeasurableSet C) (k : ℕ) :
    (J.restrict {p | (originalReserveBlockKept K own other S T C
      (originalReserveExcessInputAux (f p))).card = k}).map
      (originalReserveBlockInputReadout K own other S T C k ∘ f) =
      ((P.prod (originalReserveCountMarkLaw α rate)).restrict
        {z | (originalReserveBlockKept K own other S T C z).card = k}).prod
          (Measure.pi (fun _ : Fin k ↦ cubeMeasure (Fin q) 1)) := by
  have haux : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  have hE : MeasurableSet {p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ |
      (originalReserveBlockKept K own other S T C (originalReserveExcessInputAux p)).card = k} :=
    (measurableSet_originalReserveBlockKept_card hK own other hS hT hC k).preimage haux
  change (J.restrict (f ⁻¹' {p | (originalReserveBlockKept K own other S T C
    (originalReserveExcessInputAux p)).card = k})).map
      (originalReserveBlockInputReadout K own other S T C k ∘ f) = _
  rw [← Measure.map_map (measurable_originalReserveBlockInputReadout hK own other hS hT hC k) hf,
    ← Measure.restrict_map hf hE, hlaw]
  exact map_originalReserveBlockSelection_actual_jointLaw P α rate hK own other hS hT hC k

end OTSelector.Reconstruction
