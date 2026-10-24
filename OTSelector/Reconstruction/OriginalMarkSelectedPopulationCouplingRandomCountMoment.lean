import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingCountMomentPoisson
import OTSelector.Reconstruction.OriginalReserveSelectedSpatialLawJoinedClassExperiment

/-! True fractional moments of the same experiment's actual classwise kept counts. -/

open MeasureTheory Set Function
open OTSelector.Probability
open scoped NNReal

noncomputable section
namespace OTSelector.Reconstruction
variable {q : ℕ}

/-- The literal retained original class count in a view of the joined experiment. -/
def originalReserveExcessClassCount (R : ℝ) (own other : Fin 2) (C D : Set ℝ)
    (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) × MarkedCloudSpace q ℝ) : ℕ :=
  (originalReserveSceneExcessClassKept R own other C D (originalReserveExcessInputAux p)).card

theorem measurable_originalReserveExcessClassCount (R : ℝ) (own other : Fin 2)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Measurable (originalReserveExcessClassCount (q := q) R own other C D) := by
  have ha : Measurable (originalReserveExcessInputAux (q := q)) := by
    unfold originalReserveExcessInputAux
    fun_prop
  exact ((measurable_of_countable (fun s : Finset ℕ ↦ s.card)).comp
    (measurable_originalReserveSceneExcessClassKept R own other hC hD)).comp ha

/-- Deleting and selecting original reserve indices can only decrease the observed count. -/
theorem originalReserveExcessClassCount_le_originalCount (R : ℝ) (own other : Fin 2)
    (C D : Set ℝ) (p : (LegalMarkedOptimalInputScene q × MarkedCloudSpace q ℝ) ×
      MarkedCloudSpace q ℝ) : originalReserveExcessClassCount R own other C D p ≤ p.2.1 := by
  classical
  unfold originalReserveExcessClassCount originalReserveSceneExcessClassKept
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    ((Finset.card_le_card Finset.sdiff_subset).trans_eq (Finset.card_range _))

variable {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- Actual source retained-class fractional moments are controlled by the true
source reserve intensity under the unchanged joined experiment. -/
theorem LegalWeightedStationaryPoissonMatching.original_sourceReserveClass_count_rpow
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0) (R : ℝ)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    let K := originalReserveExcessClassCount (q := q) R 0 1 C D ∘ originalSourceReserveExperimentSplice
    Integrable (fun p ↦ (K p : ℝ) ^ r) (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, (K p : ℝ) ^ r ∂originalMainReserveExperimentLaw Q rate) ≤ (rate : ℝ) ^ r := by
  let M := originalMainReserveExperimentLaw Q rate
  let K := originalReserveExcessClassCount (q := q) R 0 1 C D ∘ originalSourceReserveExperimentSplice
  have hK : Measurable K := (measurable_originalReserveExcessClassCount R 0 1 hC hD).comp
    (by unfold originalSourceReserveExperimentSplice; fun_prop)
  have h := markedPoisson_count_rpow_integrable_and_integral_le q α rate hr₀ hr₁
  have hI : Integrable (fun p ↦ (p.2.1.1 : ℝ) ^ r) M := h.1.comp_fst _ |>.comp_snd _
  have hb (p) : (K p : ℝ) ^ r ≤ (p.2.1.1 : ℝ) ^ r :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by
      exact_mod_cast (originalReserveExcessClassCount_le_originalCount R 0 1 C D
        (originalSourceReserveExperimentSplice p))) hr₀.le
  have hm : Measurable (fun p ↦ (K p : ℝ) ^ r) :=
    (Real.continuous_rpow_const hr₀.le).measurable.comp (measurable_from_nat.comp hK)
  have hKI := hI.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact hb p)
  refine ⟨hKI, (integral_mono hKI hI hb).trans ?_⟩
  have hp : MeasurePreserving (fun p : LegalMarkedOptimalInputScene q ×
      TwoMarkedCloudSpace q ℝ ℝ ↦ p.2.1) M (markedPoissonLaw q ℝ α rate) :=
    measurePreserving_fst.comp measurePreserving_snd
  have hmapI := h.1.aestronglyMeasurable
  rw [← hp.map_eq] at hmapI
  have heq := integral_map hp.measurable.aemeasurable hmapI
  rw [hp.map_eq] at heq
  exact heq ▸ h.2

/-- The target uses the same scene and two reserves, with its own true intensity. -/
theorem LegalWeightedStationaryPoissonMatching.original_targetReserveClass_count_rpow
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0) (R : ℝ)
    {C D : Set ℝ} (hC : MeasurableSet C) (hD : MeasurableSet D)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    let K := originalReserveExcessClassCount (q := q) R 1 0 C D ∘ originalTargetReserveExperimentSplice
    Integrable (fun p ↦ (K p : ℝ) ^ r) (originalMainReserveExperimentLaw Q rate) ∧
      (∫ p, (K p : ℝ) ^ r ∂originalMainReserveExperimentLaw Q rate) ≤ (rate : ℝ) ^ r := by
  let M := originalMainReserveExperimentLaw Q rate
  let K := originalReserveExcessClassCount (q := q) R 1 0 C D ∘ originalTargetReserveExperimentSplice
  have hK : Measurable K := (measurable_originalReserveExcessClassCount R 1 0 hC hD).comp
    (by unfold originalTargetReserveExperimentSplice; fun_prop)
  have h := markedPoisson_count_rpow_integrable_and_integral_le q β rate hr₀ hr₁
  have hI : Integrable (fun p ↦ (p.2.2.1 : ℝ) ^ r) M := h.1.comp_snd _ |>.comp_snd _
  have hb (p) : (K p : ℝ) ^ r ≤ (p.2.2.1 : ℝ) ^ r :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by
      exact_mod_cast (originalReserveExcessClassCount_le_originalCount R 1 0 C D
        (originalTargetReserveExperimentSplice p))) hr₀.le
  have hm : Measurable (fun p ↦ (K p : ℝ) ^ r) :=
    (Real.continuous_rpow_const hr₀.le).measurable.comp (measurable_from_nat.comp hK)
  have hKI := hI.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact hb p)
  refine ⟨hKI, (integral_mono hKI hI hb).trans ?_⟩
  have hp : MeasurePreserving (fun p : LegalMarkedOptimalInputScene q ×
      TwoMarkedCloudSpace q ℝ ℝ ↦ p.2.2) M (markedPoissonLaw q ℝ β rate) :=
    measurePreserving_snd.comp measurePreserving_snd
  have hmapI := h.1.aestronglyMeasurable
  rw [← hp.map_eq] at hmapI
  have heq := integral_map hp.measurable.aemeasurable hmapI
  rw [hp.map_eq] at heq
  exact heq ▸ h.2

end OTSelector.Reconstruction
