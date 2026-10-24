import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneNormalized
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonDefect
import OTSelector.Probability.PoissonPrefixMoments
import Mathlib.Analysis.Real.Sqrt

/-!
# Actual finite optimal scalar marginals and original missing endpoints

The same selected matching's unused rows and columns provide exact missing
measures. The original empirical inputs dominate its marginals, and bounded
clock readout errors are paid by the actual original legal matching defects.
Only scalar marginals are identified here.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

private theorem matching_row_sum_add_free {m n : ℕ} {A : Type*} [AddCommMonoid A]
    (σ : OTSelector.PartialMatching m n) (f : Fin m → A) :
    (∑ e ∈ σ.edges, f e.1) + (∑ i ∈ σ.freeRows, f i) = ∑ i, f i := by
  classical
  have hs : (∑ i ∈ σ.rows, f i) = ∑ e ∈ σ.edges, f e.1 := by
    unfold OTSelector.PartialMatching.rows
    rw [Finset.sum_image]
    exact fun e he e' he' h ↦ σ.row_inj e he e' he' h
  have h := Finset.sum_sdiff (Finset.subset_univ σ.rows) (f := f)
  change (∑ i ∈ σ.freeRows, f i) + (∑ i ∈ σ.rows, f i) = ∑ i, f i at h
  rw [hs] at h
  simpa only [add_comm] using h

private theorem matching_col_sum_add_free {m n : ℕ} {A : Type*} [AddCommMonoid A]
    (σ : OTSelector.PartialMatching m n) (f : Fin n → A) :
    (∑ e ∈ σ.edges, f e.2) + (∑ j ∈ σ.freeCols, f j) = ∑ j, f j := by
  classical
  have hs : (∑ j ∈ σ.cols, f j) = ∑ e ∈ σ.edges, f e.2 := by
    unfold OTSelector.PartialMatching.cols
    rw [Finset.sum_image]
    exact fun e he e' he' h ↦ σ.col_inj e he e' he' h
  have h := Finset.sum_sdiff (Finset.subset_univ σ.cols) (f := f)
  change (∑ j ∈ σ.freeCols, f j) + (∑ j ∈ σ.cols, f j) = ∑ j, f j at h
  rw [hs] at h
  simpa only [add_comm] using h

private theorem abs_matching_row_sum_sub_full_le {m n : ℕ}
    (σ : OTSelector.PartialMatching m n) {f : Fin m → ℝ} {G : ℝ}
    (hf : ∀ i, |f i| ≤ G) :
    |(∑ e ∈ σ.edges, f e.1) - ∑ i, f i| ≤ (σ.freeRows.card : ℝ) * G := by
  have hs := matching_row_sum_add_free σ f
  have heq : (∑ e ∈ σ.edges, f e.1) - ∑ i, f i = -(∑ i ∈ σ.freeRows, f i) := by
    linarith
  rw [heq, abs_neg]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun i hi ↦ hf i)).trans_eq (by simp))

private theorem abs_matching_col_sum_sub_full_le {m n : ℕ}
    (σ : OTSelector.PartialMatching m n) {f : Fin n → ℝ} {G : ℝ}
    (hf : ∀ j, |f j| ≤ G) :
    |(∑ e ∈ σ.edges, f e.2) - ∑ j, f j| ≤ (σ.freeCols.card : ℝ) * G := by
  have hs := matching_col_sum_add_free σ f
  have heq : (∑ e ∈ σ.edges, f e.2) - ∑ j, f j = -(∑ j ∈ σ.freeCols, f j) := by
    linarith
  rw [heq, abs_neg]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun j hj ↦ hf j)).trans_eq (by simp))

/-- The complete original raw source empirical measure in physical scale. -/
def legalMarkedSourceEmpiricalMeasure (q : ℕ) (L : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    Measure (LegalMarkedPhysicalPoint q) :=
  ∑ i : Fin (mSourceCount ω), Measure.dirac (legalMarkedPhysicalEdge q L ω i 0).1

/-- The complete original raw target empirical measure in physical scale. -/
def legalMarkedTargetEmpiricalMeasure (q : ℕ) (L : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    Measure (LegalMarkedPhysicalPoint q) :=
  ∑ j : Fin (mTargetCount ω), Measure.dirac (legalMarkedPhysicalEdge q L ω 0 j).2

/-- The actual unused source endpoints of the same exact signed optimum. -/
def legalMarkedMissingSourceMeasure (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Measure (LegalMarkedPhysicalPoint q) :=
  ∑ i ∈ (firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
      id id r kin g t ω).freeRows, Measure.dirac (legalMarkedPhysicalEdge q L ω i 0).1

/-- The actual unused target endpoints of the same exact signed optimum. -/
def legalMarkedMissingTargetMeasure (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : Measure (LegalMarkedPhysicalPoint q) :=
  ∑ j ∈ (firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
      id id r kin g t ω).freeCols, Measure.dirac (legalMarkedPhysicalEdge q L ω 0 j).2

/-- Matched and unused source endpoints partition the exact original raw
empirical input as actual measures, even when physical atoms coincide. -/
theorem legalMarkedOptimalPlan_source_add_missing (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (legalMarkedOptimalPlan q L r kin g t ω).map Prod.fst +
      legalMarkedMissingSourceMeasure q L r kin g t ω =
        legalMarkedSourceEmpiricalMeasure q L ω := by
  classical
  unfold legalMarkedOptimalPlan legalMarkedFixedOptimalPlan
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  simp only [Measure.map_dirac]
  exact matching_row_sum_add_free
    (firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω) id id r kin g t ω)
    (fun i ↦ Measure.dirac (legalMarkedPhysicalEdge q L ω i 0).1)

/-- Matched and unused target endpoints partition the exact original raw
target empirical input as actual measures. -/
theorem legalMarkedOptimalPlan_target_add_missing (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (legalMarkedOptimalPlan q L r kin g t ω).map Prod.snd +
      legalMarkedMissingTargetMeasure q L r kin g t ω =
        legalMarkedTargetEmpiricalMeasure q L ω := by
  classical
  unfold legalMarkedOptimalPlan legalMarkedFixedOptimalPlan
  rw [Measure.map_finset_sum measurable_snd.aemeasurable]
  simp only [Measure.map_dirac]
  exact matching_col_sum_add_free
    (firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω) id id r kin g t ω)
    (fun j ↦ Measure.dirac (legalMarkedPhysicalEdge q L ω 0 j).2)

/-- Both actual normalized plan marginals are dominated by their complete
original normalized raw empirical inputs. -/
theorem legalMarkedNormalizedOptimalPlan_marginals_le_empirical
    (q : ℕ) (L : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (legalMarkedNormalizedOptimalPlan q L kin g t ω).map Prod.fst ≤
      (ENNReal.ofReal (L ^ q))⁻¹ • legalMarkedSourceEmpiricalMeasure q L ω ∧
    (legalMarkedNormalizedOptimalPlan q L kin g t ω).map Prod.snd ≤
      (ENNReal.ofReal (L ^ q))⁻¹ • legalMarkedTargetEmpiricalMeasure q L ω := by
  have hs := legalMarkedOptimalPlan_source_add_missing q L (L ^ q) kin g t ω
  have ht := legalMarkedOptimalPlan_target_add_missing q L (L ^ q) kin g t ω
  constructor
  · rw [legalMarkedNormalizedOptimalPlan, Measure.map_smul, ← hs, smul_add]
    exact le_add_of_nonneg_right bot_le
  · rw [legalMarkedNormalizedOptimalPlan, Measure.map_smul, ← ht, smul_add]
    exact le_add_of_nonneg_right bot_le

/-- The missing source mass is exactly the original unmatched source count. -/
theorem legalMarkedMissingSourceMeasure_univ (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedMissingSourceMeasure q L r kin g t ω univ =
      (mSourceCount ω - legalMarkedMaximumCard q id id ω : ℕ) := by
  classical
  have hc := (firstLegalMarkedOptimalMatching_isLegalOptimal
    q (mSourceCount ω) (mTargetCount ω) id id r kin g t ω).2.1
  change _ = ((mSourceCount ω - PartialMatching.legalMaximumCard
    (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℕ) : ℝ≥0∞)
  rw [← hc]
  simp [legalMarkedMissingSourceMeasure, Measure.finsetSum_apply,
    OTSelector.PartialMatching.card_freeRows]

/-- The missing target mass is exactly the original unmatched target count. -/
theorem legalMarkedMissingTargetMeasure_univ (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedMissingTargetMeasure q L r kin g t ω univ =
      (mTargetCount ω - legalMarkedMaximumCard q id id ω : ℕ) := by
  classical
  have hc := (firstLegalMarkedOptimalMatching_isLegalOptimal
    q (mSourceCount ω) (mTargetCount ω) id id r kin g t ω).2.1
  change _ = ((mTargetCount ω - PartialMatching.legalMaximumCard
    (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω) : ℕ) : ℝ≥0∞)
  rw [← hc]
  simp [legalMarkedMissingTargetMeasure, Measure.finsetSum_apply,
    OTSelector.PartialMatching.card_freeCols]

/-- The actual original target-only legal defect, in real count units. -/
def legalMarkedOptimalTargetDefect (q : ℕ) (ω : TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  (mTargetCount ω : ℝ) - legalMarkedMaximumCard q id id ω

/-- The bounded scalar source-clock error is paid by the actual original
unmatched source count per original physical volume. -/
theorem abs_legalMarkedNormalizedOptimalPlan_sourceClock_error_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) {h : ℝ → ℝ} {G : ℝ} (hh : ∀ a, |h a| ≤ G) :
    |(∫ e, h e.1.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) -
        (L ^ q)⁻¹ * ∑ i : Fin (mSourceCount ω), h (mSourceMark ω i)| ≤
      G * legalMarkedSourceDefect q id id ω / L ^ q := by
  classical
  let σ := firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
    id id (L ^ q) kin g t ω
  have hc := (firstLegalMarkedOptimalMatching_isLegalOptimal
    q (mSourceCount ω) (mTargetCount ω) id id (L ^ q) kin g t ω).2.1
  have hfree : (σ.freeRows.card : ℝ) = legalMarkedSourceDefect q id id ω := by
    rw [σ.card_freeRows, Nat.cast_sub (σ.card_le.trans (min_le_left _ _))]
    change (mSourceCount ω : ℝ) - σ.card =
      (mSourceCount ω : ℝ) - PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω)
    rw [hc]
  rw [integral_legalMarkedNormalizedOptimalPlan q hL.le]
  unfold legalMarkedOptimalPlan
  rw [integral_legalMarkedFixedOptimalPlan, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hL q))]
  change (L ^ q)⁻¹ * |(∑ e ∈ σ.edges, h (mSourceMark ω e.1)) -
    ∑ i : Fin (mSourceCount ω), h (mSourceMark ω i)| ≤ _
  exact (mul_le_mul_of_nonneg_left
    (abs_matching_row_sum_sub_full_le σ (fun i ↦ hh (mSourceMark ω i)))
    (inv_nonneg.mpr (pow_pos hL q).le)).trans_eq (by rw [hfree]; ring)

/-- The bounded scalar target-clock error is paid by the actual original
unmatched target count per original physical volume. -/
theorem abs_legalMarkedNormalizedOptimalPlan_targetClock_error_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) {h : ℝ → ℝ} {G : ℝ} (hh : ∀ a, |h a| ≤ G) :
    |(∫ e, h e.2.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) -
        (L ^ q)⁻¹ * ∑ j : Fin (mTargetCount ω), h (mTargetMark ω j)| ≤
      G * legalMarkedOptimalTargetDefect q ω / L ^ q := by
  classical
  let σ := firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
    id id (L ^ q) kin g t ω
  have hc := (firstLegalMarkedOptimalMatching_isLegalOptimal
    q (mSourceCount ω) (mTargetCount ω) id id (L ^ q) kin g t ω).2.1
  have hfree : (σ.freeCols.card : ℝ) = legalMarkedOptimalTargetDefect q ω := by
    rw [σ.card_freeCols, Nat.cast_sub (σ.card_le.trans (min_le_right _ _))]
    change (mTargetCount ω : ℝ) - σ.card =
      (mTargetCount ω : ℝ) - PartialMatching.legalMaximumCard
        (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) id id ω)
    rw [hc]
  rw [integral_legalMarkedNormalizedOptimalPlan q hL.le]
  unfold legalMarkedOptimalPlan
  rw [integral_legalMarkedFixedOptimalPlan, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hL q))]
  change (L ^ q)⁻¹ * |(∑ e ∈ σ.edges, h (mTargetMark ω e.2)) -
    ∑ j : Fin (mTargetCount ω), h (mTargetMark ω j)| ≤ _
  exact (mul_le_mul_of_nonneg_left
    (abs_matching_col_sum_sub_full_le σ (fun j ↦ hh (mTargetMark ω j)))
    (inv_nonneg.mpr (pow_pos hL q).le)).trans_eq (by rw [hfree]; ring)

/-- The scalar readout of every original used source mark. -/
def legalMarkedOriginalSourceClockSum (q : ℕ) (h : ℝ → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  ∑ i : Fin (mSourceCount ω), h (mSourceMark ω i)

/-- The scalar readout of every original used target mark. -/
def legalMarkedOriginalTargetClockSum (q : ℕ) (h : ℝ → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  ∑ j : Fin (mTargetCount ω), h (mTargetMark ω j)

private theorem integral_comp_fst_probability {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [IsProbabilityMeasure ν]
    {f : A → ℝ} (hf : Measurable f) :
    (∫ p, f p.1 ∂μ.prod ν) = ∫ a, f a ∂μ := by
  have h := integral_map_of_stronglyMeasurable (μ := μ.prod ν) measurable_fst
    hf.stronglyMeasurable
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h.symm

private theorem integral_comp_snd_probability {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [SFinite ν]
    {f : B → ℝ} (hf : Measurable f) :
    (∫ p, f p.2 ∂μ.prod ν) = ∫ b, f b ∂ν := by
  have h := integral_map_of_stronglyMeasurable (μ := μ.prod ν) measurable_snd
    hf.stronglyMeasurable
  rw [Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h.symm

private theorem originalMarkedClockSum_integrability_and_mean
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] (r : ℝ≥0)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G) :
    Integrable (poissonPrefixSum (fun p : (Fin q → ℝ) × ℝ ↦ h p.2))
      (markedPoissonLaw q ℝ α r) ∧
    (∫ z, poissonPrefixSum (fun p : (Fin q → ℝ) × ℝ ↦ h p.2) z
      ∂markedPoissonLaw q ℝ α r) = (r : ℝ) * ∫ a, h a ∂α := by
  have hcube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  have hi := integrable_poissonPrefixSum ((cubeMeasure (Fin q) 1).prod α) r
    (f := fun p : (Fin q → ℝ) × ℝ ↦ h p.2) (hh.comp measurable_snd) (fun p ↦ hbound p.2)
  have he := integral_poissonPrefixSum ((cubeMeasure (Fin q) 1).prod α) r
    (f := fun p : (Fin q → ℝ) × ℝ ↦ h p.2) (hh.comp measurable_snd) (fun p ↦ hbound p.2)
  rw [integral_comp_snd_probability (cubeMeasure (Fin q) 1) α hh] at he
  exact ⟨by simpa only [markedPoissonLaw, markedSeqLaw] using hi,
    by simpa only [markedPoissonLaw, markedSeqLaw] using he⟩

/-- The original Poisson source mark sum has exactly its original intensity
times its original scalar population mean. -/
theorem legalMarkedOriginalSourceClockSum_integrability_and_mean
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (r : ℝ≥0)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G) :
    Integrable (legalMarkedOriginalSourceClockSum q h) (twoMarkedCloudLaw q ℝ ℝ α β r) ∧
    (∫ ω, legalMarkedOriginalSourceClockSum q h ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) =
      (r : ℝ) * ∫ a, h a ∂α := by
  obtain ⟨hi, he⟩ := originalMarkedClockSum_integrability_and_mean q α r hh hbound
  constructor
  · exact hi.comp_fst (markedPoissonLaw q ℝ β r)
  · change (∫ ω, poissonPrefixSum (fun p : (Fin q → ℝ) × ℝ ↦ h p.2) ω.1
      ∂(markedPoissonLaw q ℝ α r).prod (markedPoissonLaw q ℝ β r)) = _
    rw [integral_comp_fst_probability (markedPoissonLaw q ℝ α r)
      (markedPoissonLaw q ℝ β r)
      (f := poissonPrefixSum (fun p : (Fin q → ℝ) × ℝ ↦ h p.2))
      (measurable_poissonPrefixSum (hh.comp measurable_snd))]
    exact he

/-- The original Poisson target mark sum has exactly its original intensity
times its original scalar population mean. -/
theorem legalMarkedOriginalTargetClockSum_integrability_and_mean
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (r : ℝ≥0)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G) :
    Integrable (legalMarkedOriginalTargetClockSum q h) (twoMarkedCloudLaw q ℝ ℝ α β r) ∧
    (∫ ω, legalMarkedOriginalTargetClockSum q h ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) =
      (r : ℝ) * ∫ a, h a ∂β := by
  obtain ⟨hi, he⟩ := originalMarkedClockSum_integrability_and_mean q β r hh hbound
  constructor
  · exact hi.comp_snd (markedPoissonLaw q ℝ α r)
  · change (∫ ω, poissonPrefixSum (fun p : (Fin q → ℝ) × ℝ ↦ h p.2) ω.2
      ∂(markedPoissonLaw q ℝ α r).prod (markedPoissonLaw q ℝ β r)) = _
    rw [integral_comp_snd_probability (markedPoissonLaw q ℝ α r)
      (markedPoissonLaw q ℝ β r)
      (f := poissonPrefixSum (fun p : (Fin q → ℝ) × ℝ ↦ h p.2))
      (measurable_poissonPrefixSum (hh.comp measurable_snd))]
    exact he

theorem integrable_legalMarkedOptimalTargetDefect (q : ℕ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (r : ℝ≥0) :
    Integrable (legalMarkedOptimalTargetDefect q) (twoMarkedCloudLaw q ℝ ℝ α β r) := by
  have heq : legalMarkedOptimalTargetDefect q = fun ω ↦
      legalMarkedSourceDefect q id id ω + (mTargetCount ω : ℝ) - (mSourceCount ω : ℝ) := by
    funext ω
    simp only [legalMarkedOptimalTargetDefect, legalMarkedSourceDefect]
    ring
  rw [heq]
  exact ((integrable_legalMarkedSourceDefect q measurable_id measurable_id α β r).add
    (integrable_mTargetCount q α β r)).sub (integrable_mSourceCount q α β r)

/-- Equal original color means make expected source and target missing
counts equal, with no law assigned to the selected endpoints. -/
theorem integral_legalMarkedOptimalTargetDefect_eq_source (q : ℕ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (r : ℝ≥0) :
    (∫ ω, legalMarkedOptimalTargetDefect q ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) =
      ∫ ω, legalMarkedSourceDefect q id id ω ∂twoMarkedCloudLaw q ℝ ℝ α β r := by
  have heq (ω : TwoMarkedCloudSpace q ℝ ℝ) : legalMarkedOptimalTargetDefect q ω =
      legalMarkedSourceDefect q id id ω + (mTargetCount ω : ℝ) - (mSourceCount ω : ℝ) := by
    simp only [legalMarkedOptimalTargetDefect, legalMarkedSourceDefect]
    ring
  simp_rw [heq]
  rw [integral_sub
    (f := fun ω ↦ legalMarkedSourceDefect q id id ω + (mTargetCount ω : ℝ))
    (g := fun ω ↦ (mSourceCount ω : ℝ))
    ((integrable_legalMarkedSourceDefect q measurable_id measurable_id α β r).add
      (integrable_mTargetCount q α β r)) (integrable_mSourceCount q α β r),
    integral_add (f := fun ω ↦ legalMarkedSourceDefect q id id ω)
      (g := fun ω ↦ (mTargetCount ω : ℝ))
      (integrable_legalMarkedSourceDefect q measurable_id measurable_id α β r)
      (integrable_mTargetCount q α β r), integral_mTargetCount_eq, integral_mSourceCount_eq]
  ring

private theorem integrable_and_abs_integral_sub_mean_le_of_defect
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f I D : Ω → ℝ} (hf : StronglyMeasurable f)
    (hI : Integrable I P) (hD : Integrable D P) {μ c : ℝ}
    (hmean : (∫ ω, I ω ∂P) = μ) (hbound : ∀ ω, |f ω - I ω| ≤ c * D ω) :
    Integrable f P ∧ |(∫ ω, f ω ∂P) - μ| ≤ c * ∫ ω, D ω ∂P := by
  have hfi : Integrable f P := (hI.abs.add (hD.const_mul c)).mono'
    hf.aestronglyMeasurable (.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs]
      change |f ω| ≤ |I ω| + c * D ω
      have htri : |f ω| ≤ |f ω - I ω| + |I ω| := by
        simpa only [sub_add_cancel] using abs_add_le (f ω - I ω) (I ω)
      linarith [hbound ω]))
  refine ⟨hfi, ?_⟩
  calc
    _ = |∫ ω, f ω - I ω ∂P| := by rw [integral_sub hfi hI, hmean]
    _ ≤ ∫ ω, |f ω - I ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, c * D ω ∂P :=
      integral_mono (hfi.sub hI).abs (hD.const_mul c) hbound
    _ = _ := integral_const_mul _ _

/-- Expected original normalized source-clock readouts differ from the
original scalar population only through the actual original source defect. -/
theorem integral_legalMarkedNormalizedOptimalPlan_sourceClock_error_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G) :
    Integrable (fun ω ↦ ∫ e, h e.1.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ∧
    |(∫ ω, ∫ e, h e.1.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) - ∫ a, h a ∂α| ≤
      G * (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q := by
  let P := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))
  let K : Kernel (TwoMarkedCloudSpace q ℝ ℝ) (LegalMarkedPhysicalEdge q) :=
    ⟨legalMarkedNormalizedOptimalPlan q L kin g t,
      measurable_legalMarkedNormalizedOptimalPlan q L hkin hg t⟩
  have hf : StronglyMeasurable
      (fun ω ↦ ∫ e, h e.1.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    (hh.comp measurable_fst.snd).stronglyMeasurable.integral_kernel (κ := K)
  have hsum := legalMarkedOriginalSourceClockSum_integrability_and_mean
    q α β (Real.toNNReal (L ^ q)) hh hbound
  have hV : 0 < L ^ q := pow_pos hL q
  have hmean : (∫ ω, (L ^ q)⁻¹ * legalMarkedOriginalSourceClockSum q h ω ∂P) =
      ∫ a, h a ∂α := by
    rw [integral_const_mul, hsum.2, Real.coe_toNNReal _ hV.le]
    field_simp
  have hd : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      |(∫ e, h e.1.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) -
        (L ^ q)⁻¹ * legalMarkedOriginalSourceClockSum q h ω| ≤
          (G / L ^ q) * legalMarkedSourceDefect q id id ω := by
    intro ω
    exact (abs_legalMarkedNormalizedOptimalPlan_sourceClock_error_le
      q hL kin g t ω hbound).trans_eq (by ring)
  obtain ⟨hi, he⟩ := integrable_and_abs_integral_sub_mean_le_of_defect P hf
    (hsum.1.const_mul (L ^ q)⁻¹)
    (integrable_legalMarkedSourceDefect q measurable_id measurable_id α β _) hmean hd
  exact ⟨hi, he.trans_eq (by ring)⟩

/-- Expected original normalized target-clock readouts have the same original
source-defect budget, since the original Poisson color means are equal. -/
theorem integral_legalMarkedNormalizedOptimalPlan_targetClock_error_le
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G) :
    Integrable (fun ω ↦ ∫ e, h e.2.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) ∧
    |(∫ ω, ∫ e, h e.2.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) - ∫ a, h a ∂β| ≤
      G * (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q := by
  let P := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))
  let K : Kernel (TwoMarkedCloudSpace q ℝ ℝ) (LegalMarkedPhysicalEdge q) :=
    ⟨legalMarkedNormalizedOptimalPlan q L kin g t,
      measurable_legalMarkedNormalizedOptimalPlan q L hkin hg t⟩
  have hf : StronglyMeasurable
      (fun ω ↦ ∫ e, h e.2.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    (hh.comp measurable_snd.snd).stronglyMeasurable.integral_kernel (κ := K)
  have hsum := legalMarkedOriginalTargetClockSum_integrability_and_mean
    q α β (Real.toNNReal (L ^ q)) hh hbound
  have hV : 0 < L ^ q := pow_pos hL q
  have hmean : (∫ ω, (L ^ q)⁻¹ * legalMarkedOriginalTargetClockSum q h ω ∂P) =
      ∫ a, h a ∂β := by
    rw [integral_const_mul, hsum.2, Real.coe_toNNReal _ hV.le]
    field_simp
  have hd : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      |(∫ e, h e.2.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω) -
        (L ^ q)⁻¹ * legalMarkedOriginalTargetClockSum q h ω| ≤
          (G / L ^ q) * legalMarkedOptimalTargetDefect q ω := by
    intro ω
    exact (abs_legalMarkedNormalizedOptimalPlan_targetClock_error_le
      q hL kin g t ω hbound).trans_eq (by ring)
  obtain ⟨hi, he⟩ := integrable_and_abs_integral_sub_mean_le_of_defect P hf
    (hsum.1.const_mul (L ^ q)⁻¹)
    (integrable_legalMarkedOptimalTargetDefect q α β _) hmean hd
  rw [integral_legalMarkedOptimalTargetDefect_eq_source] at he
  exact ⟨hi, he.trans_eq (by ring)⟩

private theorem tendsto_of_abs_sub_le_vanishing_defect
    {f D : ℝ → ℝ} {μ G : ℝ} (hD : Tendsto D atTop (𝓝 0))
    (hb : ∀ L : ℝ, 0 < L → |f L - μ| ≤ G * D L) : Tendsto f atTop (𝓝 μ) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun L ↦ G * D L) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hD
  exact squeeze_zero' (.of_forall (fun L ↦ norm_nonneg (f L - μ)))
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      simpa only [Real.norm_eq_abs] using hb L hL) hlim

/-- Vanishing actual original source-defect density identifies both expected
normalized scalar-clock marginals with their original populations. -/
theorem tendsto_legalMarkedNormalizedOptimalPlan_clock_readouts_of_sourceDefect
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G)
    (hdef : Tendsto (fun L : ℝ ↦
      (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q) atTop (𝓝 0)) :
    Tendsto (fun L : ℝ ↦ ∫ ω, ∫ e, h e.1.2
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) atTop (𝓝 (∫ a, h a ∂α)) ∧
    Tendsto (fun L : ℝ ↦ ∫ ω, ∫ e, h e.2.2
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) atTop (𝓝 (∫ a, h a ∂β)) := by
  constructor
  · apply tendsto_of_abs_sub_le_vanishing_defect hdef
    intro L hL
    exact (integral_legalMarkedNormalizedOptimalPlan_sourceClock_error_le
      q hL α β hkin hg t hh hbound).2.trans_eq (by ring)
  · apply tendsto_of_abs_sub_le_vanishing_defect hdef
    intro L hL
    exact (integral_legalMarkedNormalizedOptimalPlan_targetClock_error_le
      q hL α β hkin hg t hh hbound).2.trans_eq (by ring)

/-- The existing original scalar-bin coupling construction supplies an
explicit square-root error bound for both actual expected clock marginals.
No law for the adaptively selected endpoint clouds is introduced. -/
theorem scalarBins_integral_legalMarkedNormalizedOptimalPlan_clock_errors_le
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ p.2 - p.1)
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G) :
    let error := G * Real.sqrt
      (2 * L ^ q * Fintype.card (Option (Unit × Fin D.count × Fin D.count))) / L ^ q
    (|(∫ ω, ∫ e, h e.1.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) - ∫ a, h a ∂α| ≤ error) ∧
    (|(∫ ω, ∫ e, h e.2.2 ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) - ∫ a, h a ∂β| ≤ error) := by
  let tagMeasurable : MeasurableSpace (Option (Unit × Fin D.count × Fin D.count)) := ⊤
  let tagSingleton : MeasurableSingletonClass (Option (Unit × Fin D.count × Fin D.count)) :=
    ⟨fun _ ↦ trivial⟩
  have hG : 0 ≤ G := (abs_nonneg (h 0)).trans (hbound 0)
  have hV : 0 < L ^ q := pow_pos hL q
  have hd := (scalarBinPopulationTypes_poisson_sourceDefect D hδ
    (fun _ : ℝ × ℝ ↦ ()) id id π α β hπ measurable_const measurable_id measurable_id
      hI hgap q (Real.toNNReal (L ^ q))).2
  rw [Real.coe_toNNReal _ hV.le] at hd
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd hG) hV.le
  exact ⟨(integral_legalMarkedNormalizedOptimalPlan_sourceClock_error_le
      q hL α β hkin hg t hh hbound).2.trans hb,
    (integral_legalMarkedNormalizedOptimalPlan_targetClock_error_le
      q hL α β hkin hg t hh hbound).2.trans hb⟩

private theorem tendsto_sqrt_volume_ratio_zero (q : ℕ) (hq : 0 < q) {K : ℝ} (hK : 0 ≤ K) :
    Tendsto (fun L : ℝ ↦ Real.sqrt (2 * L ^ q * K) / L ^ q) atTop (𝓝 0) := by
  have hvol : Tendsto (fun L : ℝ ↦ L ^ q) atTop atTop := tendsto_pow_atTop hq.ne'
  have hsqrt : Tendsto (fun L : ℝ ↦ Real.sqrt (L ^ q)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hvol
  have hlim : Tendsto (fun L : ℝ ↦ Real.sqrt (2 * K) / Real.sqrt (L ^ q)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hV : 0 < L ^ q := pow_pos hL q
  have hs0 : Real.sqrt (L ^ q) ≠ 0 := (Real.sqrt_pos.mpr hV).ne'
  have hmul : 2 * L ^ q * K = (2 * K) * L ^ q := by ring
  symm
  rw [hmul, Real.sqrt_mul (by positivity : 0 ≤ 2 * K),
    div_eq_div_iff hV.ne' hs0]
  calc
    _ = Real.sqrt (2 * K) * (Real.sqrt (L ^ q) ^ 2) := by ring
    _ = _ := by rw [Real.sq_sqrt hV.le]

/-- Existing actual scalar-bin Poisson deficiency estimates internally give
vanishing source-defect density along all original real physical scales. -/
theorem scalarBins_legalMarkedSourceDefect_div_tendsto_zero
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ p.2 - p.1) (q : ℕ) (hq : 0 < q) :
    Tendsto (fun L : ℝ ↦
      (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q) atTop (𝓝 0) := by
  let tagMeasurable : MeasurableSpace (Option (Unit × Fin D.count × Fin D.count)) := ⊤
  let tagSingleton : MeasurableSingletonClass (Option (Unit × Fin D.count × Fin D.count)) :=
    ⟨fun _ ↦ trivial⟩
  apply squeeze_zero' _ _ (tendsto_sqrt_volume_ratio_zero q hq
    (Nat.cast_nonneg (Fintype.card (Option (Unit × Fin D.count × Fin D.count)))))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    apply div_nonneg _ (pow_pos hL q).le
    apply integral_nonneg
    intro ω
    rw [legalMarkedSourceDefect_eq_nat]
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hV : 0 < L ^ q := pow_pos hL q
    have hd := (scalarBinPopulationTypes_poisson_sourceDefect D hδ
      (fun _ : ℝ × ℝ ↦ ()) id id π α β hπ measurable_const measurable_id measurable_id
        hI hgap q (Real.toNNReal (L ^ q))).2
    rw [Real.coe_toNNReal _ hV.le] at hd
    exact div_le_div_of_nonneg_right hd hV.le

/-- Original finite scalar-bin coupling assumptions produce both limiting
expected scalar-clock marginals of the actual original normalized optimizer.
No stationary input or selected-cloud law is assumed. -/
theorem scalarBins_tendsto_legalMarkedNormalizedOptimalPlan_clock_readouts
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ p.2 - p.1) (q : ℕ) (hq : 0 < q)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : ℝ → ℝ} (hh : Measurable h) {G : ℝ} (hbound : ∀ a, |h a| ≤ G) :
    Tendsto (fun L : ℝ ↦ ∫ ω, ∫ e, h e.1.2
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) atTop (𝓝 (∫ a, h a ∂α)) ∧
    Tendsto (fun L : ℝ ↦ ∫ ω, ∫ e, h e.2.2
      ∂legalMarkedNormalizedOptimalPlan q L kin g t ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) atTop (𝓝 (∫ a, h a ∂β)) :=
  tendsto_legalMarkedNormalizedOptimalPlan_clock_readouts_of_sourceDefect
    q α β hkin hg t hh hbound
      (scalarBins_legalMarkedSourceDefect_div_tendsto_zero D hδ π α β hπ hI hgap q hq)

end OTSelector.Reconstruction
