import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalSceneMarginalDefect
import OTSelector.Finite.MatchingCellDiscrepancy
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyDyadicComplete
import OTSelector.Probability.CavitySemidiscreteRootedEnergy

/-!
# Actual Haar-rooted spatial test loss from the same unmatched endpoints

The original raw optimal plan, its complete empirical inputs and its exact
unused rows/columns share the same deterministic centering and Haar root.
Local test loss is controlled by the actual missing mass, without assigning
any spatial or independence law to the adaptively selected missing endpoints.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

instance legalMarkedMissingSourceMeasureIsFinite (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    IsFiniteMeasure (legalMarkedMissingSourceMeasure q L r kin g t ω) := by
  unfold legalMarkedMissingSourceMeasure
  infer_instance

instance legalMarkedMissingTargetMeasureIsFinite (q : ℕ) (L r : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    IsFiniteMeasure (legalMarkedMissingTargetMeasure q L r kin g t ω) := by
  unfold legalMarkedMissingTargetMeasure
  infer_instance

/-- The exact original source point in the deterministically centered box,
observed at the same Haar root as its original optimal plan. -/
def legalMarkedRootedSourcePoint (q : ℕ) (L : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (z : Fin q → ℝ) (i : ℕ) : LegalMarkedPhysicalPoint q :=
  (legalMarkedCenteredCoordinate q L (legalMarkedPhysicalEdge q L ω i 0).1 - z,
    mSourceMark ω i)

/-- The exact original target point at that same deterministic center and root. -/
def legalMarkedRootedTargetPoint (q : ℕ) (L : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (z : Fin q → ℝ) (j : ℕ) : LegalMarkedPhysicalPoint q :=
  (legalMarkedCenteredCoordinate q L (legalMarkedPhysicalEdge q L ω 0 j).2 - z,
    mTargetMark ω j)

/-- The actual rooted retained source test, written as its literal original
selected-edge sum. -/
def legalMarkedRootedSourceTest (q : ℕ) (L : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (h : LegalMarkedPhysicalPoint q → ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (z : Fin q → ℝ) : ℝ :=
  ∑ e ∈ (firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
      id id (L ^ q) kin g t ω).edges, h (legalMarkedRootedSourcePoint q L ω z e.1)

def legalMarkedRootedTargetTest (q : ℕ) (L : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (h : LegalMarkedPhysicalPoint q → ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (z : Fin q → ℝ) : ℝ :=
  ∑ e ∈ (firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
      id id (L ^ q) kin g t ω).edges, h (legalMarkedRootedTargetPoint q L ω z e.2)

/-- The complete unchanged original empirical source test at that same root. -/
def legalMarkedRootedSourceInputTest (q : ℕ) (L : ℝ)
    (h : LegalMarkedPhysicalPoint q → ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (z : Fin q → ℝ) : ℝ :=
  ∑ i : Fin (mSourceCount ω), h (legalMarkedRootedSourcePoint q L ω z i)

def legalMarkedRootedTargetInputTest (q : ℕ) (L : ℝ)
    (h : LegalMarkedPhysicalPoint q → ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (z : Fin q → ℝ) : ℝ :=
  ∑ j : Fin (mTargetCount ω), h (legalMarkedRootedTargetPoint q L ω z j)

/-- The retained source sum is exactly the test of the actual original
normalized plan after the existing actual physical rooting operation. -/
theorem integral_actualRooted_legalMarkedNormalizedOptimalPlan_source
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    (∫ e, h e.1 ∂physicalSceneRootedPlan (legalMarkedNormalizedOptimalPlan q L kin g t ω)
      (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) z) =
      legalMarkedRootedSourceTest q L kin g t h ω z := by
  rw [physicalSceneRootedPlan_legalMarkedNormalizedOptimalPlan_centered q hL]
  rw [integral_map_of_stronglyMeasurable
    (f := fun e : LegalMarkedPhysicalEdge q ↦ h e.1)
    (physicalSceneEdgeReroot ((fun _ ↦ L / 2) + z)).continuous.measurable
      (hh.comp measurable_fst).stronglyMeasurable]
  unfold legalMarkedOptimalPlan
  rw [integral_legalMarkedFixedOptimalPlan]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  change ((fun l ↦ L * mSourcePoint ω e.1 l) - ((fun _ ↦ L / 2) + z),
      mSourceMark ω e.1) =
    (((fun l ↦ L * mSourcePoint ω e.1 l) - (fun _ ↦ L / 2)) - z,
      mSourceMark ω e.1)
  congr 1
  abel

theorem integral_actualRooted_legalMarkedNormalizedOptimalPlan_target
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    (∫ e, h e.2 ∂physicalSceneRootedPlan (legalMarkedNormalizedOptimalPlan q L kin g t ω)
      (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) z) =
      legalMarkedRootedTargetTest q L kin g t h ω z := by
  rw [physicalSceneRootedPlan_legalMarkedNormalizedOptimalPlan_centered q hL]
  rw [integral_map_of_stronglyMeasurable
    (f := fun e : LegalMarkedPhysicalEdge q ↦ h e.2)
    (physicalSceneEdgeReroot ((fun _ ↦ L / 2) + z)).continuous.measurable
      (hh.comp measurable_snd).stronglyMeasurable]
  unfold legalMarkedOptimalPlan
  rw [integral_legalMarkedFixedOptimalPlan]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  change ((fun l ↦ L * mTargetPoint ω e.2 l) - ((fun _ ↦ L / 2) + z),
      mTargetMark ω e.2) =
    (((fun l ↦ L * mTargetPoint ω e.2 l) - (fun _ ↦ L / 2)) - z,
      mTargetMark ω e.2)
  congr 1
  abel

/-- Rooted source loss is exactly the readout of the same optimizer's actual
unused source measure. -/
theorem legalMarkedRootedSourceTest_sub_input_eq_missing
    (q : ℕ) (L : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (h : LegalMarkedPhysicalPoint q → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    legalMarkedRootedSourceTest q L kin g t h ω z - legalMarkedRootedSourceInputTest q L h ω z =
      -(∫ p, h (legalMarkedCenteredCoordinate q L p - z, p.2)
        ∂legalMarkedMissingSourceMeasure q L (L ^ q) kin g t ω) := by
  classical
  let σ := firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
    id id (L ^ q) kin g t ω
  have hb := σ.free_vertex_sum_sub_eq_original_sub_edge_divergence
    (fun i ↦ h (legalMarkedRootedSourcePoint q L ω z i)) (fun _ ↦ 0)
  simp only [Finset.sum_const_zero, sub_zero] at hb
  unfold legalMarkedMissingSourceMeasure
  rw [integral_finsetSum_measure (fun i hi ↦ integrable_dirac (by simp))]
  simp only [integral_dirac]
  change (∑ e ∈ σ.edges, h (legalMarkedRootedSourcePoint q L ω z e.1)) -
    ∑ i : Fin (mSourceCount ω), h (legalMarkedRootedSourcePoint q L ω z i) =
    -(∑ i ∈ σ.freeRows, h (legalMarkedRootedSourcePoint q L ω z i))
  linarith

theorem legalMarkedRootedTargetTest_sub_input_eq_missing
    (q : ℕ) (L : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (h : LegalMarkedPhysicalPoint q → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z : Fin q → ℝ) :
    legalMarkedRootedTargetTest q L kin g t h ω z - legalMarkedRootedTargetInputTest q L h ω z =
      -(∫ p, h (legalMarkedCenteredCoordinate q L p - z, p.2)
        ∂legalMarkedMissingTargetMeasure q L (L ^ q) kin g t ω) := by
  classical
  let σ := firstLegalMarkedOptimalMatching q (mSourceCount ω) (mTargetCount ω)
    id id (L ^ q) kin g t ω
  have hb := σ.free_vertex_sum_sub_eq_original_sub_edge_divergence
    (fun _ ↦ 0) (fun j ↦ h (legalMarkedRootedTargetPoint q L ω z j))
  simp only [Finset.sum_const_zero, zero_sub, Finset.sum_neg_distrib] at hb
  unfold legalMarkedMissingTargetMeasure
  rw [integral_finsetSum_measure (fun j hj ↦ integrable_dirac (by simp))]
  simp only [integral_dirac]
  change (∑ e ∈ σ.edges, h (legalMarkedRootedTargetPoint q L ω z e.2)) -
    ∑ j : Fin (mTargetCount ω), h (legalMarkedRootedTargetPoint q L ω z j) =
    -(∑ j ∈ σ.freeCols, h (legalMarkedRootedTargetPoint q L ω z j))
  linarith

private theorem ofReal_abs_rootedPointReadout_le_window
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) (coord : X → ι → ℝ) (clock : X → ℝ)
    {h : (ι → ℝ) × ℝ → ℝ} {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (ι → ℝ))
    (hzero : ∀ p, p.1 ∉ U → h p = 0) (z : ι → ℝ) :
    ENNReal.ofReal |∫ p, h (coord p - z, clock p) ∂μ| ≤
      ENNReal.ofReal G * cavityRootWindowReadout μ coord (fun _ ↦ 1) U z := by
  have hnorm := enorm_integral_le_lintegral_enorm
    (μ := μ) (fun p ↦ h (coord p - z, clock p))
  have hpoint (p : X) : ENNReal.ofReal |h (coord p - z, clock p)| ≤
      ENNReal.ofReal G * U.indicator (fun _ ↦ (1 : ℝ≥0∞)) (coord p - z) := by
    by_cases hp : coord p - z ∈ U
    · rw [indicator_of_mem hp, mul_one]
      exact ENNReal.ofReal_le_ofReal (hbound _)
    · rw [hzero _ hp, abs_zero, ENNReal.ofReal_zero, indicator_of_notMem hp, mul_zero]
  have hfirst : ENNReal.ofReal |∫ p, h (coord p - z, clock p) ∂μ| ≤
      ∫⁻ p, ENNReal.ofReal |h (coord p - z, clock p)| ∂μ := by
    simpa only [← ofReal_norm, Real.norm_eq_abs] using hnorm
  exact hfirst.trans ((lintegral_mono hpoint).trans_eq
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))

/-- Actual Haar averaging of a bounded spatially supported point test is
controlled by its unchanged original finite point mass. -/
theorem lintegral_cavityRoot_abs_rootedPointReadout_le
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (coord : X → ι → ℝ) (hcoord : Measurable coord)
    (clock : X → ℝ) {h : (ι → ℝ) × ℝ → ℝ} {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hzero : ∀ p, p.1 ∉ U → h p = 0) (D : Set (ι → ℝ)) (N : ℝ) :
    (∫⁻ z, ENNReal.ofReal |∫ p, h (coord p - z, clock p) ∂μ|
      ∂cavityRootMeasure volume D N) ≤
      (ENNReal.ofReal N)⁻¹ * ENNReal.ofReal G * volume U * μ univ := by
  rw [cavityRootMeasure, lintegral_smul_measure, smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal N)⁻¹ *
        ∫⁻ z, ENNReal.ofReal |∫ p, h (coord p - z, clock p) ∂μ| ∂volume :=
      mul_le_mul_of_nonneg_left (lintegral_mono' Measure.restrict_le_self le_rfl) bot_le
    _ ≤ (ENNReal.ofReal N)⁻¹ *
        ∫⁻ z, ENNReal.ofReal G * cavityRootWindowReadout μ coord (fun _ ↦ 1) U z ∂volume :=
      mul_le_mul_of_nonneg_left (lintegral_mono
        (ofReal_abs_rootedPointReadout_le_window μ coord clock hbound U hzero)) bot_le
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_cavityRootWindowReadout volume μ coord hcoord _ measurable_const U hU,
        lintegral_const, one_mul]
      ac_rfl

theorem measurable_legalMarkedRootedSourcePoint (q : ℕ) (L : ℝ) (i : ℕ) :
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedSourcePoint q L p.1 p.2 i) := by
  exact (((measurable_legalMarkedCenteredCoordinate q L).comp
    (((measurable_legalMarkedPhysicalEdge q L i 0).fst).comp measurable_fst)).sub
      measurable_snd).prodMk ((measurable_mSourceMark q i).comp measurable_fst)

theorem measurable_legalMarkedRootedTargetPoint (q : ℕ) (L : ℝ) (j : ℕ) :
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedTargetPoint q L p.1 p.2 j) := by
  exact (((measurable_legalMarkedCenteredCoordinate q L).comp
    (((measurable_legalMarkedPhysicalEdge q L 0 j).snd).comp measurable_fst)).sub
      measurable_snd).prodMk ((measurable_mTargetMark q j).comp measurable_fst)

/-- Both retained and full original source tests are measurable jointly in
their unchanged original environment and their chosen root. -/
theorem measurable_legalMarkedRooted_sourceTests (q : ℕ) (L : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) :
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedSourceTest q L kin g t h p.1 p.2) ∧
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedSourceInputTest q L h p.1 p.2) := by
  have hfixed (mn : ℕ × ℕ) : Measurable
      (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
        ∑ e ∈ (firstLegalMarkedOptimalMatching q mn.1 mn.2 id id (L ^ q) kin g t p.1).edges,
          h (legalMarkedRootedSourcePoint q L p.1 p.2 e.1)) :=
    measurable_retained_edge_sum _ (fun e ↦
      (measurableSet_mem_firstLegalMarkedOptimalMatching q mn.1 mn.2
        measurable_id measurable_id hk hg (L ^ q) t e).preimage measurable_fst) _
      (fun e ↦ hh.comp (measurable_legalMarkedRootedSourcePoint q L e.1))
  have hfull (m : ℕ) : Measurable
      (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
        ∑ i : Fin m, h (legalMarkedRootedSourcePoint q L p.1 p.2 i)) :=
    Finset.measurable_sum _ (fun i hi ↦
      hh.comp (measurable_legalMarkedRootedSourcePoint q L i))
  constructor
  · have hprod : Measurable (fun p : (ℕ × ℕ) ×
        (TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) ↦
        ∑ e ∈ (firstLegalMarkedOptimalMatching q p.1.1 p.1.2 id id (L ^ q)
          kin g t p.2.1).edges, h (legalMarkedRootedSourcePoint q L p.2.1 p.2.2 e.1)) :=
      measurable_from_prod_countable_right hfixed
    have hp := hprod.comp
      ((((measurable_mSourceCount q).comp measurable_fst).prodMk
        ((measurable_mTargetCount q).comp measurable_fst)).prodMk measurable_id)
    simpa only [Function.comp_def, id_eq, legalMarkedRootedSourceTest] using hp
  · have hprod : Measurable (fun p : ℕ ×
        (TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) ↦
        ∑ i : Fin p.1, h (legalMarkedRootedSourcePoint q L p.2.1 p.2.2 i)) :=
      measurable_from_prod_countable_right hfull
    have hp := hprod.comp
      (((measurable_mSourceCount q).comp measurable_fst).prodMk measurable_id)
    simpa only [Function.comp_def, id_eq, legalMarkedRootedSourceInputTest] using hp

theorem measurable_legalMarkedRooted_targetTests (q : ℕ) (L : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) :
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedTargetTest q L kin g t h p.1 p.2) ∧
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedTargetInputTest q L h p.1 p.2) := by
  have hfixed (mn : ℕ × ℕ) : Measurable
      (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
        ∑ e ∈ (firstLegalMarkedOptimalMatching q mn.1 mn.2 id id (L ^ q) kin g t p.1).edges,
          h (legalMarkedRootedTargetPoint q L p.1 p.2 e.2)) :=
    measurable_retained_edge_sum _ (fun e ↦
      (measurableSet_mem_firstLegalMarkedOptimalMatching q mn.1 mn.2
        measurable_id measurable_id hk hg (L ^ q) t e).preimage measurable_fst) _
      (fun e ↦ hh.comp (measurable_legalMarkedRootedTargetPoint q L e.2))
  have hfull (n : ℕ) : Measurable
      (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
        ∑ j : Fin n, h (legalMarkedRootedTargetPoint q L p.1 p.2 j)) :=
    Finset.measurable_sum _ (fun j hj ↦
      hh.comp (measurable_legalMarkedRootedTargetPoint q L j))
  constructor
  · have hprod : Measurable (fun p : (ℕ × ℕ) ×
        (TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) ↦
        ∑ e ∈ (firstLegalMarkedOptimalMatching q p.1.1 p.1.2 id id (L ^ q)
          kin g t p.2.1).edges, h (legalMarkedRootedTargetPoint q L p.2.1 p.2.2 e.2)) :=
      measurable_from_prod_countable_right hfixed
    have hp := hprod.comp
      ((((measurable_mSourceCount q).comp measurable_fst).prodMk
        ((measurable_mTargetCount q).comp measurable_fst)).prodMk measurable_id)
    simpa only [Function.comp_def, id_eq, legalMarkedRootedTargetTest] using hp
  · have hprod : Measurable (fun p : ℕ ×
        (TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) ↦
        ∑ j : Fin p.1, h (legalMarkedRootedTargetPoint q L p.2.1 p.2.2 j)) :=
      measurable_from_prod_countable_right hfull
    have hp := hprod.comp
      (((measurable_mTargetCount q).comp measurable_fst).prodMk measurable_id)
    simpa only [Function.comp_def, id_eq, legalMarkedRootedTargetInputTest] using hp

/-- Per original environment, Haar averaging pays source local test loss
only by that exact environment's same unused-source mass. -/
theorem lintegral_rooted_legalMarked_source_test_error_le
    (q : ℕ) (L : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) {h : LegalMarkedPhysicalPoint q → ℝ} {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (hzero : ∀ p, p.1 ∉ U → h p = 0) (D : Set (Fin q → ℝ))
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (∫⁻ z, ENNReal.ofReal |legalMarkedRootedSourceTest q L kin g t h ω z -
        legalMarkedRootedSourceInputTest q L h ω z|
      ∂cavityRootMeasure volume D (L ^ q)) ≤
      (ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal G * volume U *
        legalMarkedMissingSourceMeasure q L (L ^ q) kin g t ω univ := by
  simp_rw [legalMarkedRootedSourceTest_sub_input_eq_missing, abs_neg]
  exact lintegral_cavityRoot_abs_rootedPointReadout_le _
    (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
      Prod.snd hbound U hU hzero D (L ^ q)

theorem lintegral_rooted_legalMarked_target_test_error_le
    (q : ℕ) (L : ℝ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) {h : LegalMarkedPhysicalPoint q → ℝ} {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (hzero : ∀ p, p.1 ∉ U → h p = 0) (D : Set (Fin q → ℝ))
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (∫⁻ z, ENNReal.ofReal |legalMarkedRootedTargetTest q L kin g t h ω z -
        legalMarkedRootedTargetInputTest q L h ω z|
      ∂cavityRootMeasure volume D (L ^ q)) ≤
      (ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal G * volume U *
        legalMarkedMissingTargetMeasure q L (L ^ q) kin g t ω univ := by
  simp_rw [legalMarkedRootedTargetTest_sub_input_eq_missing, abs_neg]
  exact lintegral_cavityRoot_abs_rootedPointReadout_le _
    (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
      Prod.snd hbound U hU hzero D (L ^ q)

/-- The original uniform root on the entire deterministically centered box. -/
def legalMarkedHaarRootLaw (q : ℕ) (L : ℝ) : Measure (Fin q → ℝ) :=
  cavityRootMeasure volume (haarRootCube (Fin q) (L / 2)) (L ^ q)

theorem isProbabilityMeasure_legalMarkedHaarRootLaw (q : ℕ) {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (legalMarkedHaarRootLaw q L) :=
  isProbabilityMeasure_cavityRootMeasure volume _ _ (pow_pos hL q)
    (volume_haarRootCube_half_legalMarked_scale q hL.le)

/-- The actual original source spatial-test discrepancy, averaged in absolute
value over the original independent environment and the original Haar root. -/
def legalMarkedRootedSourceTestError (q : ℕ) (L : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (h : LegalMarkedPhysicalPoint q → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ z, ENNReal.ofReal |legalMarkedRootedSourceTest q L kin g t h ω z -
    legalMarkedRootedSourceInputTest q L h ω z| ∂legalMarkedHaarRootLaw q L
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))

def legalMarkedRootedTargetTestError (q : ℕ) (L : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (h : LegalMarkedPhysicalPoint q → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ z, ENNReal.ofReal |legalMarkedRootedTargetTest q L kin g t h ω z -
    legalMarkedRootedTargetInputTest q L h ω z| ∂legalMarkedHaarRootLaw q L
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))

private theorem lintegral_error_le_of_actual_defect
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ≥0∞} {D : Ω → ℝ}
    (hD : Integrable D P) (hDn : ∀ ω, 0 ≤ D ω) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ ω, f ω ≤ ENNReal.ofReal c * ENNReal.ofReal (D ω)) :
    (∫⁻ ω, f ω ∂P) ≤ ENNReal.ofReal (c * ∫ ω, D ω ∂P) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (c * D ω) ∂P := by
      apply lintegral_mono
      intro ω
      simpa only [ENNReal.ofReal_mul hc] using hb ω
    _ = ENNReal.ofReal (∫ ω, c * D ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal (hD.const_mul c)
        (.of_forall (fun ω ↦ mul_nonneg hc (hDn ω)))).symm
    _ = _ := by rw [integral_const_mul]

private theorem rooted_test_coefficient_eq_ofReal
    {q : ℕ} {L G : ℝ} (hL : 0 < L) (hG : 0 ≤ G)
    (U : Set (Fin q → ℝ)) (hUf : volume U ≠ ⊤) :
    (ENNReal.ofReal (L ^ q))⁻¹ * ENNReal.ofReal G * volume U =
      ENNReal.ofReal (G * (volume U).toReal / L ^ q) := by
  rw [ENNReal.ofReal_div_of_pos (pow_pos hL q), ENNReal.ofReal_mul hG,
    ENNReal.ofReal_toReal hUf, div_eq_mul_inv]
  ac_rfl

/-- Joint measurability and the actual expected source-defect density control
the full expected absolute local source-test loss. -/
theorem legalMarkedRootedSourceTestError_le_sourceDefect
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (hzero : ∀ p, p.1 ∉ U → h p = 0) :
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
        legalMarkedRootedSourceInputTest q L h p.1 p.2) ∧
    legalMarkedRootedSourceTestError q L α β kin g t h ≤
      ENNReal.ofReal (G * (volume U).toReal * (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q) := by
  obtain ⟨hm, hf⟩ := measurable_legalMarkedRooted_sourceTests q L hk hg t hh
  refine ⟨hm.sub hf, ?_⟩
  have hG : 0 ≤ G := (abs_nonneg (h (0, 0))).trans (hbound (0, 0))
  have hDn (ω : TwoMarkedCloudSpace q ℝ ℝ) : 0 ≤ legalMarkedSourceDefect q id id ω := by
    rw [legalMarkedSourceDefect_eq_nat]
    positivity
  have hc : 0 ≤ G * (volume U).toReal / L ^ q := by positivity
  have hpointwise (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      (∫⁻ z, ENNReal.ofReal |legalMarkedRootedSourceTest q L kin g t h ω z -
          legalMarkedRootedSourceInputTest q L h ω z| ∂legalMarkedHaarRootLaw q L) ≤
        ENNReal.ofReal (G * (volume U).toReal / L ^ q) *
          ENNReal.ofReal (legalMarkedSourceDefect q id id ω) := by
    have hmass : legalMarkedMissingSourceMeasure q L (L ^ q) kin g t ω univ =
        ENNReal.ofReal (legalMarkedSourceDefect q id id ω) := by
      rw [legalMarkedMissingSourceMeasure_univ, legalMarkedSourceDefect_eq_nat,
        ENNReal.ofReal_natCast]
    have hpoint := lintegral_rooted_legalMarked_source_test_error_le q L kin g t
      hbound U hU hzero (haarRootCube (Fin q) (L / 2)) ω
    rw [rooted_test_coefficient_eq_ofReal hL hG U hUf, hmass] at hpoint
    exact hpoint
  have hb := lintegral_error_le_of_actual_defect
    (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)))
    (integrable_legalMarkedSourceDefect q measurable_id measurable_id α β _)
    hDn hc hpointwise
  exact hb.trans_eq (congrArg ENNReal.ofReal (by ring))

/-- Equal original color means give the identical source-defect budget for
the full expected absolute local target-test loss. -/
theorem legalMarkedRootedTargetTestError_le_sourceDefect
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (hzero : ∀ p, p.1 ∉ U → h p = 0) :
    Measurable (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      legalMarkedRootedTargetTest q L kin g t h p.1 p.2 -
        legalMarkedRootedTargetInputTest q L h p.1 p.2) ∧
    legalMarkedRootedTargetTestError q L α β kin g t h ≤
      ENNReal.ofReal (G * (volume U).toReal * (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q) := by
  obtain ⟨hm, hf⟩ := measurable_legalMarkedRooted_targetTests q L hk hg t hh
  refine ⟨hm.sub hf, ?_⟩
  have hG : 0 ≤ G := (abs_nonneg (h (0, 0))).trans (hbound (0, 0))
  have hDn (ω : TwoMarkedCloudSpace q ℝ ℝ) : 0 ≤ legalMarkedOptimalTargetDefect q ω := by
    unfold legalMarkedOptimalTargetDefect
    exact sub_nonneg.mpr (Nat.cast_le.mpr
      ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_right _ _)))
  have hc : 0 ≤ G * (volume U).toReal / L ^ q := by positivity
  have hpointwise (ω : TwoMarkedCloudSpace q ℝ ℝ) :
      (∫⁻ z, ENNReal.ofReal |legalMarkedRootedTargetTest q L kin g t h ω z -
          legalMarkedRootedTargetInputTest q L h ω z| ∂legalMarkedHaarRootLaw q L) ≤
        ENNReal.ofReal (G * (volume U).toReal / L ^ q) *
          ENNReal.ofReal (legalMarkedOptimalTargetDefect q ω) := by
    have hnat : legalMarkedOptimalTargetDefect q ω =
        ((mTargetCount ω - legalMarkedMaximumCard q id id ω : ℕ) : ℝ) := by
      have hcard : legalMarkedMaximumCard q id id ω ≤ mTargetCount ω :=
        (PartialMatching.legalMaximumCard_le_min _).trans (min_le_right _ _)
      exact (Nat.cast_sub hcard).symm
    have hmass : legalMarkedMissingTargetMeasure q L (L ^ q) kin g t ω univ =
        ENNReal.ofReal (legalMarkedOptimalTargetDefect q ω) := by
      rw [legalMarkedMissingTargetMeasure_univ, hnat, ENNReal.ofReal_natCast]
    have hpoint := lintegral_rooted_legalMarked_target_test_error_le q L kin g t
      hbound U hU hzero (haarRootCube (Fin q) (L / 2)) ω
    rw [rooted_test_coefficient_eq_ofReal hL hG U hUf, hmass] at hpoint
    exact hpoint
  have hb := lintegral_error_le_of_actual_defect
    (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q)))
    (integrable_legalMarkedOptimalTargetDefect q α β _) hDn hc hpointwise
  rw [integral_legalMarkedOptimalTargetDefect_eq_source] at hb
  exact hb.trans_eq (congrArg ENNReal.ofReal (by ring))

private theorem integrable_and_integral_abs_le_of_lintegral_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : (∫⁻ ω, ENNReal.ofReal |f ω| ∂P) ≤ ENNReal.ofReal B) :
    Integrable f P ∧ (∫ ω, |f ω| ∂P) ≤ B := by
  have hfi : Integrable f P := ⟨hf.stronglyMeasurable.aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm f).mpr
      (by simpa only [Real.norm_eq_abs] using hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hfi, (ENNReal.ofReal_le_ofReal_iff hB).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hfi.abs (.of_forall (fun ω ↦ abs_nonneg (f ω)))]
  exact hb

/-- The genuine real expected absolute local test discrepancies on the
original environment/root product law have the same actual defect budget. -/
theorem integral_abs_rooted_legalMarked_test_errors_le_sourceDefect
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (hzero : ∀ p, p.1 ∉ U → h p = 0) :
    let P := (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
      (legalMarkedHaarRootLaw q L)
    let B := G * (volume U).toReal * (∫ ω, legalMarkedSourceDefect q id id ω
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q
    (Integrable (fun p ↦ legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
        legalMarkedRootedSourceInputTest q L h p.1 p.2) P ∧
      (∫ p, |legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
        legalMarkedRootedSourceInputTest q L h p.1 p.2| ∂P) ≤ B) ∧
    (Integrable (fun p ↦ legalMarkedRootedTargetTest q L kin g t h p.1 p.2 -
        legalMarkedRootedTargetInputTest q L h p.1 p.2) P ∧
      (∫ p, |legalMarkedRootedTargetTest q L kin g t h p.1 p.2 -
        legalMarkedRootedTargetInputTest q L h p.1 p.2| ∂P) ≤ B) := by
  have hr : IsProbabilityMeasure (legalMarkedHaarRootLaw q L) :=
    isProbabilityMeasure_legalMarkedHaarRootLaw q hL
  have hG : 0 ≤ G := (abs_nonneg (h (0, 0))).trans (hbound (0, 0))
  have hD : 0 ≤ (∫ ω, legalMarkedSourceDefect q id id ω
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) := by
    apply integral_nonneg
    intro ω
    rw [legalMarkedSourceDefect_eq_nat]
    positivity
  have hB : 0 ≤ G * (volume U).toReal * (∫ ω, legalMarkedSourceDefect q id id ω
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q := by positivity
  obtain ⟨hms, hbs⟩ := legalMarkedRootedSourceTestError_le_sourceDefect
    q hL α β hk hg t hh hbound U hU hUf hzero
  obtain ⟨hmt, hbt⟩ := legalMarkedRootedTargetTestError_le_sourceDefect
    q hL α β hk hg t hh hbound U hU hUf hzero
  constructor
  · apply integrable_and_integral_abs_le_of_lintegral_bound _ hms hB
    rw [lintegral_prod (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      ENNReal.ofReal |legalMarkedRootedSourceTest q L kin g t h p.1 p.2 -
        legalMarkedRootedSourceInputTest q L h p.1 p.2|)
      (ENNReal.measurable_ofReal.comp hms.abs).aemeasurable]
    exact hbs
  · apply integrable_and_integral_abs_le_of_lintegral_bound _ hmt hB
    rw [lintegral_prod (fun p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ) ↦
      ENNReal.ofReal |legalMarkedRootedTargetTest q L kin g t h p.1 p.2 -
        legalMarkedRootedTargetInputTest q L h p.1 p.2|)
      (ENNReal.measurable_ofReal.comp hmt.abs).aemeasurable]
    exact hbt

private theorem tendsto_ennreal_zero_of_defect_bound
    {f : ℝ → ℝ≥0∞} {D : ℝ → ℝ} {c : ℝ} (hD : Tendsto D atTop (𝓝 0))
    (hb : ∀ L : ℝ, 0 < L → f L ≤ ENNReal.ofReal (c * D L)) :
    Tendsto f atTop (𝓝 0) := by
  have hreal : Tendsto (fun L ↦ c * D L) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hD
  have hupper : Tendsto (fun L ↦ ENNReal.ofReal (c * D L)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (.of_forall (fun L ↦ bot_le)) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      exact hb L hL)

/-- Vanishing actual source-defect density removes both original local
spatial test losses in mean absolute value under actual Haar rooting. -/
theorem tendsto_legalMarkedRooted_spatialTestErrors_of_sourceDefect
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (hzero : ∀ p, p.1 ∉ U → h p = 0)
    (hdef : Tendsto (fun L : ℝ ↦
      (∫ ω, legalMarkedSourceDefect q id id ω
        ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))) / L ^ q) atTop (𝓝 0)) :
    Tendsto (fun L ↦ legalMarkedRootedSourceTestError q L α β kin g t h) atTop (𝓝 0) ∧
    Tendsto (fun L ↦ legalMarkedRootedTargetTestError q L α β kin g t h) atTop (𝓝 0) := by
  constructor
  · apply tendsto_ennreal_zero_of_defect_bound (c := G * (volume U).toReal) hdef
    intro L hL
    exact (legalMarkedRootedSourceTestError_le_sourceDefect q hL α β hk hg t hh
      hbound U hU hUf hzero).2.trans_eq (congrArg ENNReal.ofReal (by ring))
  · apply tendsto_ennreal_zero_of_defect_bound (c := G * (volume U).toReal) hdef
    intro L hL
    exact (legalMarkedRootedTargetTestError_le_sourceDefect q hL α β hk hg t hh
      hbound U hU hUf hzero).2.trans_eq (congrArg ENNReal.ofReal (by ring))

/-- The original scalar-bin coupling produces actual local spatial test
retention along every real physical scale for both original colors. -/
theorem scalarBins_tendsto_legalMarkedRooted_spatialTestErrors
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hπ : Vlasov.IsCoupling π α β)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ p.2 - p.1) (q : ℕ) (hq : 0 < q)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {h : LegalMarkedPhysicalPoint q → ℝ} (hh : Measurable h) {G : ℝ}
    (hbound : ∀ p, |h p| ≤ G) (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (hzero : ∀ p, p.1 ∉ U → h p = 0) :
    Tendsto (fun L ↦ legalMarkedRootedSourceTestError q L α β kin g t h) atTop (𝓝 0) ∧
    Tendsto (fun L ↦ legalMarkedRootedTargetTestError q L α β kin g t h) atTop (𝓝 0) :=
  tendsto_legalMarkedRooted_spatialTestErrors_of_sourceDefect q α β hk hg t hh hbound
    U hU hUf hzero
      (scalarBins_legalMarkedSourceDefect_div_tendsto_zero D hδ π α β hπ hI hgap q hq)

end OTSelector.Reconstruction
