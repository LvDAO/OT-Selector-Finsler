import OTSelector.Reconstruction.OriginalLegalWeightedReserveCompletion
import OTSelector.Reconstruction.OriginalPoissonWindowSetCounts
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryOriginalInputIntensity
import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveClockSlack

/-!
# Clock count budgets on the actual original reserve coordinate

The counts below read the immutable input of an arbitrary genuine stationary
matching. Exact compact input laws and original intensity identify their true
Poisson rate; neither an ordering of selected reserve arrays nor a positive
population clock gap is assumed.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

local instance reserveClockBudgetInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance reserveClockBudgetPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual number of original input atoms of one color in a fixed physical
window, read as a real number without changing its clock or origin label. -/
def legalOriginalWindowCount (q : ℕ) (B : Set (LegalMarkedPhysicalPoint q))
    (c : Fin 2) (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ((s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})).toReal

/-- Actual fixed-window color counts are measurable on the original scene. -/
theorem measurable_legalOriginalWindowCount (q : ℕ)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B) (c : Fin 2) :
    Measurable (legalOriginalWindowCount q B c) :=
  (((Measure.measurable_coe (hB.prod (measurableSet_singleton c))).comp
    measurable_localFiniteMeasure_coe).comp measurable_snd).ennreal_toReal

/-- Counting the literal finite array agrees with evaluation of its point
measure, including repeated points and all original labels. -/
theorem legalInputBlockMeasure_apply_eq_blockSetCount
    {X : Type*} [MeasurableSpace X] {B : Set X} (hB : MeasurableSet B)
    (b : BlockData X) : legalInputBlockMeasure b B = (blockSetCount B b : ℝ≥0∞) := by
  classical
  simp only [legalInputBlockMeasure, Measure.finsetSum_apply, Measure.dirac_apply' _ hB,
    blockSetCount, Finset.card_filter]
  simp [Set.indicator_apply]

/-- The true colored finite-array readout counts exactly its source array. -/
theorem legalInputTwoBlockMeasure_sourceCount (q : ℕ)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    legalInputTwoBlockMeasure q b (B ×ˢ {(0 : Fin 2)}) = (blockSetCount B b.1 : ℝ≥0∞) := by
  classical
  simp only [legalInputTwoBlockMeasure, Measure.add_apply, legalInputBlockMeasure,
    Measure.finsetSum_apply, mapBlockData, Measure.dirac_apply' _
      (hB.prod (measurableSet_singleton (0 : Fin 2)))]
  simp only [Set.mem_prod, Set.mem_singleton_iff, one_ne_zero, and_false,
    Set.indicator_of_notMem, not_false_eq_true, Finset.sum_const_zero, add_zero]
  simp only [blockSetCount, Finset.card_filter]
  simp [Set.indicator_apply]

/-- The corresponding target readout uses the unchanged original target array. -/
theorem legalInputTwoBlockMeasure_targetCount (q : ℕ)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    legalInputTwoBlockMeasure q b (B ×ˢ {(1 : Fin 2)}) = (blockSetCount B b.2 : ℝ≥0∞) := by
  classical
  simp only [legalInputTwoBlockMeasure, Measure.add_apply, legalInputBlockMeasure,
    Measure.finsetSum_apply, mapBlockData, Measure.dirac_apply' _
      (hB.prod (measurableSet_singleton (1 : Fin 2)))]
  simp only [Set.mem_prod, Set.mem_singleton_iff, zero_ne_one, and_false,
    Set.indicator_of_notMem, not_false_eq_true, Finset.sum_const_zero, zero_add]
  simp only [blockSetCount, Finset.card_filter]
  simp [Set.indicator_apply]

/-- Exact Poisson laws on compact input restrictions already determine the
count law before any core or reserve endpoint is selected. -/
theorem exists_rate_hasLaw_legalOriginalWindowCount
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B K : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hK : IsCompact K) (hBK : B ⊆ K) (c : Fin 2) :
    ∃ r : ℝ≥0, HasLaw (legalOriginalWindowCount q B c)
      ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) (N.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let U : Set (LegalColoredInputPoint q) := K ×ˢ univ
  obtain ⟨S, hS, hmap⟩ := N.map_inputRestriction_eq_originalPoisson
    (hK.prod isCompact_univ)
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have hfin : volume (haarRootCube (Fin q) S) ≠ ∞ :=
    (isCompact_Icc : IsCompact (haarRootCube (Fin q) S)).measure_lt_top.ne
  let P := legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β
  let X := fun b : BlockData (LegalMarkedPhysicalPoint q) ×
      BlockData (LegalMarkedPhysicalPoint q) ↦ (legalInputTwoBlockMeasure q b).restrict U
  let Y := fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)).restrict U
  let f := fun μ : Measure (LegalColoredInputPoint q) ↦ (μ (B ×ˢ {c})).toReal
  have hf : Measurable f := (Measure.measurable_coe
    (hB.prod (measurableSet_singleton c))).ennreal_toReal
  have hmrestrict : Measurable (fun μ : Measure (LegalColoredInputPoint q) ↦ μ.restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [Measure.restrict_apply hV, U] using
      Measure.measurable_coe (hV.inter (hK.measurableSet.prod MeasurableSet.univ))
  have hX : Measurable X := hmrestrict.comp
    (measurable_localFiniteMeasure_coe.comp (measurable_legalInputTwoBlockLocal q))
  have hY : Measurable Y := hmrestrict.comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)
  have hBX : B ×ˢ {c} ⊆ U := by
    rintro ⟨x, a⟩ hx
    exact ⟨hBK hx.1, mem_univ _⟩
  have hfY (s : LegalMarkedOptimalInputScene q) : f (Y s) = legalOriginalWindowCount q B c s := by
    dsimp only [f, Y, legalOriginalWindowCount]
    rw [Measure.restrict_apply (hB.prod (measurableSet_singleton c)), inter_eq_left.mpr hBX]
  have hlawY : HasLaw Y (P.map X) (N.law : Measure (LegalMarkedOptimalInputScene q)) := ⟨hY.aemeasurable, hmap⟩
  have hlawX : HasLaw X (P.map X) P := ⟨hX.aemeasurable, rfl⟩
  have hfX (b) : f (X b) = (legalInputTwoBlockMeasure q b (B ×ˢ {c})).toReal := by
    dsimp only [f, X]
    rw [Measure.restrict_apply (hB.prod (measurableSet_singleton c)), inter_eq_left.mpr hBX]
  have htransfer (r : ℝ≥0)
      (h : HasLaw (fun b ↦ (legalInputTwoBlockMeasure q b (B ×ˢ {c})).toReal)
        ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) P) :
      HasLaw (legalOriginalWindowCount q B c)
        ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) (N.law : Measure (LegalMarkedOptimalInputScene q)) := by
    have hh := hlawX.comp_of_hasLaw_comp hf.aemeasurable hlawY
      (h.congr (.of_forall hfX))
    exact hh.congr (.of_forall fun s ↦ (hfY s).symm)
  fin_cases c
  · let r := (((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S)).prod α B).toNNReal
    refine ⟨r, htransfer r ?_⟩
    have hc := hasLaw_originalPoissonWindow_sourceSetCount_physical q hfin hvol α β hB
    have hcast : HasLaw (fun n : ℕ ↦ (n : ℝ))
        ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) (poissonMeasure r) :=
      ⟨measurable_from_nat.aemeasurable, rfl⟩
    exact (hcast.fun_comp hc).congr (.of_forall fun b ↦ by
      change (legalInputTwoBlockMeasure q b (B ×ˢ {(0 : Fin 2)})).toReal = _
      rw [legalInputTwoBlockMeasure_sourceCount q hB, ENNReal.toReal_natCast])
  · let r := (((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S)).prod β B).toNNReal
    refine ⟨r, htransfer r ?_⟩
    have hc := hasLaw_originalPoissonWindow_targetSetCount_physical q hfin hvol α β hB
    have hcast : HasLaw (fun n : ℕ ↦ (n : ℝ))
        ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) (poissonMeasure r) :=
      ⟨measurable_from_nat.aemeasurable, rfl⟩
    exact (hcast.fun_comp hc).congr (.of_forall fun b ↦ by
      change (legalInputTwoBlockMeasure q b (B ×ˢ {(1 : Fin 2)})).toReal = _
      rw [legalInputTwoBlockMeasure_targetCount q hB, ENNReal.toReal_natCast])

/-- The original clock law attached to an immutable input color. -/
def legalOriginalColorClock (α β : Measure ℝ) (c : Fin 2) : Measure ℝ :=
  if c = 0 then α else β

/-- The exact first moment of an actual bounded-window count uses the
original physical volume and original clock measure. -/
theorem LegalWeightedStationaryPoissonMatching.integral_legalOriginalWindowCount
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B K : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hK : IsCompact K) (hBK : B ⊆ K) (c : Fin 2) :
    (∫ s, legalOriginalWindowCount q B c s ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) =
      (((volume : Measure (Fin q → ℝ)).prod (legalOriginalColorClock α β c)) B).toReal := by
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c})) :=
    ((Measure.measurable_coe (hB.prod (measurableSet_singleton c))).comp
      measurable_localFiniteMeasure_coe).comp measurable_snd
  have hfinite : ∀ᵐ s ∂(N.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) < ∞ := by
    apply Eventually.of_forall
    intro s
    exact (measure_mono (Set.prod_mono hBK (Subset.refl _))).trans_lt
      (hK.prod isCompact_singleton).measure_lt_top
  have hcol (s : LegalMarkedOptimalInputScene q) :
      legalInputColorMeasure q s.2 c B =
        (s.2 : Measure (LegalColoredInputPoint q)) (B ×ˢ {c}) := by
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst hB,
      Measure.restrict_apply (hB.preimage measurable_fst)]
    rfl
  calc
    _ = (∫⁻ s, legalInputColorMeasure q s.2 c B ∂(N.law : Measure (LegalMarkedOptimalInputScene q))).toReal := by
      simp_rw [hcol]
      exact integral_toReal hm.aemeasurable hfinite
    _ = (legalMarkedInputColorIntensity q (N.law : Measure (LegalMarkedOptimalInputScene q)) c B).toReal := by
      rw [lintegral_legalInputColorMeasure_eq_intensity q _ c hB]
    _ = _ := by
      fin_cases c
      · rw [show (⟨0, by omega⟩ : Fin 2) = 0 from rfl,
          N.inputColorIntensities_eq_volume_prod.1]
        rfl
      · rw [show (⟨1, by omega⟩ : Fin 2) = 1 from rfl,
          N.inputColorIntensities_eq_volume_prod.2]
        rfl

/-- Every actual bounded physical-window color count has the exact Poisson
law of its unchanged original intensity. The auxiliary enclosing finite
array cube disappears by its genuine first-moment identity. -/
theorem LegalWeightedStationaryPoissonMatching.hasLaw_legalOriginalWindowCount
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B K : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hK : IsCompact K) (hBK : B ⊆ K) (c : Fin 2) :
    HasLaw (legalOriginalWindowCount q B c)
      ((poissonMeasure ((((volume : Measure (Fin q → ℝ)).prod
        (legalOriginalColorClock α β c)) B).toNNReal)).map (fun n : ℕ ↦ (n : ℝ)))
      (N.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨r, hr⟩ := exists_rate_hasLaw_legalOriginalWindowCount N hB hK hBK c
  have hmean : (∫ s, legalOriginalWindowCount q B c s ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) = (r : ℝ) := by
    rw [hr.integral_eq]
    change (∫ x : ℝ, id x ∂(poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) = _
    rw [integral_map measurable_from_nat.aemeasurable aestronglyMeasurable_id]
    exact integral_id_poissonMeasure r
  have heq : r = (((volume : Measure (Fin q → ℝ)).prod
      (legalOriginalColorClock α β c)) B).toNNReal := by
    apply NNReal.eq
    exact hmean.symm.trans (N.integral_legalOriginalWindowCount hB hK hBK c)
  simpa only [heq] using hr

/-- Actual original count fluctuations have the genuine Poisson square-root
bound. This requires no population gap, kinetic moment, or selected iid law. -/
theorem LegalWeightedStationaryPoissonMatching.windowCount_deviation_integrable_bound
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {B K : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hK : IsCompact K) (hBK : B ⊆ K) (c : Fin 2) :
    let m := (((volume : Measure (Fin q → ℝ)).prod (legalOriginalColorClock α β c)) B).toReal
    Integrable (fun s ↦ |legalOriginalWindowCount q B c s - m|) (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, |legalOriginalWindowCount q B c s - m| ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) ≤ Real.sqrt m := by
  dsimp only
  let r := (((volume : Measure (Fin q → ℝ)).prod (legalOriginalColorClock α β c)) B).toNNReal
  have hr := N.hasLaw_legalOriginalWindowCount hB hK hBK c
  have hcast := (measurable_from_nat : Measurable (fun n : ℕ ↦ (n : ℝ)))
  have hI : Integrable (fun x : ℝ ↦ |x - (r : ℝ)|)
      ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) := by
    apply (integrable_map_measure (by fun_prop) hcast.aemeasurable).mpr
    exact ((integrable_id_poissonMeasure r).sub (integrable_const (r : ℝ))).abs
  have hI' : Integrable (fun x : ℝ ↦ |x - (r : ℝ)|)
      ((N.law : Measure (LegalMarkedOptimalInputScene q)).map (legalOriginalWindowCount q B c)) := by
    rw [hr.map_eq]
    exact hI
  refine ⟨hI'.comp_measurable (measurable_legalOriginalWindowCount q hB c), ?_⟩
  calc
    _ = ∫ x : ℝ, |x - (r : ℝ)| ∂(poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ)) :=
      hr.integral_comp hI.aestronglyMeasurable
    _ = ∫ n : ℕ, |(n : ℝ) - (r : ℝ)| ∂poissonMeasure r :=
      integral_map hcast.aemeasurable hI.aestronglyMeasurable
    _ ≤ Real.sqrt (r : ℝ) := integral_abs_sub_id_poissonMeasure_le r

/-- Dilation retains the original color and clock; a window count is its
literal pullback count on the unchanged original reserve coordinate. -/
theorem legalOriginalWindowCount_dilation (q : ℕ) (d : ℝ) (hd : d ≠ 0)
    {B : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (c : Fin 2) (s : LegalMarkedOptimalInputScene q) :
    legalOriginalWindowCount q B c (legalMarkedInputSceneDilation q d hd s) =
      legalOriginalWindowCount q ((legalMarkedPointDilation q d hd) ⁻¹' B) c s := by
  unfold legalOriginalWindowCount
  change (((localFiniteMapHomeomorph (legalColoredInputDilation q d hd) s.2 :
    LocalFiniteMeasure (LegalColoredInputPoint q)) : Measure _) (B ×ˢ {c})).toReal = _
  rw [coe_localFiniteMapHomeomorph, Measure.map_apply
    (legalColoredInputDilation q d hd).continuous.measurable
    (hB.prod (measurableSet_singleton c))]
  rfl

/-- The genuine reserve count after physical dilation has its exact original
intensity, including the full dimension-dependent spatial Jacobian. -/
theorem LegalWeightedStationaryPoissonMatching.dilated_windowCount_deviation_integrable_bound
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0)
    {B K : Set (LegalMarkedPhysicalPoint q)} (hB : MeasurableSet B)
    (hK : IsCompact K) (hBK : B ⊆ K) (c : Fin 2) :
    let m := |(d ^ q)⁻¹| *
      (((volume : Measure (Fin q → ℝ)).prod (legalOriginalColorClock α β c)) B).toReal
    Integrable (fun s ↦ |legalOriginalWindowCount q B c
      (legalMarkedInputSceneDilation q d hd s) - m|) (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, |legalOriginalWindowCount q B c (legalMarkedInputSceneDilation q d hd s) - m|
        ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) ≤ Real.sqrt m := by
  dsimp only
  have hpre := (legalMarkedPointDilation q d hd).continuous.measurable hB
  have hcompact := (legalMarkedPointDilation q d hd).isCompact_preimage.mpr hK
  have hsub : (legalMarkedPointDilation q d hd) ⁻¹' B ⊆
      (legalMarkedPointDilation q d hd) ⁻¹' K := preimage_mono hBK
  have : IsProbabilityMeasure (legalOriginalColorClock α β c) := by
    fin_cases c <;> dsimp [legalOriginalColorClock] <;> infer_instance
  have hrate : (((volume : Measure (Fin q → ℝ)).prod (legalOriginalColorClock α β c))
      ((legalMarkedPointDilation q d hd) ⁻¹' B)).toReal =
      |(d ^ q)⁻¹| * (((volume : Measure (Fin q → ℝ)).prod
        (legalOriginalColorClock α β c)) B).toReal := by
    rw [← Measure.map_apply (legalMarkedPointDilation q d hd).continuous.measurable hB,
      map_physicalIntensity_legalMarkedPointDilation q d hd, Measure.smul_apply,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  have h := N.windowCount_deviation_integrable_bound hpre hcompact hsub c
  simpa only [legalOriginalWindowCount_dilation q d hd hB, hrate] using h

/-- A reserve array extracted by the genuine origin-index embedding has
exactly the actual original reserve clock counts. Its tuple order receives
no independent-distribution assertion. -/
theorem originalReserveArray_clockCount_eq_actual
    {q : ℕ} (r : LegalMarkedOptimalInputScene q) (c : Fin 2)
    {U B : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    (hB : MeasurableSet B) (b : BlockData (LegalMarkedPhysicalPoint q))
    (hread : legalInputBlockMeasure b = (legalInputColorMeasure q r.2 c).restrict U) :
    (blockSetCount B b : ℝ) = legalOriginalWindowCount q (U ∩ B) c r := by
  have h := congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ (μ B).toReal) hread
  rw [legalInputBlockMeasure_apply_eq_blockSetCount hB, ENNReal.toReal_natCast,
    Measure.restrict_apply hB, legalInputColorMeasure, Measure.map_apply measurable_fst
      (hB.inter hU), Measure.restrict_apply ((hB.inter hU).preimage measurable_fst)] at h
  rw [h]
  unfold legalOriginalWindowCount
  congr 2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
  tauto

/-- The actual mean count in a fixed physical window after the reserve
spatial dilation, with original color law and exact inverse Jacobian. -/
def legalOriginalDilatedWindowMean (q : ℕ) (α β : Measure ℝ) (d : ℝ)
    (B : Set (LegalMarkedPhysicalPoint q)) (c : Fin 2) : ℝ :=
  |(d ^ q)⁻¹| * (((volume : Measure (Fin q → ℝ)).prod
    (legalOriginalColorClock α β c)) B).toReal

/-- Two true reserve clock counts in a single original scene control the
expected shortfall below their own original population surplus. Independence
between the selected counts and the retained core is unnecessary. -/
theorem LegalWeightedStationaryPoissonMatching.reserveWindow_shortfall_integrable_bound
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0)
    {Bs Bt K : Set (LegalMarkedPhysicalPoint q)}
    (hBs : MeasurableSet Bs) (hBt : MeasurableSet Bt)
    (hK : IsCompact K) (hBsK : Bs ⊆ K) (hBtK : Bt ⊆ K) :
    let ms := legalOriginalDilatedWindowMean q α β d Bs 0
    let mt := legalOriginalDilatedWindowMean q α β d Bt 1
    let deficit := fun s ↦ max ((mt - ms) -
      (legalOriginalWindowCount q Bt 1 (legalMarkedInputSceneDilation q d hd s) -
        legalOriginalWindowCount q Bs 0 (legalMarkedInputSceneDilation q d hd s))) 0
    Integrable deficit (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, deficit s ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        Real.sqrt ms + Real.sqrt mt := by
  dsimp only
  obtain ⟨hIs, hbs⟩ := N.dilated_windowCount_deviation_integrable_bound d hd hBs hK hBsK 0
  obtain ⟨hIt, hbt⟩ := N.dilated_windowCount_deviation_integrable_bound d hd hBt hK hBtK 1
  let xs := fun s ↦ legalOriginalWindowCount q Bs 0 (legalMarkedInputSceneDilation q d hd s)
  let xt := fun s ↦ legalOriginalWindowCount q Bt 1 (legalMarkedInputSceneDilation q d hd s)
  let ms := legalOriginalDilatedWindowMean q α β d Bs 0
  let mt := legalOriginalDilatedWindowMean q α β d Bt 1
  have hm : Measurable (fun s ↦ max ((mt - ms) - (xt s - xs s)) 0) := by
    exact (measurable_const.sub
      (((measurable_legalOriginalWindowCount q hBt 1).comp
        (continuous_legalMarkedInputSceneDilation q d hd).measurable).sub
      ((measurable_legalOriginalWindowCount q hBs 0).comp
        (continuous_legalMarkedInputSceneDilation q d hd).measurable))).max measurable_const
  have hb (s) : max ((mt - ms) - (xt s - xs s)) 0 ≤ |xs s - ms| + |xt s - mt| := by
    apply max_le
    · have hs := le_abs_self (xs s - ms)
      have ht := neg_le_abs (xt s - mt)
      linarith
    · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hI : Integrable (fun s ↦ max ((mt - ms) - (xt s - xs s)) 0)
      (N.law : Measure (LegalMarkedOptimalInputScene q)) := by
    apply (hIs.add hIt).mono' hm.aestronglyMeasurable
    exact .of_forall fun s ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hb s
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ s, |xs s - ms| + |xt s - mt| ∂(N.law : Measure (LegalMarkedOptimalInputScene q)) :=
      integral_mono hI (hIs.add hIt) hb
    _ = _ := integral_add hIs hIt
    _ ≤ _ := add_le_add hbs hbt

/-- The total genuine reserve error at a finite prescribed list of clock
thresholds inside the SAME physical window. -/
def legalOriginalReserveWindowClockDeviation {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) (d : ℝ) (hd : d ≠ 0)
    (U : Set (LegalMarkedPhysicalPoint q)) (a : J → ℝ)
    (s : LegalMarkedOptimalInputScene q) : ℝ :=
  ∑ j : J,
    (|legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a j))) 0
        (legalMarkedInputSceneDilation q d hd s) -
      legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a j))) 0| +
    |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a j))) 1
        (legalMarkedInputSceneDilation q d hd s) -
      legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a j))) 1|)

/-- Every original finite-window clock surplus is within the chosen error
of its own original population surplus. No positive gap is imposed. -/
def legalOriginalReserveWindowClockBudgetEvent {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) (d : ℝ) (hd : d ≠ 0)
    (U : Set (LegalMarkedPhysicalPoint q)) (a : J → ℝ) (δ : ℝ) :
    Set (LegalMarkedOptimalInputScene q) :=
  {s | ∀ j,
    legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a j))) 1 -
        legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a j))) 0 - δ ≤
      legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a j))) 1
          (legalMarkedInputSceneDilation q d hd s) -
        legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a j))) 0
          (legalMarkedInputSceneDilation q d hd s)}

/-- The true finite-window reserve clock deviation is pointwise nonnegative. -/
theorem legalOriginalReserveWindowClockDeviation_nonneg {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) (d : ℝ) (hd : d ≠ 0)
    (U : Set (LegalMarkedPhysicalPoint q)) (a : J → ℝ) (s) :
    0 ≤ legalOriginalReserveWindowClockDeviation q α β d hd U a s :=
  Finset.sum_nonneg fun _ _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Every failed original finite-window surplus inequality forces a large
actual deviation of the true original reserve counts. -/
theorem legalOriginalReserveWindowClockBudgetEvent_compl_subset_deviation
    {J : Type*} [Fintype J] (q : ℕ) (α β : Measure ℝ) (d : ℝ) (hd : d ≠ 0)
    (U : Set (LegalMarkedPhysicalPoint q)) (a : J → ℝ) (δ : ℝ) :
    (legalOriginalReserveWindowClockBudgetEvent q α β d hd U a δ)ᶜ ⊆
      {s | δ ≤ legalOriginalReserveWindowClockDeviation q α β d hd U a s} := by
  intro s hs
  obtain ⟨j, hj⟩ := not_forall.mp hs
  have hsingle :
      |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a j))) 0
          (legalMarkedInputSceneDilation q d hd s) -
        legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a j))) 0| +
      |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a j))) 1
          (legalMarkedInputSceneDilation q d hd s) -
        legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a j))) 1| ≤
        legalOriginalReserveWindowClockDeviation q α β d hd U a s :=
    by
      unfold legalOriginalReserveWindowClockDeviation
      exact Finset.single_le_sum
        (f := fun k : J ↦
          |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a k))) 0
            (legalMarkedInputSceneDilation q d hd s) -
              legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a k))) 0| +
          |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a k))) 1
            (legalMarkedInputSceneDilation q d hd s) -
              legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a k))) 1|)
        (fun _ _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
  have hs := le_abs_self (legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a j))) 0
    (legalMarkedInputSceneDilation q d hd s) -
    legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a j))) 0)
  have ht := neg_le_abs (legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a j))) 1
    (legalMarkedInputSceneDilation q d hd s) -
    legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a j))) 1)
  have hj' := lt_of_not_ge hj
  change δ ≤ legalOriginalReserveWindowClockDeviation q α β d hd U a s
  linarith

/-- The actual dilated input mean of any fixed subwindow is bounded by its
literal spatial carrier volume; the original clock law has total mass one. -/
theorem legalOriginalDilatedWindowMean_le_spatialVolume
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (d : ℝ) {B : Set (LegalMarkedPhysicalPoint q)}
    {V : Set (Fin q → ℝ)} (_hV : MeasurableSet V) (hVfin : volume V ≠ ∞)
    (hBV : B ⊆ V ×ˢ univ) (c : Fin 2) :
    legalOriginalDilatedWindowMean q α β d B c ≤ |(d ^ q)⁻¹| * (volume V).toReal := by
  have : IsProbabilityMeasure (legalOriginalColorClock α β c) := by
    fin_cases c <;> dsimp [legalOriginalColorClock] <;> infer_instance
  unfold legalOriginalDilatedWindowMean
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply ENNReal.toReal_mono hVfin
  exact (measure_mono hBV).trans_eq (by rw [Measure.prod_prod, measure_univ, mul_one])

/-- The simultaneous genuine reserve clock event is measurable on the same
original scene, retaining its correlation with every retained core. -/
theorem measurableSet_legalOriginalReserveWindowClockBudgetEvent
    {J : Type*} [Fintype J] (q : ℕ) (α β : Measure ℝ) (d : ℝ) (hd : d ≠ 0)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    (a : J → ℝ) (δ : ℝ) :
    MeasurableSet (legalOriginalReserveWindowClockBudgetEvent q α β d hd U a δ) := by
  have hm (j : J) : MeasurableSet {s : LegalMarkedOptimalInputScene q |
      legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a j))) 1 -
          legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a j))) 0 - δ ≤
        legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a j))) 1
            (legalMarkedInputSceneDilation q d hd s) -
          legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a j))) 0
            (legalMarkedInputSceneDilation q d hd s)} := by
    apply measurableSet_le measurable_const
    exact (((measurable_legalOriginalWindowCount q
      (hU.inter (MeasurableSet.univ.prod measurableSet_Ioi)) 1).comp
        (continuous_legalMarkedInputSceneDilation q d hd).measurable).sub
      ((measurable_legalOriginalWindowCount q
        (hU.inter (MeasurableSet.univ.prod measurableSet_Ici)) 0).comp
          (continuous_legalMarkedInputSceneDilation q d hd).measurable))
  simpa only [legalOriginalReserveWindowClockBudgetEvent, Set.ofPred_forall] using
    MeasurableSet.iInter hm

/-- The finite list of genuine reserve clock counts has a square-root
volume expected error, uniformly in the original physical clock cutoff. -/
theorem LegalWeightedStationaryPoissonMatching.reserveWindow_clockDeviation_integrable_bound
    {J : Type*} [Fintype J] {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : IsCompact U)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V) (hVfin : volume V ≠ ∞)
    (hUV : U ⊆ V ×ˢ univ) (a : J → ℝ) :
    Integrable (legalOriginalReserveWindowClockDeviation q α β d hd U a)
        (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, legalOriginalReserveWindowClockDeviation q α β d hd U a s
        ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        2 * (Fintype.card J : ℝ) * Real.sqrt (|(d ^ q)⁻¹| * (volume V).toReal) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have hs (j : J) := N.dilated_windowCount_deviation_integrable_bound d hd
    (hU.measurableSet.inter (MeasurableSet.univ.prod (measurableSet_Ici (a := a j))))
    hU inter_subset_left 0
  have ht (j : J) := N.dilated_windowCount_deviation_integrable_bound d hd
    (hU.measurableSet.inter (MeasurableSet.univ.prod (measurableSet_Ioi (a := a j))))
    hU inter_subset_left 1
  have hms (j : J) := legalOriginalDilatedWindowMean_le_spatialVolume α β d hV hVfin
    (inter_subset_left.trans hUV : U ∩ (univ ×ˢ Ici (a j)) ⊆ V ×ˢ univ) 0
  have hmt (j : J) := legalOriginalDilatedWindowMean_le_spatialVolume α β d hV hVfin
    (inter_subset_left.trans hUV : U ∩ (univ ×ˢ Ioi (a j)) ⊆ V ×ˢ univ) 1
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (hs j).1.add (ht j).1), ?_⟩
  unfold legalOriginalReserveWindowClockDeviation
  have hIj (j : J) : Integrable (fun s ↦
      |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a j))) 0
          (legalMarkedInputSceneDilation q d hd s) -
        legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a j))) 0| +
      |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a j))) 1
          (legalMarkedInputSceneDilation q d hd s) -
        legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a j))) 1|)
      (N.law : Measure (LegalMarkedOptimalInputScene q)) := (hs j).1.add (ht j).1
  rw [integral_finsetSum _ (fun j _ ↦ hIj j)]
  have hb (j : J) :
      (∫ s, |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici (a j))) 0
        (legalMarkedInputSceneDilation q d hd s) -
          legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ici (a j))) 0| +
        |legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi (a j))) 1
          (legalMarkedInputSceneDilation q d hd s) -
          legalOriginalDilatedWindowMean q α β d (U ∩ (univ ×ˢ Ioi (a j))) 1|
        ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        2 * Real.sqrt (|(d ^ q)⁻¹| * (volume V).toReal) := by
    dsimp only [legalOriginalDilatedWindowMean]
    rw [integral_add (hs j).1 (ht j).1]
    exact (add_le_add (hs j).2 (ht j).2).trans
      ((add_le_add (Real.sqrt_le_sqrt (hms j)) (Real.sqrt_le_sqrt (hmt j))).trans_eq (by ring))
  exact (Finset.sum_le_sum (fun j _ ↦ hb j)).trans_eq (by simp; ring)

/-- The original reserve coordinate satisfies all finite-window clock
surplus inequalities except on a set of the displayed true Poisson error
probability. No positive population clock gap or capacity oracle is assumed. -/
theorem LegalWeightedStationaryPoissonMatching.reserveWindow_clockBudget_failure_bound
    {J : Type*} [Fintype J] {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : IsCompact U)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V) (hVfin : volume V ≠ ∞)
    (hUV : U ⊆ V ×ˢ univ) (a : J → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (N.law : Measure (LegalMarkedOptimalInputScene q)).real
      (legalOriginalReserveWindowClockBudgetEvent q α β d hd U a δ)ᶜ ≤
        2 * (Fintype.card J : ℝ) * Real.sqrt (|(d ^ q)⁻¹| * (volume V).toReal) / δ := by
  obtain ⟨hI, hb⟩ := N.reserveWindow_clockDeviation_integrable_bound d hd hU hV hVfin hUV a
  have hm := mul_meas_ge_le_integral_of_nonneg
    (.of_forall (legalOriginalReserveWindowClockDeviation_nonneg q α β d hd U a)) hI δ
  have hprob := measureReal_mono
    (μ := (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (legalOriginalReserveWindowClockBudgetEvent_compl_subset_deviation q α β d hd U a δ)
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ δ * (N.law : Measure (LegalMarkedOptimalInputScene q)).real
        {s | δ ≤ legalOriginalReserveWindowClockDeviation q α β d hd U a s} := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprob hδ.le
    _ ≤ _ := hm.trans hb

/-- On the original physical cube the rate is literally
`|(d^q)⁻¹| * (2R)^q`; no enclosing-array volume enters the bound. -/
theorem LegalWeightedStationaryPoissonMatching.reservePhysicalWindow_clockBudget_failure_bound
    {J : Type*} [Fintype J] {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0) {R : ℝ} (hR : 0 ≤ R) (K : ℝ)
    (a : J → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (N.law : Measure (LegalMarkedOptimalInputScene q)).real
      (legalOriginalReserveWindowClockBudgetEvent q α β d hd
        (legalWeightedPhysicalWindow q R K) a δ)ᶜ ≤
      2 * (Fintype.card J : ℝ) * Real.sqrt (|(d ^ q)⁻¹| * (2 * R) ^ q) / δ := by
  have h := N.reserveWindow_clockBudget_failure_bound d hd
    (isCompact_legalWeightedPhysicalWindow q R K) measurableSet_Icc
    (isCompact_Icc.measure_lt_top.ne : volume (haarRootCube (Fin q) R) ≠ ∞)
    (fun x hx ↦ ⟨hx.1, mem_univ _⟩) a hδ
  change (N.law : Measure (LegalMarkedOptimalInputScene q)).real
      (legalOriginalReserveWindowClockBudgetEvent q α β d hd
        (legalWeightedPhysicalWindow q R K) a δ)ᶜ ≤
      2 * (Fintype.card J : ℝ) *
        Real.sqrt (|(d ^ q)⁻¹| * (volume (haarRootCube (Fin q) R)).toReal) / δ at h
  have hpow : 0 ≤ (2 * R) ^ q := pow_nonneg (mul_nonneg (by norm_num) hR) q
  simpa only [volume_haarRootCube (Fin q) hR, Fintype.card_fin,
    ENNReal.toReal_ofReal hpow] using h

/-- In the produced finite core, the very same reserve index arrays read
the two original clock tails exactly, at every threshold simultaneously. -/
theorem IsOriginalReserveWindowCore.clockCounts_eq_actual
    {q : ℕ} {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    {cost : LegalMarkedPhysicalEdge q → ℝ} {s r : LegalMarkedOptimalInputScene q}
    {b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)}
    (hcore : IsOriginalReserveWindowCore q U cost s r b) :
    let source := legalOriginalBlockRestriction U b.1
    let target := legalOriginalBlockRestriction U b.2
    let νs := (legalInputColorMeasure q r.2 0).restrict U
    let νt := (legalInputColorMeasure q r.2 1).restrict U
    ∀ a : ℝ,
      (blockSetCount (univ ×ˢ Ici a) (originalReserveAtomArray νs source.2) : ℝ) =
        legalOriginalWindowCount q (U ∩ (univ ×ˢ Ici a)) 0 r ∧
      (blockSetCount (univ ×ˢ Ioi a) (originalReserveAtomArray νt target.2) : ℝ) =
        legalOriginalWindowCount q (U ∩ (univ ×ˢ Ioi a)) 1 r := by
  dsimp only [IsOriginalReserveWindowCore] at hcore
  obtain ⟨σ, _, _, _, _, _, hs, ht, _, _, _⟩ := hcore
  dsimp only
  intro a
  exact ⟨originalReserveArray_clockCount_eq_actual r 0 hU
      (MeasurableSet.univ.prod measurableSet_Ici) _ hs,
    originalReserveArray_clockCount_eq_actual r 1 hU
      (MeasurableSet.univ.prod measurableSet_Ioi) _ ht⟩

/-- The original labelled coupling retains the exact law of its actual
reserve coordinate. Clock probabilities therefore transfer through that
coordinate without assigning any iid law to an ordered extracted subarray. -/
theorem reserveWindow_clockBudget_failure_bound_of_original_marginal
    {J : Type*} [Fintype J] {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (P : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))))
    (hP : P.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (d : ℝ) (hd : d ≠ 0)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : IsCompact U)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V) (hVfin : volume V ≠ ∞)
    (hUV : U ⊆ V ×ˢ univ) (a : J → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    P.real ((fun p ↦ p.1.2) ⁻¹'
      (legalOriginalReserveWindowClockBudgetEvent q α β d hd U a δ)ᶜ) ≤
        2 * (Fintype.card J : ℝ) * Real.sqrt (|(d ^ q)⁻¹| * (volume V).toReal) / δ := by
  have hproj : P.map (fun p ↦ p.1.2) = (N.law : Measure (LegalMarkedOptimalInputScene q)) := by
    rw [show (fun p : (LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) ↦
      p.1.2) = Prod.snd ∘ Prod.fst from rfl,
      ← Measure.map_map measurable_snd measurable_fst, hP]
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
  have hE := (measurableSet_legalOriginalReserveWindowClockBudgetEvent q α β d hd
    hU.measurableSet a δ).compl
  have heq : P.real ((fun p ↦ p.1.2) ⁻¹'
      (legalOriginalReserveWindowClockBudgetEvent q α β d hd U a δ)ᶜ) =
      (N.law : Measure (LegalMarkedOptimalInputScene q)).real
        (legalOriginalReserveWindowClockBudgetEvent q α β d hd U a δ)ᶜ := by
    have hmeas : Measurable (fun p :
        (LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) ↦
        p.1.2) := measurable_snd.comp measurable_fst
    have hh := Measure.map_apply (μ := P) hmeas hE
    rw [hproj] at hh
    exact congrArg ENNReal.toReal hh.symm
  rw [heq]
  exact N.reserveWindow_clockBudget_failure_bound d hd hU hV hVfin hUV a hδ

/-- Original retained and reserve coordinates produce the SAME finite
legal core and the genuine finite-window clock budget on its actual unused
reserve index arrays. Both original joining marginals remain exact. -/
theorem exists_original_labelled_reserve_windowCore_with_clockBudget
    {J : Type*} [Fintype J] {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 0 < q)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : IsCompact U)
    {V : Set (Fin q → ℝ)} (hV : MeasurableSet V) (hVfin : volume V ≠ ∞)
    (hUV : U ⊆ V ×ˢ univ) (cost : LegalMarkedPhysicalEdge q → ℝ)
    (a : J → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S > 0, ∃ P : ProbabilityMeasure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (P : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.fst =
        (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
          (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (P : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map Prod.snd = legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      (∀ᵐ p ∂(P : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))), IsOriginalReserveWindowCore q U cost
        (legalMarkedInputSceneDilation q c hc p.1.1)
        (legalMarkedInputSceneDilation q d hd p.1.2) p.2) ∧
      (P : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).real ((fun p ↦ p.1.2) ⁻¹'
        (legalOriginalReserveWindowClockBudgetEvent q α β d hd U a δ)ᶜ) ≤
          2 * (Fintype.card J : ℝ) * Real.sqrt (|(d ^ q)⁻¹| * (volume V).toReal) / δ := by
  obtain ⟨S, hS, P, hl, hr, hcore⟩ := exists_original_labelled_reserve_windowCore
    M N hq c d hc hd hunit hU cost
  refine ⟨S, hS, P, hl, hr, hcore, ?_⟩
  exact reserveWindow_clockBudget_failure_bound_of_original_marginal M N _ hl
    d hd hU hV hVfin hUV a hδ

/-- Strict forwardness of the SAME genuine Palm matching forces the original
closed source tail to fit into the strict target tail at every fixed cut. -/
theorem LegalWeightedStationaryPoissonMatching.sourceClock_Ici_le_targetClock_Ioi
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g) (a : ℝ) :
    α (Ici a) ≤ β (Ioi a) := by
  calc
    α (Ici a) = legalMarkedJointPalm q N.law {m | a ≤ m.1.1} := by
      have hs := congrArg (fun μ : Measure ℝ ↦ μ (Ici a)) N.source_clock
      rw [Measure.map_apply measurable_fst.fst measurableSet_Ici] at hs
      exact hs.symm
    _ ≤ legalMarkedJointPalm q N.law {m | a < m.1.2} := by
      apply measure_mono_ae
      filter_upwards [N.ae_palm_forward] with m hm
      exact fun h ↦ lt_of_le_of_lt h hm
    _ = β (Ioi a) := by
      have ht := congrArg (fun μ : Measure ℝ ↦ μ (Ioi a)) N.target_clock
      rw [Measure.map_apply measurable_fst.snd measurableSet_Ioi] at ht
      exact ht

/-- Truncating the original clock window can lose only the original target
mass outside that window. This bound follows from the genuine forward Palm
coupling and does not assume strict population slack. -/
theorem LegalWeightedStationaryPoissonMatching.truncatedClock_source_excess_le_target_tail
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A : Set ℝ} (_hA : MeasurableSet A) (a : ℝ) :
    (α (A ∩ Ici a)).toReal ≤ (β (A ∩ Ioi a)).toReal + (β Aᶜ).toReal := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have hset : Ioi a ⊆ (A ∩ Ioi a) ∪ Aᶜ := by
    intro x hx
    by_cases h : x ∈ A
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr h
  have hh : α (A ∩ Ici a) ≤ β (A ∩ Ioi a) + β Aᶜ :=
    (measure_mono inter_subset_right).trans
      ((N.sourceClock_Ici_le_targetClock_Ioi a).trans
        ((measure_mono hset).trans (measure_union_le _ _)))
  have ht : β (A ∩ Ioi a) + β Aᶜ ≠ ∞ := by finiteness
  have hreal := ENNReal.toReal_mono ht hh
  simpa only [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] using hreal

/-- The exact reserve rate of a physical product window keeps its original
spatial volume and original clock truncation factors separate. -/
theorem legalOriginalDilatedWindowMean_prod_inter_clock
    {q : ℕ} (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (d : ℝ) (V : Set (Fin q → ℝ)) (A C : Set ℝ) (c : Fin 2) :
    legalOriginalDilatedWindowMean q α β d ((V ×ˢ A) ∩ (univ ×ˢ C)) c =
      |(d ^ q)⁻¹| * (volume V).toReal * ((legalOriginalColorClock α β c) (A ∩ C)).toReal := by
  have : IsProbabilityMeasure (legalOriginalColorClock α β c) := by
    fin_cases c <;> dsimp [legalOriginalColorClock] <;> infer_instance
  have heq : (V ×ˢ A) ∩ (univ ×ˢ C) = V ×ˢ (A ∩ C) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    tauto
  rw [legalOriginalDilatedWindowMean, heq, Measure.prod_prod, ENNReal.toReal_mul]
  ring

/-- The true reserve population clock deficit inside the original physical
window is at most the omitted original target-clock mass times the true
spatial reserve volume. -/
theorem LegalWeightedStationaryPoissonMatching.reservePhysicalWindow_mean_source_excess_bound
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d R K a : ℝ) (hR : 0 ≤ R) :
    legalOriginalDilatedWindowMean q α β d
        (legalWeightedPhysicalWindow q R K ∩ (univ ×ˢ Ici a)) 0 -
      legalOriginalDilatedWindowMean q α β d
        (legalWeightedPhysicalWindow q R K ∩ (univ ×ˢ Ioi a)) 1 ≤
      (|(d ^ q)⁻¹| * (2 * R) ^ q) * (β (Icc (-K) K)ᶜ).toReal := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q N.law) := N.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← N.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← N.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have hh := N.truncatedClock_source_excess_le_target_tail
    (measurableSet_Icc : MeasurableSet (Icc (-K) K)) a
  have hr : 0 ≤ |(d ^ q)⁻¹| * (2 * R) ^ q :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) hR) q)
  have hpow : 0 ≤ (2 * R) ^ q := pow_nonneg (mul_nonneg (by norm_num) hR) q
  rw [legalWeightedPhysicalWindow,
    legalOriginalDilatedWindowMean_prod_inter_clock α β d,
    legalOriginalDilatedWindowMean_prod_inter_clock α β d,
    volume_haarRootCube (Fin q) hR, Fintype.card_fin, ENNReal.toReal_ofReal hpow]
  simp only [legalOriginalColorClock, show (1 : Fin 2) ≠ 0 from one_ne_zero, ite_true, ite_false]
  nlinarith [mul_le_mul_of_nonneg_left hh hr]

/-- Genuine original reserve inputs have only a small actual finite-list
clock shortage, including the literal target-clock truncation loss. This
probability estimate follows from the original matching class itself. -/
theorem LegalWeightedStationaryPoissonMatching.reservePhysicalWindow_clockShortage_failure_bound
    {J : Type*} [Fintype J] {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : ℝ) (hd : d ≠ 0) {R : ℝ} (hR : 0 ≤ R) (K : ℝ)
    (a : J → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (N.law : Measure (LegalMarkedOptimalInputScene q)).real {s |
      ∃ j : J, (|(d ^ q)⁻¹| * (2 * R) ^ q) * (β (Icc (-K) K)ᶜ).toReal + δ <
        legalOriginalWindowCount q (legalWeightedPhysicalWindow q R K ∩ (univ ×ˢ Ici (a j))) 0
            (legalMarkedInputSceneDilation q d hd s) -
          legalOriginalWindowCount q (legalWeightedPhysicalWindow q R K ∩ (univ ×ˢ Ioi (a j))) 1
            (legalMarkedInputSceneDilation q d hd s)} ≤
      2 * (Fintype.card J : ℝ) * Real.sqrt (|(d ^ q)⁻¹| * (2 * R) ^ q) / δ := by
  apply (measureReal_mono (μ := (N.law : Measure (LegalMarkedOptimalInputScene q)))
    (show {s | ∃ j : J,
        (|(d ^ q)⁻¹| * (2 * R) ^ q) * (β (Icc (-K) K)ᶜ).toReal + δ <
          legalOriginalWindowCount q (legalWeightedPhysicalWindow q R K ∩ (univ ×ˢ Ici (a j))) 0
              (legalMarkedInputSceneDilation q d hd s) -
            legalOriginalWindowCount q (legalWeightedPhysicalWindow q R K ∩ (univ ×ˢ Ioi (a j))) 1
              (legalMarkedInputSceneDilation q d hd s)} ⊆
        (legalOriginalReserveWindowClockBudgetEvent q α β d hd
          (legalWeightedPhysicalWindow q R K) a δ)ᶜ from ?_)).trans
      (N.reservePhysicalWindow_clockBudget_failure_bound d hd hR K a hδ)
  rintro s ⟨j, hj⟩ hgood
  have hcut := N.reservePhysicalWindow_mean_source_excess_bound d R K (a j) hR
  have hbound := hgood j
  linarith

end OTSelector.Reconstruction
