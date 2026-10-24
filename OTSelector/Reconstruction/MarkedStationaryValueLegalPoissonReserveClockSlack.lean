import OTSelector.Reconstruction.MarkedStationaryValueLegalPoisson
import OTSelector.Probability.PoissonPrefixMoments
import OTSelector.Probability.PoissonSingleDeviation
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Original Poisson reserve clocks produce actual finite prefix slack

Every count reads only the used original finite prefix. A two-valued readout
of the original clocks supplies its exact thinned Poisson law; no selected
orphan cloud is assigned any law. Strict original mass slack at fixed finite
thresholds yields simultaneous realized clock slack with probability tending
to one.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Count exactly the original used observations whose scalar clock belongs
to the selected set, retaining the original position and clock observations. -/
def originalReserveClockCount (q : ℕ) (U : Set ℝ) (z : MarkedCloudSpace q ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin z.1 ↦ (z.2 i).2 ∈ U)).card

private def reserveClockTag (U : Set ℝ) (a : ℝ) : Fin 2 :=
  if a ∈ U then 0 else 1

private theorem measurable_reserveClockTag {U : Set ℝ} (hU : MeasurableSet U) :
    Measurable (reserveClockTag U) :=
  measurable_const.ite hU measurable_const

private theorem originalReserveClockCount_eq_typeCount (q : ℕ) (U : Set ℝ)
    (z : MarkedCloudSpace q ℝ) :
    originalReserveClockCount q U z = poissonTypeCount (markedTypeCloud (reserveClockTag U) z) 0 := by
  unfold originalReserveClockCount poissonTypeCount
  congr 1
  ext i
  simp [markedTypeCloud, reserveClockTag]

/-- The original used-prefix clock count is measurable before selecting any
core matching or orphan endpoints. -/
theorem measurable_originalReserveClockCount (q : ℕ) {U : Set ℝ} (hU : MeasurableSet U) :
    Measurable (originalReserveClockCount q U) := by
  have h := ((measurable_pi_apply (0 : Fin 2)).comp
    (measurable_poissonTypeCount (T := Fin 2))).comp
      (measurable_markedTypeCloud (q := q) (measurable_reserveClockTag hU))
  simpa only [Function.comp_def, ← originalReserveClockCount_eq_typeCount] using h

/-- Thinning is proved on the literal original prefix, giving its exact
Poisson count law with the unchanged original scalar mass. -/
theorem map_originalReserveClockCount (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (r : ℝ≥0) {U : Set ℝ} (hU : MeasurableSet U) :
    (markedPoissonLaw q ℝ α r).map (originalReserveClockCount q U) =
      poissonMeasure (r * (α U).toNNReal) := by
  let tag := reserveClockTag U
  let L := α.map tag
  have htag : Measurable tag := measurable_reserveClockTag hU
  have : IsProbabilityMeasure L := Measure.isProbabilityMeasure_map htag.aemeasurable
  have hmass : L {(0 : Fin 2)} = α U := by
    rw [show L = α.map tag from rfl, Measure.map_apply htag (measurableSet_singleton _)]
    congr 1
    ext a
    simp [tag, reserveClockTag]
  have hcounts : (markedPoissonLaw q ℝ α r).map
      (fun z ↦ poissonTypeCount (markedTypeCloud tag z)) =
        Measure.pi (fun b : Fin 2 ↦ poissonMeasure (r * (L {b}).toNNReal)) := by
    change (markedPoissonLaw q ℝ α r).map (poissonTypeCount ∘ markedTypeCloud tag) = _
    rw [← Measure.map_map measurable_poissonTypeCount (measurable_markedTypeCloud htag),
      map_markedPoissonLaw_types q α htag r]
    exact map_poissonTypeCount L r
  have h := congrArg (fun μ : Measure (Fin 2 → ℕ) ↦ μ.map (Function.eval (0 : Fin 2))) hcounts
  have hev := (measurePreserving_eval
    (μ := fun b : Fin 2 ↦ poissonMeasure (r * (L {b}).toNNReal)) (0 : Fin 2)).map_eq
  rw [Measure.map_map (measurable_pi_apply _) (by
    exact measurable_poissonTypeCount.comp (measurable_markedTypeCloud htag)), hev, hmass] at h
  simpa only [Function.comp_def, tag, ← originalReserveClockCount_eq_typeCount] using h

/-- Actual prefix count integrability follows from its actual Poisson law. -/
theorem originalReserveClockCount_deviation_integrable_bound
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] (r : ℝ≥0)
    {U : Set ℝ} (hU : MeasurableSet U) :
    Integrable (fun z ↦ |(originalReserveClockCount q U z : ℝ) - (r : ℝ) * (α U).toReal|)
      (markedPoissonLaw q ℝ α r) ∧
      (∫ z, |(originalReserveClockCount q U z : ℝ) - (r : ℝ) * (α U).toReal|
        ∂markedPoissonLaw q ℝ α r) ≤ Real.sqrt (r : ℝ) := by
  let rate := r * (α U).toNNReal
  have hrate : (rate : ℝ) = (r : ℝ) * (α U).toReal := rfl
  have hmap := map_originalReserveClockCount q α r hU
  have hcount := measurable_originalReserveClockCount q hU
  have hI : Integrable (fun n : ℕ ↦ |(n : ℝ) - (rate : ℝ)|) (poissonMeasure rate) :=
    ((integrable_id_poissonMeasure rate).sub (integrable_const (rate : ℝ))).abs
  have hI' : Integrable (fun n : ℕ ↦ |(n : ℝ) - (rate : ℝ)|)
      ((markedPoissonLaw q ℝ α r).map (originalReserveClockCount q U)) := by
    rw [hmap]
    exact hI
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, hrate] using hI'.comp_measurable hcount
  · have heq := integral_map hcount.aemeasurable hI'.aestronglyMeasurable
    have hrle : (rate : ℝ) ≤ (r : ℝ) := by
      have hm : (α U).toReal ≤ 1 := by
        exact (ENNReal.toReal_mono (by simp) (show α U ≤ 1 from
          (measure_mono (subset_univ _)).trans_eq measure_univ)).trans_eq (by simp)
      rw [hrate]
      exact mul_le_of_le_one_right r.coe_nonneg hm
    calc
      _ = ∫ n : ℕ, |(n : ℝ) - (rate : ℝ)| ∂poissonMeasure rate := by
        rw [← hmap]
        simpa only [Function.comp_def, hrate] using heq.symm
      _ ≤ Real.sqrt (rate : ℝ) := integral_abs_sub_id_poissonMeasure_le rate
      _ ≤ Real.sqrt (r : ℝ) := Real.sqrt_le_sqrt hrle

/-- Total absolute clock count deviation on the unchanged original two-color
cloud, at the fixed finite list of reserve thresholds. -/
def originalReserveClockDeviation {J : Type*} [Fintype J] (q : ℕ)
    (α β : Measure ℝ) (r : ℝ≥0) (c : J → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  ∑ j : J,
    (|(originalReserveClockCount q (Ici (c j)) ω.1 : ℝ) - (r : ℝ) * (α (Ici (c j))).toReal| +
      |(originalReserveClockCount q (Ioi (c j)) ω.2 : ℝ) - (r : ℝ) * (β (Ioi (c j))).toReal|)

/-- The actual reserve clock inequalities hold at every fixed threshold. -/
def originalReserveClockSlackEvent {J : Type*} [Fintype J] (q : ℕ)
    (r : ℝ≥0) (η : ℝ) (c : J → ℝ) : Set (TwoMarkedCloudSpace q ℝ ℝ) :=
  {ω | ∀ j : J, (r : ℝ) * η / 2 ≤
    (originalReserveClockCount q (Ioi (c j)) ω.2 : ℝ) -
      (originalReserveClockCount q (Ici (c j)) ω.1 : ℝ)}

theorem originalReserveClockDeviation_nonneg {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) (r : ℝ≥0) (c : J → ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : 0 ≤ originalReserveClockDeviation q α β r c ω :=
  Finset.sum_nonneg (fun _ _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The simultaneous actual count slack event is measurable on the original
random experiment, before inspecting any orphan endpoints. -/
theorem measurableSet_originalReserveClockSlackEvent {J : Type*} [Fintype J]
    (q : ℕ) (r : ℝ≥0) (η : ℝ) (c : J → ℝ) :
    MeasurableSet (originalReserveClockSlackEvent q r η c) := by
  have hm (j : J) : MeasurableSet {ω : TwoMarkedCloudSpace q ℝ ℝ |
      (r : ℝ) * η / 2 ≤ (originalReserveClockCount q (Ioi (c j)) ω.2 : ℝ) -
        (originalReserveClockCount q (Ici (c j)) ω.1 : ℝ)} :=
    measurableSet_le measurable_const
      ((measurable_from_nat.comp ((measurable_originalReserveClockCount q measurableSet_Ioi).comp
        measurable_snd)).sub (measurable_from_nat.comp
          ((measurable_originalReserveClockCount q measurableSet_Ici).comp measurable_fst)))
  simpa only [originalReserveClockSlackEvent, Set.ofPred_forall] using MeasurableSet.iInter hm

/-- The actual original finite threshold error is integrable and of square-root
order. No independence property of any later selected endpoints is used. -/
theorem originalReserveClockDeviation_integrable_bound {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) (c : J → ℝ) :
    Integrable (originalReserveClockDeviation q α β r c) (twoMarkedCloudLaw q ℝ ℝ α β r) ∧
      (∫ ω, originalReserveClockDeviation q α β r c ω ∂twoMarkedCloudLaw q ℝ ℝ α β r) ≤
        2 * (Fintype.card J : ℝ) * Real.sqrt (r : ℝ) := by
  have hα (j : J) := originalReserveClockCount_deviation_integrable_bound q α r
    (U := Ici (c j)) measurableSet_Ici
  have hβ (j : J) := originalReserveClockCount_deviation_integrable_bound q β r
    (U := Ioi (c j)) measurableSet_Ioi
  have hI (j : J) : Integrable (fun ω : TwoMarkedCloudSpace q ℝ ℝ ↦
      |(originalReserveClockCount q (Ici (c j)) ω.1 : ℝ) - (r : ℝ) * (α (Ici (c j))).toReal| +
        |(originalReserveClockCount q (Ioi (c j)) ω.2 : ℝ) - (r : ℝ) * (β (Ioi (c j))).toReal|)
      (twoMarkedCloudLaw q ℝ ℝ α β r) :=
    ((hα j).1.comp_fst (markedPoissonLaw q ℝ β r)).add
      ((hβ j).1.comp_snd (markedPoissonLaw q ℝ α r))
  have hB (j : J) : (∫ ω : TwoMarkedCloudSpace q ℝ ℝ,
      |(originalReserveClockCount q (Ici (c j)) ω.1 : ℝ) - (r : ℝ) * (α (Ici (c j))).toReal| +
        |(originalReserveClockCount q (Ioi (c j)) ω.2 : ℝ) - (r : ℝ) * (β (Ioi (c j))).toReal|
      ∂twoMarkedCloudLaw q ℝ ℝ α β r) ≤ 2 * Real.sqrt (r : ℝ) := by
    unfold twoMarkedCloudLaw
    rw [integral_add ((hα j).1.comp_fst _) ((hβ j).1.comp_snd _)]
    change (∫ ω, _ ∂(markedPoissonLaw q ℝ α r).prod (markedPoissonLaw q ℝ β r)) +
      (∫ ω, _ ∂(markedPoissonLaw q ℝ α r).prod (markedPoissonLaw q ℝ β r)) ≤ _
    rw [integral_fun_fst (fun z : MarkedCloudSpace q ℝ ↦
      |(originalReserveClockCount q (Ici (c j)) z : ℝ) - (r : ℝ) * (α (Ici (c j))).toReal|),
      integral_fun_snd (fun z : MarkedCloudSpace q ℝ ↦
        |(originalReserveClockCount q (Ioi (c j)) z : ℝ) - (r : ℝ) * (β (Ioi (c j))).toReal|)]
    simp only [probReal_univ, one_smul]
    linarith [(hα j).2, (hβ j).2]
  refine ⟨integrable_finsetSum _ (fun j _ ↦ hI j), ?_⟩
  unfold originalReserveClockDeviation
  rw [integral_finsetSum _ (fun j _ ↦ hI j)]
  exact (Finset.sum_le_sum (fun j _ ↦ hB j)).trans_eq (by simp; ring)

/-- Original mass slack forces every failed simultaneous clock event to have
a large actual original finite-prefix counting error. -/
theorem originalReserveClockSlackEvent_compl_subset_deviation
    {J : Type*} [Fintype J] (q : ℕ) (α β : Measure ℝ) (r : ℝ≥0)
    (η : ℝ) (c : J → ℝ)
    (hslack : ∀ j, (α (Ici (c j))).toReal + η ≤ (β (Ioi (c j))).toReal) :
    (originalReserveClockSlackEvent q r η c)ᶜ ⊆
      {ω | (r : ℝ) * η / 2 ≤ originalReserveClockDeviation q α β r c ω} := by
  intro ω hω
  obtain ⟨j, hj⟩ := not_forall.mp hω
  have hm := mul_le_mul_of_nonneg_left (hslack j) r.coe_nonneg
  have hα := le_abs_self ((originalReserveClockCount q (Ici (c j)) ω.1 : ℝ) -
    (r : ℝ) * (α (Ici (c j))).toReal)
  have hβ := neg_le_abs ((originalReserveClockCount q (Ioi (c j)) ω.2 : ℝ) -
    (r : ℝ) * (β (Ioi (c j))).toReal)
  have hs :
      |(originalReserveClockCount q (Ici (c j)) ω.1 : ℝ) - (r : ℝ) * (α (Ici (c j))).toReal| +
        |(originalReserveClockCount q (Ioi (c j)) ω.2 : ℝ) - (r : ℝ) * (β (Ioi (c j))).toReal| ≤
      originalReserveClockDeviation q α β r c ω :=
    Finset.single_le_sum (f := fun k : J ↦
      |(originalReserveClockCount q (Ici (c k)) ω.1 : ℝ) - (r : ℝ) * (α (Ici (c k))).toReal| +
        |(originalReserveClockCount q (Ioi (c k)) ω.2 : ℝ) - (r : ℝ) * (β (Ioi (c k))).toReal|)
      (fun _ _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
  change (r : ℝ) * η / 2 ≤ originalReserveClockDeviation q α β r c ω
  have hj' := lt_of_not_ge hj
  nlinarith

/-- Literal original Poisson reserve inputs satisfy all finite clock slack
inequalities except on a set of probability at most a constant over sqrt r. -/
theorem originalReserveClockSlack_failure_bound {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (r : ℝ≥0) (hr : 0 < r) {η : ℝ} (hη : 0 < η) (c : J → ℝ)
    (hslack : ∀ j, (α (Ici (c j))).toReal + η ≤ (β (Ioi (c j))).toReal) :
    (twoMarkedCloudLaw q ℝ ℝ α β r).real (originalReserveClockSlackEvent q r η c)ᶜ ≤
      4 * (Fintype.card J : ℝ) / (η * Real.sqrt (r : ℝ)) := by
  let P := twoMarkedCloudLaw q ℝ ℝ α β r
  let t : ℝ := (r : ℝ) * η / 2
  have hrR : 0 < (r : ℝ) := hr
  have ht : 0 < t := by positivity
  obtain ⟨hI, hB⟩ := originalReserveClockDeviation_integrable_bound q α β r c
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (.of_forall (originalReserveClockDeviation_nonneg q α β r c)) hI t
  have hsub := originalReserveClockSlackEvent_compl_subset_deviation q α β r η c hslack
  have hprob : P.real (originalReserveClockSlackEvent q r η c)ᶜ ≤
      P.real {ω | t ≤ originalReserveClockDeviation q α β r c ω} := measureReal_mono hsub
  have hraw : P.real (originalReserveClockSlackEvent q r η c)ᶜ ≤
      (2 * (Fintype.card J : ℝ) * Real.sqrt (r : ℝ)) / t := by
    apply (le_div_iff₀ ht).mpr
    calc
      _ ≤ t * P.real {ω | t ≤ originalReserveClockDeviation q α β r c ω} := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprob ht.le
      _ ≤ _ := hmark.trans hB
  apply hraw.trans_eq
  have hspos := Real.sqrt_pos.2 hrR
  have hs := Real.sq_sqrt hrR.le
  dsimp [t]
  field_simp
  nlinarith

/-- At increasing natural intensities all fixed original finite reserve
clock inequalities hold with probability tending to one. -/
theorem tendsto_originalReserveClockSlack_probability_one {J : Type*} [Fintype J]
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {η : ℝ} (hη : 0 < η) (c : J → ℝ)
    (hslack : ∀ j, (α (Ici (c j))).toReal + η ≤ (β (Ioi (c j))).toReal) :
    Tendsto (fun n : ℕ ↦ (twoMarkedCloudLaw q ℝ ℝ α β (n + 1 : ℝ≥0)).real
      (originalReserveClockSlackEvent q (n + 1 : ℝ≥0) η c)) atTop (𝓝 1) := by
  have hrate : Tendsto (fun n : ℕ ↦ ((n + 1 : ℝ≥0) : ℝ)) atTop atTop := by
    simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb : Tendsto (fun n : ℕ ↦ 4 * (Fintype.card J : ℝ) /
      (η * Real.sqrt ((n + 1 : ℝ≥0) : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 4 * (Fintype.card J : ℝ) / η)).mul
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hrate))
    simpa only [Function.comp_def, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm,
      mul_comm, mul_zero, zero_mul] using h
  have hfail : Tendsto (fun n : ℕ ↦ (twoMarkedCloudLaw q ℝ ℝ α β (n + 1 : ℝ≥0)).real
      (originalReserveClockSlackEvent q (n + 1 : ℝ≥0) η c)ᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ ↦ ENNReal.toReal_nonneg)
    intro n
    exact originalReserveClockSlack_failure_bound q α β (n + 1 : ℝ≥0) (by positivity) hη c hslack
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hfail
  have h' : Tendsto (fun n : ℕ ↦ 1 - (twoMarkedCloudLaw q ℝ ℝ α β (n + 1 : ℝ≥0)).real
      (originalReserveClockSlackEvent q (n + 1 : ℝ≥0) η c)ᶜ) atTop (𝓝 1) := by
    simpa only [sub_zero] using h
  refine h'.congr' (Filter.Eventually.of_forall (fun n ↦ ?_))
  rw [probReal_compl_eq_one_sub (measurableSet_originalReserveClockSlackEvent q _ η c),
    sub_sub_cancel]

end OTSelector.Reconstruction
