import OTSelector.Reconstruction.FinslerOriginalCanonicalSceneSimplicity
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputFiniteSimplicity

/-!
# Canonical scene full matching from plan simplicity

This module closes the remaining scene-side inputs of
FinslerOriginalCanonicalSceneSimplicity and combines everything into the a.e.
full-matching condition for the canonical scene.

1. **restrict_finsetSum_measure / dirac_restrict_of_mem**: elementary measure
   algebra (restriction distributes over finite measure sums; a dirac restricted
   to a set containing its point is the dirac).
2. **isLegalSimpleCountingMeasure_canonicalInputMeasure**: the canonical input
   measure is simple, given pointwise plan simplicity.  The coloured input atoms
   are (matched source point, colour 0) and (matched target point, colour 1);
   cross-colour atoms differ by the Fin 2 coordinate, and same-colour atoms are
   pairwise distinct by plan simplicity.  The finite injective enumeration lemma
   isLegalSimpleCountingMeasure_of_injective_fintype is applied to
   Sum.elim source target.
3. **canonicalPlanMeasure_fst / snd**: the colour marginals of the canonical plan
   measure are the finite dirac sums over the matched source (resp. target)
   physical points (Measure.map_finset_sum + Measure.map_dirac).
4. **legalInputColorMeasure_canonicalInputMeasure**: the same finite dirac sums
   for the canonical input measure, using restrict_finsetSum_measure and
   dirac_restrict_of_mem (colour-1 atoms are killed by the colour-0 restriction
   and vice versa).
5. **canonicalScene_marginals**: hm, the two colour marginal identities,
   unconditionally in the cloud state.
6. **isLegalCountingMeasure_canonicalScene**: hc, unconditional, from
   canonicalPlanConfig_spec.
7. **isFullOriginalInputMatching_canonicalScene_of_simplicity**: the full
   matching from plan simplicity, via
   isFullOriginalInputMatching_of_counting_simple_marginals.
8. **ae_canonicalSceneFullMatching**: a.e. full matching under twoMarkedCloudLaw
   for q >= 1 and L != 0, using ae_canonicalScenePlanSimplicity.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

local instance canonicalSceneFullMatchingColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {q : ℕ} {L r : ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {t : ℝ}

/-- Restriction distributes over a finite sum of measures. -/
theorem restrict_finsetSum_measure {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (m : ι → Measure α) (U : Set α) :
    (∑ i ∈ s, m i).restrict U = ∑ i ∈ s, (m i).restrict U := by
  ext V hV
  simp only [Measure.finsetSum_apply, Measure.restrict_apply hV]

/-- A dirac restricted to a measurable set containing its point is the dirac. -/
theorem dirac_restrict_of_mem {α : Type*} [MeasurableSpace α] {a : α} {U : Set α}
    (hU : MeasurableSet U) (ha : a ∈ U) :
    (Measure.dirac a).restrict U = Measure.dirac a := by
  ext V hV
  rw [Measure.restrict_apply hV, Measure.dirac_apply' _ (hV.inter hU),
    Measure.dirac_apply' _ hV]
  by_cases h : a ∈ V <;> simp [h, ha]

/-- A dirac restricted to a measurable set not containing its point is zero. -/
theorem dirac_restrict_of_notMem {α : Type*} [MeasurableSpace α] {a : α} {U : Set α}
    (hU : MeasurableSet U) (ha : a ∉ U) :
    (Measure.dirac a).restrict U = 0 := by
  ext V hV
  rw [Measure.restrict_apply hV, Measure.dirac_apply' _ (hV.inter hU)]
  change (V ∩ U).indicator (1 : α → ℝ≥0∞) a = 0
  have h' : a ∉ V ∩ U := fun hvu => ha hvu.2
  rw [Set.indicator_of_notMem h']

/-- The measurable set of coloured input points with a fixed colour. -/
theorem measurableSet_inputColor (c : Fin 2) :
    MeasurableSet {x : LegalColoredInputPoint q | x.2 = c} :=
  measurable_snd (measurableSet_singleton c)

/-- **The canonical input measure is simple** given pointwise plan simplicity. -/
theorem isLegalSimpleCountingMeasure_canonicalInputMeasure
    (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hsimple : CanonicalScenePlanSimplicity q L r kin g t ω) :
    IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
      (canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω) := by
  classical
  let s := canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω
  let f : s ⊕ s → LegalColoredInputPoint q :=
    Sum.elim
      (fun e => ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e.1).1,
        (0 : Fin 2)))
      (fun e => ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e.1).2,
        (1 : Fin 2)))
  have hf : Injective f := by
    rintro (a | a) (b | b) hab
    · have h1 : (canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω
          a.1).1 =
          (canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω b.1).1 := by
        simpa [f] using congrArg Prod.fst hab
      exact congrArg Sum.inl (hsimple.1 h1)
    · have hc := congrArg Prod.snd hab
      simp [f] at hc
    · have hc := congrArg Prod.snd hab
      simp [f] at hc
    · have h2 : (canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω
          a.1).2 =
          (canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω b.1).2 := by
        simpa [f] using congrArg Prod.fst hab
      exact congrArg Sum.inr (hsimple.2 h2)
  have h := isLegalSimpleCountingMeasure_of_injective_fintype
    (0 : LegalColoredInputPoint q) f hf
  have heq : (⟨∑ i, Measure.dirac (f i), inferInstance⟩ :
        LocalFiniteMeasure (LegalColoredInputPoint q)) =
      canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω := by
    apply Subtype.ext
    simp only [canonicalInputMeasure]
    rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
    have hX : (∑ a : ↥s, Measure.dirac (f (Sum.inl a))) =
        ∑ e ∈ s, Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
            (0 : Fin 2)) := by
      rw [← Finset.sum_coe_sort s (fun e => Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
          (0 : Fin 2)))]
      exact Finset.sum_congr rfl (fun a _ => by simp [f])
    have hY : (∑ a : ↥s, Measure.dirac (f (Sum.inr a))) =
        ∑ e ∈ s, Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
            (1 : Fin 2)) := by
      rw [← Finset.sum_coe_sort s (fun e => Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
          (1 : Fin 2)))]
      exact Finset.sum_congr rfl (fun a _ => by simp [f])
    rw [hX, hY]
    rw [Finset.sum_coe_sort s (fun e => Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
          (0 : Fin 2))),
      Finset.sum_coe_sort s (fun e => Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
          (1 : Fin 2)))]
  rwa [heq] at h

/-- The colour-0 marginal of the canonical plan measure is the finite dirac sum
over the matched source physical points. -/
theorem canonicalPlanMeasure_fst (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ((canonicalScene q L r kin g t ω).1.1 :
        Measure (LegalMarkedPhysicalEdge q)).fst =
      ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1) := by
  rw [Measure.fst]
  change (legalMarkedOptimalPlan q L r kin g t ω).map Prod.fst =
    ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
      Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1)
  rw [legalMarkedOptimalPlan]
  simp only [legalMarkedFixedOptimalPlan, canonicalPlanEdges, canonicalPlanPoints]
  rw [Measure.map_finset_sum (Measurable.aemeasurable measurable_fst)]
  simp only [Measure.map_dirac]

/-- The colour-1 input marginal of the canonical input measure is the finite dirac
sum over the matched target physical points. -/
theorem legalInputColorMeasure_canonicalInputMeasure_one
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalInputColorMeasure q
        (canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω) 1 =
      ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2) := by
  rw [legalInputColorMeasure]
  have hU : MeasurableSet {x : LegalColoredInputPoint q | x.2 = (1 : Fin 2)} :=
    measurableSet_inputColor 1
  have hin : ((canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω :
        Measure (LegalColoredInputPoint q))) =
      ∑ e : ↥(canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω),
        (Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω ↑e).1,
              (0 : Fin 2)) +
          Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω ↑e).2,
              (1 : Fin 2))) := rfl
  rw [hin,
    Finset.sum_coe_sort (canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω)
      (fun e => (Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
              (0 : Fin 2)) +
          Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
              (1 : Fin 2)))),
    restrict_finsetSum_measure]
  have hterm : ∀ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
      (Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
            (0 : Fin 2)) +
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
            (1 : Fin 2))).restrict {x : LegalColoredInputPoint q | x.2 = (1 : Fin 2)} =
      Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
          (1 : Fin 2)) := by
    intro e _
    rw [Measure.restrict_add,
      dirac_restrict_of_notMem hU (by simp),
      dirac_restrict_of_mem hU (by simp), zero_add]
  rw [show (∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        (Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
              (0 : Fin 2)) +
          Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
              (1 : Fin 2))).restrict {x : LegalColoredInputPoint q | x.2 = (1 : Fin 2)}) =
      ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
            (1 : Fin 2)) from Finset.sum_congr rfl hterm]
  rw [Measure.map_finset_sum (Measurable.aemeasurable measurable_fst)]
  simp only [Measure.map_dirac]

/-- The colour-1 marginal of the canonical plan measure is the finite dirac sum
over the matched target physical points. -/
theorem canonicalPlanMeasure_snd (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ((canonicalScene q L r kin g t ω).1.1 :
        Measure (LegalMarkedPhysicalEdge q)).snd =
      ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2) := by
  rw [Measure.snd]
  change (legalMarkedOptimalPlan q L r kin g t ω).map Prod.snd =
    ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
      Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2)
  rw [legalMarkedOptimalPlan]
  simp only [legalMarkedFixedOptimalPlan, canonicalPlanEdges, canonicalPlanPoints]
  rw [Measure.map_finset_sum (Measurable.aemeasurable measurable_snd)]
  simp only [Measure.map_dirac]

/-- The colour-0 input marginal of the canonical input measure is the finite dirac
sum over the matched source physical points. -/
theorem legalInputColorMeasure_canonicalInputMeasure_zero
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    legalInputColorMeasure q
        (canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω) 0 =
      ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1) := by
  rw [legalInputColorMeasure]
  have hU : MeasurableSet {x : LegalColoredInputPoint q | x.2 = (0 : Fin 2)} :=
    measurableSet_inputColor 0
  have hin : ((canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω :
        Measure (LegalColoredInputPoint q))) =
      ∑ e : ↥(canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω),
        (Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω ↑e).1,
              (0 : Fin 2)) +
          Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω ↑e).2,
              (1 : Fin 2))) := rfl
  rw [hin,
    Finset.sum_coe_sort (canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω)
      (fun e => (Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
              (0 : Fin 2)) +
          Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
              (1 : Fin 2)))),
    restrict_finsetSum_measure]
  have hterm : ∀ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
      (Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
            (0 : Fin 2)) +
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
            (1 : Fin 2))).restrict {x : LegalColoredInputPoint q | x.2 = (0 : Fin 2)} =
      Measure.dirac
        ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
          (0 : Fin 2)) := by
    intro e _
    rw [Measure.restrict_add,
      dirac_restrict_of_mem hU (by simp),
      dirac_restrict_of_notMem hU (by simp), add_zero]
  rw [show (∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        (Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
              (0 : Fin 2)) +
          Measure.dirac
            ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).2,
              (1 : Fin 2))).restrict {x : LegalColoredInputPoint q | x.2 = (0 : Fin 2)}) =
      ∑ e ∈ canonicalPlanEdges q (mSourceCount ω) (mTargetCount ω) L r kin g t ω,
        Measure.dirac
          ((canonicalPlanPoints q (mSourceCount ω) (mTargetCount ω) L r kin g t ω e).1,
            (0 : Fin 2)) from Finset.sum_congr rfl hterm]
  rw [Measure.map_finset_sum (Measurable.aemeasurable measurable_fst)]
  simp only [Measure.map_dirac]

/-- **hc**: the canonical edge measure is an integer counting measure. -/
theorem isLegalCountingMeasure_canonicalScene (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)
      (canonicalScene q L r kin g t ω).1.1 := by
  refine ⟨canonicalPlanConfig q (mSourceCount ω) (mTargetCount ω) L r kin g t ω, ?_⟩
  apply Subtype.ext
  change LocalConfiguration.countingMeasure
      (canonicalPlanConfig q (mSourceCount ω) (mTargetCount ω) L r kin g t ω) =
    legalMarkedOptimalPlan q L r kin g t ω
  rw [canonicalPlanConfig_spec]
  rfl

/-- **hm**: the two colour marginal identities of the canonical scene. -/
theorem canonicalScene_marginals (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).fst =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 0 ∧
      ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).snd =
        legalInputColorMeasure q (canonicalScene q L r kin g t ω).2 1 := by
  constructor
  · change ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).fst =
        legalInputColorMeasure q
          (canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω) 0
    rw [canonicalPlanMeasure_fst, legalInputColorMeasure_canonicalInputMeasure_zero]
  · change ((canonicalScene q L r kin g t ω).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).snd =
        legalInputColorMeasure q
          (canonicalInputMeasure q (mSourceCount ω) (mTargetCount ω) L r kin g t ω) 1
    rw [canonicalPlanMeasure_snd, legalInputColorMeasure_canonicalInputMeasure_one]

/-- **The canonical scene full matching from pointwise plan simplicity.** -/
theorem isFullOriginalInputMatching_canonicalScene_of_simplicity
    (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hsimple : CanonicalScenePlanSimplicity q L r kin g t ω) :
    CanonicalSceneFullMatching q L r kin g t ω :=
  canonicalScene_fullMatching_of_components q L r kin g t ω
    (isLegalCountingMeasure_canonicalScene ω)
    (isLegalSimpleCountingMeasure_canonicalInputMeasure ω hsimple)
    (canonicalScene_marginals ω)

/-- **A.e. canonical scene full matching**, unconditionally for q >= 1 and
nonzero spatial scale: this is the hypothesis consumed by
ae_canonicalScene_transport_of_ae_fullMatching. -/
theorem ae_canonicalSceneFullMatching (hq : 0 < q) (hL : L ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      CanonicalSceneFullMatching q L r kin g t ω := by
  filter_upwards [ae_canonicalScenePlanSimplicity (q := q) (L := L) (r := r)
    (kin := kin) (g := g) (t := t) hq hL α β ρ] with ω hsimple
  exact isFullOriginalInputMatching_canonicalScene_of_simplicity ω hsimple

end OTSelector.Reconstruction
