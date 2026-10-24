import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputIntensity
import OTSelector.MeasureTheory.MeasurableLocalMeasureEquality

/-!
# Canonical scene representatives retain the actual first matching and inputs

The matching class constrains only its first edge measure. Its second edge
slot is an unused formal coordinate and does not enter its genuine Palm or
value. Duplicating the first measure into that slot preserves the complete
actual matching/input law and gives a representative suitable for compactness.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
local instance canonicalFirstInputColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance canonicalFirstInputInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance canonicalFirstInputPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Discard only the unused second edge slot; the actual first matching and
complete colored input measure remain pointwise unchanged. -/
def legalMarkedCanonicalFirstInputScene (q : ℕ) (s : LegalMarkedOptimalInputScene q) :
    LegalMarkedOptimalInputScene q := ((s.1.1, s.1.1), s.2)

theorem continuous_legalMarkedCanonicalFirstInputScene (q : ℕ) :
    Continuous (legalMarkedCanonicalFirstInputScene q) :=
  (continuous_fst.fst.prodMk continuous_fst.fst).prodMk continuous_snd

/-- The actual same first matching/input law on the canonical joint carrier. -/
def legalMarkedCanonicalFirstInputLaw (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  Q.map (continuous_legalMarkedCanonicalFirstInputScene q).measurable.aemeasurable

/-- The complete first-matching/input joint law is unchanged, including all
correlations and every original clock and immutable input color. -/
theorem map_canonicalFirstInputLaw_first_input (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    (legalMarkedCanonicalFirstInputLaw q Q : Measure (LegalMarkedOptimalInputScene q)).map
      (fun s ↦ (s.1.1, s.2)) =
    (Q : Measure (LegalMarkedOptimalInputScene q)).map (fun s ↦ (s.1.1, s.2)) := by
  change ((Q : Measure (LegalMarkedOptimalInputScene q)).map (legalMarkedCanonicalFirstInputScene q)).map _ = _
  rw [Measure.map_map (measurable_fst.fst.prodMk measurable_snd)
    (continuous_legalMarkedCanonicalFirstInputScene q).measurable]
  rfl

/-- The original true source-anchored Palm does not use the discarded slot. -/
theorem legalMarkedJointPalm_canonicalFirstInputLaw (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    legalMarkedJointPalm q (legalMarkedCanonicalFirstInputLaw q Q) =
      legalMarkedJointPalm q Q := by
  unfold legalMarkedJointPalm
  congr 1
  apply Measure.ext
  intro B hB
  simp only [physicalScenePairCampbell, Measure.bind_apply hB
    (Kernel.measurable _).aemeasurable]
  change (∫⁻ scene, physicalScenePairKernel scene B
    ∂((Q : Measure (LegalMarkedOptimalInputScene q)).map
      (legalMarkedCanonicalFirstInputScene q)).map Prod.fst) =
    ∫⁻ scene, physicalScenePairKernel scene B
      ∂(Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.fst
  rw [lintegral_map (Kernel.measurable_coe _ hB) measurable_fst,
    lintegral_map (Kernel.measurable_coe _ hB) measurable_fst]
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      physicalScenePairKernel s.1 B) := (Kernel.measurable_coe _ hB).comp measurable_fst
  rw [lintegral_map hm (continuous_legalMarkedCanonicalFirstInputScene q).measurable]
  apply lintegral_congr
  intro s
  rw [physicalScenePairKernel_apply, physicalScenePairKernel_apply]
  rfl

/-- The full original integer matching assertion is a Borel event. Its
apparently quantified partner fields follow from integer simple marginals. -/
theorem measurableSet_isFullOriginalInputMatching (q : ℕ) :
    MeasurableSet {s : LegalMarkedOptimalInputScene q | IsFullOriginalInputMatching q s} := by
  have hsrc : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst) :=
    (Measure.measurable_map Prod.fst measurable_fst).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  have htgt : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd) :=
    (Measure.measurable_map Prod.snd measurable_snd).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  have hc (c : Fin 2) : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      legalInputColorMeasure q s.2 c) := by
    convert (Kernel.measurable (legalMarkedInputColorKernel q c)) using 1
    funext s
    exact (legalMarkedInputColorKernel_apply q c s).symm
  let lc (c : Fin 2) (s : LegalMarkedOptimalInputScene q) :
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q) :=
    ⟨legalInputColorMeasure q s.2 c, inferInstance⟩
  have hlc (c : Fin 2) : Measurable (lc c) :=
    measurable_localFiniteMeasure_of_measurable_measure (lc c) (hc c)
  have he : {s : LegalMarkedOptimalInputScene q | IsFullOriginalInputMatching q s} =
      {s | IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) s.1.1} ∩
      ({s | IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) s.2} ∩
      ({s | (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst = legalInputColorMeasure q s.2 0} ∩
      {s | (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd = legalInputColorMeasure q s.2 1})) := by
    ext s
    constructor
    · intro hs
      exact ⟨((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1,
        hs.simple_inputs, hs.source_marginal, hs.target_marginal⟩
    · rintro ⟨he, hi, hs, ht⟩
      exact isFullOriginalInputMatching_of_counting_simple_marginals q s he hi ⟨hs, ht⟩
  rw [he]
  apply ((isClosed_isLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q)).measurableSet.preimage
    measurable_fst.fst).inter
  apply ((measurableSet_isLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)).preimage
    measurable_snd).inter
  exact (measurableSet_measure_eq_localFiniteMeasure _ hsrc (lc 0) (hlc 0)).inter
    (measurableSet_measure_eq_localFiniteMeasure _ htgt (lc 1) (hlc 1))

/-- Canonical representatives preserve the actual joint reroot exactly. -/
theorem legalMarkedCanonicalFirstInputScene_commute_reroot (q : ℕ) (v : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) :
    legalMarkedCanonicalFirstInputScene q (legalMarkedInputSceneReroot q v s) =
      legalMarkedInputSceneReroot q v (legalMarkedCanonicalFirstInputScene q s) := rfl

/-- The original canonical representative remains jointly stationary. -/
theorem measurePreserving_canonicalFirstInputLaw_reroot
    {q : ℕ} (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hQ : ∀ v, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q))
      (Q : Measure (LegalMarkedOptimalInputScene q))) (v : Fin q → ℝ) :
    MeasurePreserving (legalMarkedInputSceneReroot q v)
      (legalMarkedCanonicalFirstInputLaw q Q : Measure (LegalMarkedOptimalInputScene q))
      (legalMarkedCanonicalFirstInputLaw q Q : Measure (LegalMarkedOptimalInputScene q)) := by
  refine ⟨(continuous_legalMarkedInputSceneReroot q v).measurable, ?_⟩
  change ((Q : Measure (LegalMarkedOptimalInputScene q)).map (legalMarkedCanonicalFirstInputScene q)).map
    (legalMarkedInputSceneReroot q v) = (Q : Measure (LegalMarkedOptimalInputScene q)).map _
  rw [Measure.map_map (continuous_legalMarkedInputSceneReroot q v).measurable
    (continuous_legalMarkedCanonicalFirstInputScene q).measurable]
  have hcomm : legalMarkedInputSceneReroot q v ∘ legalMarkedCanonicalFirstInputScene q =
      legalMarkedCanonicalFirstInputScene q ∘ legalMarkedInputSceneReroot q v := rfl
  rw [hcomm, ← Measure.map_map (continuous_legalMarkedCanonicalFirstInputScene q).measurable
    (continuous_legalMarkedInputSceneReroot q v).measurable, (hQ v).map_eq]

/-- Every original full matching property is retained on the canonical law. -/
theorem LegalWeightedStationaryPoissonMatching.canonicalFirstInput_full_matching
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ s ∂(legalMarkedCanonicalFirstInputLaw q M.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s := by
  change ∀ᵐ s ∂(M.law : Measure _).map (legalMarkedCanonicalFirstInputScene q), _
  apply (ae_map_iff (continuous_legalMarkedCanonicalFirstInputScene q).measurable.aemeasurable
    (measurableSet_isFullOriginalInputMatching q)).mpr
  filter_upwards [M.full_matching] with s hs
  exact
    { simple_edges := hs.simple_edges
      simple_inputs := hs.simple_inputs
      source_marginal := hs.source_marginal
      target_marginal := hs.target_marginal
      source_injective := hs.source_injective
      target_injective := hs.target_injective
      source_occupied := hs.source_occupied
      target_occupied := hs.target_occupied }

/-- The actual strict support order is preserved on the same first matching. -/
theorem LegalWeightedStationaryPoissonMatching.canonicalFirstInput_forward
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ s ∂(legalMarkedCanonicalFirstInputLaw q M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  let B : Set (LegalMarkedPhysicalEdge q) := {e | ¬ e.1.2 < e.2.2}
  have hB : MeasurableSet B := (measurableSet_lt measurable_fst.snd measurable_snd.snd).compl
  have hzero : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) B = 0 := by
    filter_upwards [M.forward] with s hs
    exact measure_mono_null (fun e he hmem ↦ he (hs e hmem))
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).measure_compl_support
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) B) :=
    (Measure.measurable_coe hB).comp (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  have hz : ∀ᵐ s ∂(legalMarkedCanonicalFirstInputLaw q M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) B = 0 := by
    change ∀ᵐ s ∂(M.law : Measure _).map (legalMarkedCanonicalFirstInputScene q), _
    exact (ae_map_iff (continuous_legalMarkedCanonicalFirstInputScene q).measurable.aemeasurable
      (measurableSet_eq_fun hm measurable_const)).mpr hzero
  filter_upwards [M.canonicalFirstInput_full_matching, hz] with s hs hz
  intro e he
  by_contra hn
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hone := one_le_singleton_of_mem_support_of_legalCounting
    (0 : LegalMarkedPhysicalEdge q) s.1.1 hcount he
  have hz' : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) {e} = 0 :=
    measure_mono_null (singleton_subset_iff.mpr hn) hz
  rw [hz'] at hone
  norm_num at hone

/-- The same actual matching and inputs, with the unused slot canonically
filled. Every matching-class assertion and its original true Palm is preserved. -/
def LegalWeightedStationaryPoissonMatching.canonicalFirstInput
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    LegalWeightedStationaryPoissonMatching q α β kin g where
  law := legalMarkedCanonicalFirstInputLaw q M.law
  stationary := measurePreserving_canonicalFirstInputLaw_reroot M.law M.stationary
  full_matching := M.canonicalFirstInput_full_matching
  forward := M.canonicalFirstInput_forward
  input_laplace := by
    intro S hS F hF hz
    change (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(M.law : Measure _).map (legalMarkedCanonicalFirstInputScene q)) = _
    rw [integral_map (continuous_legalMarkedCanonicalFirstInputScene q).measurable.aemeasurable
      (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable]
    exact M.input_laplace S hS F hF hz
  palm_probability := by
    rw [legalMarkedJointPalm_canonicalFirstInputLaw]
    exact M.palm_probability
  source_clock := by
    rw [legalMarkedJointPalm_canonicalFirstInputLaw]
    exact M.source_clock
  target_clock := by
    rw [legalMarkedJointPalm_canonicalFirstInputLaw]
    exact M.target_clock
  kinetic_integrable := by
    rw [legalMarkedJointPalm_canonicalFirstInputLaw]
    exact M.kinetic_integrable
  probe_integrable := by
    rw [legalMarkedJointPalm_canonicalFirstInputLaw]
    exact M.probe_integrable

/-- Canonical representatives have exactly the original kinetic/probe value. -/
theorem LegalWeightedStationaryPoissonMatching.value_canonicalFirstInput
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) :
    M.canonicalFirstInput.value t = M.value t := by
  have hp : legalMarkedJointPalm q M.canonicalFirstInput.law =
      legalMarkedJointPalm q M.law := legalMarkedJointPalm_canonicalFirstInputLaw q M.law
  simp only [LegalWeightedStationaryPoissonMatching.value, hp]

end OTSelector.Reconstruction
