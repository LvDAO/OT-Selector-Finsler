import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShift
import OTSelector.PointProcess.MatchingSceneReroot

/-!
# Actual full original matching under continuous clock-dependent shifts

The same integer configurations move through the actual point homeomorphisms.
Exact whole endpoint and immutable-color marginals recover every occupied
input and its unique edge in the actual pushed joint scene.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section HomeomorphCounting
variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/-- Actual pushforward by a point homeomorphism is itself a homeomorphism
of the vague locally finite measure carrier, with the actual inverse push. -/
def legalLocalFiniteMeasureHomeomorph (e : X ≃ₜ X) :
    LocalFiniteMeasure X ≃ₜ LocalFiniteMeasure X where
  toFun := localFiniteMapHomeomorph e
  invFun := localFiniteMapHomeomorph e.symm
  left_inv μ := by
    apply Subtype.ext
    change ((μ : Measure X).map e).map e.symm = (μ : Measure X)
    rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    have hc : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
    rw [hc, Measure.map_id]
  right_inv μ := by
    apply Subtype.ext
    change ((μ : Measure X).map e.symm).map e = (μ : Measure X)
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have hc : e ∘ e.symm = id := by funext x; exact e.apply_symm_apply x
    rw [hc, Measure.map_id]
  continuous_toFun := continuous_localFiniteMapHomeomorph e
  continuous_invFun := continuous_localFiniteMapHomeomorph e.symm

/-- The actual transformed measure retains the original integer
multiplicities, represented by the existing configuration transport. -/
theorem isLegalCountingMeasure_mapHomeomorph (base : X) (e : X ≃ₜ X)
    (μ : LocalFiniteMeasure X) (hμ : IsLegalCountingMeasure base μ) :
    IsLegalCountingMeasure base (localFiniteMapHomeomorph e μ) := by
  obtain ⟨c, rfl⟩ := hμ
  refine ⟨LocalConfiguration.mapHomeomorph e c, ?_⟩
  apply Subtype.ext
  exact LocalConfiguration.countingMeasure_mapHomeomorph e c

/-- A point homeomorphism retains every original unit occupied atom. -/
theorem isLegalSimpleCountingMeasure_mapHomeomorph (base : X) (e : X ≃ₜ X)
    (μ : LocalFiniteMeasure X) (hμ : IsLegalSimpleCountingMeasure base μ) :
    IsLegalSimpleCountingMeasure base (localFiniteMapHomeomorph e μ) := by
  obtain ⟨c, rfl, hc⟩ := hμ
  refine ⟨LocalConfiguration.mapHomeomorph e c, ?_, fun x ↦ ?_⟩
  · apply Subtype.ext
    exact LocalConfiguration.countingMeasure_mapHomeomorph e c
  · simpa only [LocalConfiguration.multiplicity_mapHomeomorph] using hc (e.symm x)

/-- The support of the actual transported integer measure consists exactly
of the transported original occupied sites. -/
theorem mem_support_mapHomeomorph_iff_of_legalCounting
    (base : X) (e : X ≃ₜ X) (μ : LocalFiniteMeasure X)
    (hμ : IsLegalCountingMeasure base μ) (x : X) :
    x ∈ (localFiniteMapHomeomorph e μ : Measure X).support ↔
      e.symm x ∈ (μ : Measure X).support := by
  obtain ⟨c, rfl⟩ := hμ
  change x ∈ ((LocalConfiguration.countingMeasure c).map e).support ↔
    e.symm x ∈ (LocalConfiguration.countingMeasure c).support
  rw [← LocalConfiguration.countingMeasure_mapHomeomorph,
    LocalConfiguration.support_countingMeasure, LocalConfiguration.support_countingMeasure]
  simp only [Function.mem_support, LocalConfiguration.multiplicity_mapHomeomorph]

end HomeomorphCounting

local instance markedStationaryValueLegalStationaryClockShiftMatchingColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance markedStationaryValueLegalStationaryClockShiftMatchingInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryClockShiftMatchingPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The whole actual joint clock shift has an actual inverse on its carrier. -/
def legalMarkedInputSceneClockShiftHomeomorph (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    LegalMarkedOptimalInputScene q ≃ₜ LegalMarkedOptimalInputScene q :=
  ((legalLocalFiniteMeasureHomeomorph (legalClockShiftEdge q b)).prodCongr
    (legalLocalFiniteMeasureHomeomorph (legalClockShiftEdge q b))).prodCongr
      (legalLocalFiniteMeasureHomeomorph (legalClockShiftColoredPoint q b))

/-- Reading an immutable color after the actual input push is exactly the
push of that original color by its own unchanged-clock point homeomorphism. -/
theorem legalInputColorMeasure_clockShift (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (c : Fin 2) :
    legalInputColorMeasure q (localFiniteMapHomeomorph (legalClockShiftColoredPoint q b) μ) c =
      (legalInputColorMeasure q μ c).map (legalClockShiftPoint q (b c)) := by
  have hC : MeasurableSet {x : LegalColoredInputPoint q | x.2 = c} :=
    measurable_snd (measurableSet_singleton c)
  have hpre : legalClockShiftColoredPoint q b ⁻¹' {x | x.2 = c} = {x | x.2 = c} := rfl
  unfold legalInputColorMeasure
  rw [coe_localFiniteMapHomeomorph,
    Measure.restrict_map (legalClockShiftColoredPoint q b).continuous.measurable hC, hpre,
    Measure.map_map measurable_fst (legalClockShiftColoredPoint q b).continuous.measurable,
    Measure.map_map (legalClockShiftPoint q (b c)).continuous.measurable measurable_fst]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem hC] with x hx
  change legalClockShiftPoint q (b x.2) x.1 = legalClockShiftPoint q (b c) x.1
  rw [hx]

/-- The complete original source marginal moves through its own point map. -/
theorem fst_map_legalClockShiftEdge (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (μ : Measure (LegalMarkedPhysicalEdge q)) :
    (μ.map (legalClockShiftEdge q b)).fst = μ.fst.map (legalClockShiftPoint q (b 0)) := by
  change (μ.map (legalClockShiftEdge q b)).map Prod.fst =
    (μ.map Prod.fst).map (legalClockShiftPoint q (b 0))
  rw [Measure.map_map measurable_fst (legalClockShiftEdge q b).continuous.measurable,
    Measure.map_map (legalClockShiftPoint q (b 0)).continuous.measurable measurable_fst]
  rfl

/-- The complete original target marginal moves through its own point map. -/
theorem snd_map_legalClockShiftEdge (q : ℕ) (b : Fin 2 → C(ℝ, Fin q → ℝ))
    (μ : Measure (LegalMarkedPhysicalEdge q)) :
    (μ.map (legalClockShiftEdge q b)).snd = μ.snd.map (legalClockShiftPoint q (b 1)) := by
  change (μ.map (legalClockShiftEdge q b)).map Prod.snd =
    (μ.map Prod.snd).map (legalClockShiftPoint q (b 1))
  rw [Measure.map_map measurable_snd (legalClockShiftEdge q b).continuous.measurable,
    Measure.map_map (legalClockShiftPoint q (b 1)).continuous.measurable measurable_snd]
  rfl

/-- Integer transport and exact original color marginals produce a full
one-to-one matching of every actual transformed original input atom. -/
theorem IsFullOriginalInputMatching.clockShift {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    IsFullOriginalInputMatching q (legalMarkedInputSceneClockShift q b s) := by
  apply isFullOriginalInputMatching_of_counting_simple_marginals
  · exact isLegalCountingMeasure_mapHomeomorph _ _ _
      ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  · exact isLegalSimpleCountingMeasure_mapHomeomorph _ _ _ hs.simple_inputs
  · constructor
    · change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map (legalClockShiftEdge q b)).fst =
        legalInputColorMeasure q (localFiniteMapHomeomorph (legalClockShiftColoredPoint q b) s.2) 0
      rw [fst_map_legalClockShiftEdge, hs.source_marginal, legalInputColorMeasure_clockShift]
    · change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map (legalClockShiftEdge q b)).snd =
        legalInputColorMeasure q (localFiniteMapHomeomorph (legalClockShiftColoredPoint q b) s.2) 1
      rw [snd_map_legalClockShiftEdge, hs.target_marginal, legalInputColorMeasure_clockShift]

/-- Every actual support edge remains strictly forward after its clock shift. -/
theorem IsFullOriginalInputMatching.forward_clockShift {q : ℕ}
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (hf : ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    ∀ e ∈ ((legalMarkedInputSceneClockShift q b s).1.1 :
      Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  intro e he
  have hback := (mem_support_mapHomeomorph_iff_of_legalCounting
    (0 : LegalMarkedPhysicalEdge q) (legalClockShiftEdge q b) s.1.1
    ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1 e).mp he
  have h := hf ((legalClockShiftEdge q b).symm e) hback
  exact h

/-- The actual pushed law inherits full original matching almost surely;
no matching or marginal assertion is added as a hypothesis on the new law. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_full_matching
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    ∀ᵐ s ∂(legalMarkedInputClockShiftLaw q b M.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s := by
  change ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map
    (legalMarkedInputSceneClockShiftHomeomorph q b), IsFullOriginalInputMatching q s
  apply (legalMarkedInputSceneClockShiftHomeomorph q b).toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [M.full_matching] with s hs
  exact hs.clockShift b

/-- Strict original forward support is produced on the actual pushed law. -/
theorem LegalWeightedStationaryPoissonMatching.clockShift_forward
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (b : Fin 2 → C(ℝ, Fin q → ℝ)) :
    ∀ᵐ s ∂(legalMarkedInputClockShiftLaw q b M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  change ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map
    (legalMarkedInputSceneClockShiftHomeomorph q b),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2
  apply (legalMarkedInputSceneClockShiftHomeomorph q b).toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [M.full_matching, M.forward] with s hs hf
  exact hs.forward_clockShift hf b

end OTSelector.Reconstruction
