import OTSelector.Reconstruction.OriginalReservePhysicalWindowSampler

/-! Join the whole original reserve to its own literal physical-window iid sampler. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance originalReservePhysicalJoiningInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReservePhysicalJoiningPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The entire original reserve scene is kept as an identity witness. Its own
finite window sampler retains the independent count, positions, and mark law.
Only this finite sampler is used for later marks-only deletion and iid laws. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalReserve_window_joining_of_sampler
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U)
    (hUK : U ⊆ (Prod.fst ∘ Prod.fst) ⁻¹' K)
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (P : Measure Y) [IsProbabilityMeasure P]
    (arrays : Y → BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (harrays : Measurable arrays)
    (harraylaw : P.map arrays = legalInputPoissonWindowLaw q K α β) :
    ∃ J : ProbabilityMeasure (LegalMarkedOptimalInputScene q × Y),
      (J : Measure (LegalMarkedOptimalInputScene q × Y)).map
        Prod.fst = (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (J : Measure (LegalMarkedOptimalInputScene q × Y)).map
        Prod.snd = P ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × Y)),
        (p.1.2 : Measure (LegalColoredInputPoint q)).restrict U =
          (legalInputTwoBlockMeasure q (arrays p.2)).restrict U := by
  let : Nonempty (LegalMarkedOptimalInputScene q) :=
    nonempty_of_isProbabilityMeasure (N.law : Measure (LegalMarkedOptimalInputScene q))
  let f : LegalMarkedOptimalInputScene q → LocalFiniteMeasure (LegalColoredInputPoint q) :=
    fun scene ↦ legalInputRestrictionLocal U scene.2
  let z : (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) →
      LocalFiniteMeasure (LegalColoredInputPoint q) :=
    fun b ↦ legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)
  have hf : Measurable f := (measurable_legalInputRestrictionLocal hU.measurableSet).comp
    measurable_snd
  have hz : Measurable z := (measurable_legalInputRestrictionLocal hU.measurableSet).comp
    (measurable_legalInputTwoBlockLocal q)
  have hlaw := N.map_originalInput_compactWindow_eq_exactSpatialPoisson hK hKpos hU hUK
  let F := finitePlanLocalVersion
    (id : Measure (LegalColoredInputPoint q) → Measure (LegalColoredInputPoint q))
  have hF : Measurable F := measurable_finitePlanLocalVersion id measurable_id
  have hblock : Measurable (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) :=
    (measurable_originalMeasureRestriction hU.measurableSet).comp
      (measurable_originalInputTwoBlockMeasure q)
  have hlocal := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦ P.map F) hlaw
  rw [Measure.map_map hF (measurable_originalSceneInputRestriction q hU.measurableSet),
    Measure.map_map hF hblock] at hlocal
  have hb (b) : F ((legalInputTwoBlockMeasure q b).restrict U) = z b :=
    finitePlanLocalVersion_restrict_compact_eq hU (legalInputTwoBlockLocal q b)
  have hlocal' : (N.law : Measure _).map f =
      (legalInputPoissonWindowLaw q K α β).map z := by
    simpa only [Function.comp_def, hb, F, f,
      finitePlanLocalVersion_restrict_compact_eq hU] using hlocal
  have hraw : (N.law : Measure _).map f =
      (P).map
        (z ∘ arrays) := by
    rw [← Measure.map_map hz harrays,
      harraylaw]
    exact hlocal'
  obtain ⟨J, hleft, hright, heq⟩ := exists_joint_original_input_readout
    (N.law : Measure _) (P)
      f (z ∘ arrays) hf
      (hz.comp harrays) hraw
  refine ⟨J, hleft, hright, ?_⟩
  filter_upwards [heq] with p hp
  exact congrArg (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
    (μ : Measure (LegalColoredInputPoint q))) hp

/-- The actual normalized-Haar sampler satisfies the joining input law
internally, while preserving its entire original count and indexed infinite sequence. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalReserve_physicalWindow_joining
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U)
    (hUK : U ⊆ (Prod.fst ∘ Prod.fst) ⁻¹' K) :
    ∃ J : ProbabilityMeasure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ),
      (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map
        Prod.fst = (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)).map
        Prod.snd = originalPhysicalReserveTwoCloudLaw q K α β ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
        (p.1.2 : Measure (LegalColoredInputPoint q)).restrict U =
          (legalInputTwoBlockMeasure q (originalPhysicalReserveCloudArrays q p.2)).restrict U := by
  let := isProbabilityMeasure_originalPhysicalReserveTwoCloudLaw q hK hKpos α β
  let : StandardBorelSpace (MarkedCloudSpace q ℝ) := by infer_instance
  exact N.exists_originalReserve_window_joining_of_sampler hK hKpos hU hUK
    (originalPhysicalReserveTwoCloudLaw q K α β) (originalPhysicalReserveCloudArrays q)
    (measurable_originalPhysicalReserveCloudArrays q)
    (map_originalPhysicalReserveCloudArrays q hK hKpos α β)

end OTSelector.Reconstruction
