import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudgetLimit

/-! The actual full-block excess budget has quadratically negligible
probability of exceeding any fixed positive fraction of the same cube volume. -/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ} {α β : Measure ℝ}

/-- The complete actual finite-block discrepancy is a measurable scene/reserve readout. -/
theorem measurable_originalFullClockSlabDiscrepancy (G : OriginalStageClockGrid)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) :
    Measurable (originalFullClockSlabDiscrepancy (α := α) (β := β) G K) := by
  unfold originalFullClockSlabDiscrepancy
  exact Finset.measurable_sum _ fun b _ ↦
    measurable_originalFullBlockDiscrepancy hK (G.blockCells_measurable b).1 (G.blockCells_measurable b).2

/-- Markov's inequality consumes the actual full-count cost theorem internally.
The event is the real summed block excess crossing r times the physical volume. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalFullClockSlabDiscrepancy_budgetFailure_quadratic_probability_zero
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ : ℝ≥0) (G : OriginalStageClockGrid) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦
      let K := originalCenteredPhysicalCubeRegion frame (2 * R)
      R^2 * (originalMainReserveExperimentLaw Q (θ * (volume K).toNNReal)).real
        {p | r * volume.real K < originalFullClockSlabDiscrepancy (α := α) (β := β) G K p})
      atTop (𝓝 0) := by
  have hlimit := (Q.tendsto_originalFullClockSlabDiscrepancy_quadratic_cost_zero hq frame θ G).const_mul r⁻¹
  simp only [mul_zero] at hlimit
  apply squeeze_zero' (Eventually.of_forall fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg) ?_ hlimit
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  let K := originalCenteredPhysicalCubeRegion frame (2 * R)
  let V := volume.real K
  let M := originalMainReserveExperimentLaw Q (θ * (volume K).toNNReal)
  let f := originalFullClockSlabDiscrepancy (α := α) (β := β) G K
  have : IsProbabilityMeasure M := by
    change IsProbabilityMeasure ((Q.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (twoMarkedCloudLaw q ℝ ℝ α β (θ * (volume K).toNNReal)))
    infer_instance
  have hVpos : 0 < V := by
    change 0 < (volume (originalCenteredPhysicalCubeRegion frame (2 * R))).toReal
    rw [volume_originalOrientedTraffic_cube]
    change 0 < volume.real (haarRootCube (Fin q) R)
    rw [volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    positivity
  have hI : Integrable f M :=
    (Q.originalFullClockSlabDiscrepancy_integrable_and_integral_le frame R θ G).1
  have hnn (p) : 0 ≤ f p := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hmark := mul_meas_ge_le_integral_of_nonneg (ae_of_all M hnn) hI (r * V)
  have hmono : M.real {p | r * V < f p} ≤ M.real {p | r * V ≤ f p} :=
    measureReal_mono (by
      intro p hp
      exact (show r * V < f p from hp).le)
  have hprob : M.real {p | r * V < f p} ≤ (∫ p, f p ∂M) / (r * V) := by
    apply (le_div_iff₀ (mul_pos hr hVpos)).mpr
    calc
      _ = (r * V) * M.real {p | r * V < f p} := by ring
      _ ≤ (r * V) * M.real {p | r * V ≤ f p} :=
        mul_le_mul_of_nonneg_left hmono (mul_nonneg hr.le hVpos.le)
      _ ≤ _ := hmark
  calc
    _ ≤ R^2 * ((∫ p, f p ∂M) / (r * V)) := mul_le_mul_of_nonneg_left hprob (sq_nonneg R)
    _ = r⁻¹ * (R^2 * (∫ p, f p ∂M) / V) := by
      field_simp [hr.ne', hVpos.ne']

/-- Every requested source or target selector excess is bounded pointwise by
the actual summed full-block budget, before any successful deletion is assumed. -/
theorem originalReserveBlockExcess_le_fullClockSlabDiscrepancy
    (G : OriginalStageClockGrid) (K : Set (Fin q → ℝ))
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)
    (b : G.ClockSlabBlock α β) :
    (originalReserveBlockExcess K 0 1 (G.sourceBlockCell α β b) (G.targetBlockCell α β b)
      (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) : ℝ) ≤
        originalFullClockSlabDiscrepancy (α := α) (β := β) G K p ∧
    (originalReserveBlockExcess K 1 0 (G.targetBlockCell α β b) (G.sourceBlockCell α β b)
      (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) : ℝ) ≤
        originalFullClockSlabDiscrepancy (α := α) (β := β) G K p := by
  have he := originalReserveBlockExcess_sum_eq_fullDiscrepancy K
    (G.sourceBlockCell α β b) (G.targetBlockCell α β b) p
  have hle : originalFullBlockDiscrepancy K (G.sourceBlockCell α β b) (G.targetBlockCell α β b) p ≤
      originalFullClockSlabDiscrepancy (α := α) (β := β) G K p := by
    unfold originalFullClockSlabDiscrepancy
    exact Finset.single_le_sum
      (f := fun c : G.ClockSlabBlock α β ↦
        originalFullBlockDiscrepancy K (G.sourceBlockCell α β c) (G.targetBlockCell α β c) p)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ b)
  have hs : 0 ≤ (originalReserveBlockExcess K 0 1 (G.sourceBlockCell α β b) (G.targetBlockCell α β b)
      (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ (originalReserveBlockExcess K 1 0 (G.targetBlockCell α β b) (G.sourceBlockCell α β b)
      (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

/-- The event that any actual source or target block excess exceeds r times
the true volume has quadratically negligible probability on the same experiment. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_originalReserveBlockExcess_threshold_quadratic_probability_zero
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 4 < q)
    (frame : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (θ : ℝ≥0) (G : OriginalStageClockGrid) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R : ℝ ↦
      let K := originalCenteredPhysicalCubeRegion frame (2 * R)
      R^2 * (originalMainReserveExperimentLaw Q (θ * (volume K).toNNReal)).real
        {p | ∃ b : G.ClockSlabBlock α β,
          r * volume.real K < (originalReserveBlockExcess K 0 1
            (G.sourceBlockCell α β b) (G.targetBlockCell α β b)
            (originalReserveExcessInputAux (originalSourceReserveExperimentSplice p)) : ℝ) ∨
          r * volume.real K < (originalReserveBlockExcess K 1 0
            (G.targetBlockCell α β b) (G.sourceBlockCell α β b)
            (originalReserveExcessInputAux (originalTargetReserveExperimentSplice p)) : ℝ)})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg) ?_
    (Q.tendsto_originalFullClockSlabDiscrepancy_budgetFailure_quadratic_probability_zero hq frame θ G hr)
  exact Eventually.of_forall fun R ↦ by
    let K := originalCenteredPhysicalCubeRegion frame (2 * R)
    have : IsFiniteMeasure (originalMainReserveExperimentLaw Q (θ * (volume K).toNNReal)) := by
      unfold originalMainReserveExperimentLaw
      infer_instance
    apply mul_le_mul_of_nonneg_left ?_ (sq_nonneg R)
    refine measureReal_mono ?_ (by
      change (originalMainReserveExperimentLaw Q (θ * (volume K).toNNReal)) _ ≠ ∞
      exact measure_ne_top _ _)
    intro p hp
    obtain ⟨b, hb⟩ := hp
    have hle := originalReserveBlockExcess_le_fullClockSlabDiscrepancy G K p b
    rcases hb with hb | hb
    · exact hb.trans_le hle.1
    · exact hb.trans_le hle.2

end OTSelector.Reconstruction
