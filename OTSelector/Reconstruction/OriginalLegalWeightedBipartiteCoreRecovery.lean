import OTSelector.Reconstruction.OriginalLegalWeightedBoundaryRecovery
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryOriginalInputIntensity
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryOriginalWindowCore

/-!
# The same actual retained grid core recovers both original endpoint colors

The target source-unit analogue is normalized by the actual stationary target
intensity. Both port losses and the original same-kernel signed-value loss are
controlled by a single grid phase, with no displacement moment assumption.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
local instance bipartiteRecoveryPlanPolish :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace
local instance bipartiteRecoveryInputPolish :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The original target-unit mean plan leaves the source endpoint completely
unrestricted, using the same actual matching law and both original clocks. -/
def legalMarkedTargetUnitMeanPlan (q : ℕ)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    Measure (LegalMarkedPhysicalEdge q) :=
  (physicalSceneMeanPlan (legalMarkedInputPairLaw q Q :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))).restrict
      {e | e.2.1 ∈ palmUnitCube (Fin q)}

/-- Taking the actual mean and projecting its unchanged target commute. -/
theorem physicalSceneMeanPlan_map_snd
    (P : Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) :
    (physicalSceneMeanPlan P).map Prod.snd = physicalSceneTargetIntensity P := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB, physicalSceneMeanPlan,
    Measure.bind_apply (hB.preimage measurable_snd) (Kernel.measurable _).aemeasurable,
    physicalSceneTargetIntensity, Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro scene
  rw [physicalSceneTargetKernel, Kernel.map_apply _ measurable_snd]
  rw [Measure.map_apply measurable_snd hB]
  rfl

/-- Actual stationarity and complete original target marginals normalize the
true target-unit mean plan to probability, without a displacement moment. -/
instance legalWeightedStationaryPoissonMatchingTargetUnitMeanPlanProbability
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    IsProbabilityMeasure (legalMarkedTargetUnitMeanPlan q M.law) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have : IsProbabilityMeasure β := by
    rw [← M.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  let P := (legalMarkedInputPairLaw q M.law :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
  have hi : physicalSceneTargetIntensity P = (volume : Measure (Fin q → ℝ)).prod β :=
    M.targetIntensity_eq_inputColorIntensity.trans M.inputColorIntensities_eq_volume_prod.2
  constructor
  change ((physicalSceneMeanPlan P).restrict
    {e | e.2.1 ∈ palmUnitCube (Fin q)}) univ = 1
  rw [Measure.restrict_apply_univ]
  calc
    _ = ((physicalSceneMeanPlan P).map Prod.snd) (palmUnitCube (Fin q) ×ˢ univ) := by
      rw [Measure.map_apply measurable_snd
        ((measurableSet_palmUnitCube (Fin q)).prod MeasurableSet.univ)]
      congr 1
      ext e
      simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_univ, and_true]
    _ = physicalSceneTargetIntensity P (palmUnitCube (Fin q) ×ˢ univ) :=
      congrArg (fun ν ↦ ν (palmUnitCube (Fin q) ×ˢ univ)) (physicalSceneMeanPlan_map_snd P)
    _ = 1 := by rw [hi, Measure.prod_prod, volume_palmUnitCube, measure_univ, mul_one]

/-- The SAME actual cut-edge rule counts unmatched original target atoms. -/
def legalWeightedGridTargetBoundaryLoss
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (ell : ℝ) (phase : Fin q → ℝ) : ℝ≥0∞ :=
  ∫⁻ e, (if shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1
    then (1 : ℝ≥0∞) else 0) ∂legalMarkedTargetUnitMeanPlan q M.law

/-- The original target input is partitioned by precisely the same retained
plan used for the source side. No independent target matching is selected. -/
theorem IsFullOriginalInputMatching.target_unit_eq_retained_add_gridBoundary
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (ell : ℝ) (phase : Fin q → ℝ) :
    legalInputColorMeasure q s.2 1 {x | x.1 ∈ palmUnitCube (Fin q)} =
      legalWeightedGridRetainedPlan ell phase s {e | e.2.1 ∈ palmUnitCube (Fin q)} +
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        {e | e.2.1 ∈ palmUnitCube (Fin q) ∧
          shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1} := by
  let U : Set (LegalMarkedPhysicalPoint q) := {x | x.1 ∈ palmUnitCube (Fin q)}
  let W : Set (LegalMarkedPhysicalEdge q) := {e | e.2.1 ∈ palmUnitCube (Fin q)}
  let K : Set (LegalMarkedPhysicalEdge q) :=
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}
  have hU : MeasurableSet U := (measurableSet_palmUnitCube (Fin q)).preimage measurable_fst
  have hW : MeasurableSet W := hU.preimage measurable_snd
  have hK : MeasurableSet K := measurableSet_legalWeightedGridRetained ell phase
  have hinput : legalInputColorMeasure q s.2 1 U =
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) W := by
    rw [← hs.target_marginal, Measure.snd, Measure.map_apply measurable_snd hU]
    rfl
  rw [hinput]
  change _ = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict K W +
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (W \ K)
  rw [Measure.restrict_apply hW]
  exact (measure_inter_add_sdiff W hK).symm

/-- The retained original core consumes at most the exact original capacity
of either immutable input color, even after observing the full matching. -/
theorem IsFullOriginalInputMatching.grid_retained_original_capacities
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (ell : ℝ) (phase : Fin q → ℝ) :
    (legalWeightedGridRetainedPlan ell phase s).fst ≤ legalInputColorMeasure q s.2 0 ∧
      (legalWeightedGridRetainedPlan ell phase s).snd ≤ legalInputColorMeasure q s.2 1 := by
  constructor
  · rw [← hs.source_marginal]
    exact Measure.map_mono Measure.restrict_le_self measurable_fst
  · rw [← hs.target_marginal]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd

/-- The literal retained plan belongs to the same locally finite integer-plan carrier. -/
def legalWeightedGridRetainedLocalPlan (ell : ℝ) (phase : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) : LocalFiniteMeasure (LegalMarkedPhysicalEdge q) :=
  ⟨legalWeightedGridRetainedPlan ell phase s, by
    change IsFiniteMeasureOnCompacts ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict _)
    infer_instance⟩

/-- Each retained atom is the same original unit matching atom; restricting
this original plan neither duplicates atoms nor changes the source/target pairing. -/
theorem IsFullOriginalInputMatching.simple_grid_retained_original_plan
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (ell : ℝ) (phase : Fin q → ℝ) :
    IsLegalSimpleCountingMeasure (0 : LegalMarkedPhysicalEdge q)
      (legalWeightedGridRetainedLocalPlan ell phase s) :=
  isLegalSimpleCountingMeasure_restrict _ s.1.1 hs.simple_edges _

/-- The true target deficit and retained target mass partition exact original
unit intensity, with the same grid cells as the source core. -/
theorem LegalWeightedStationaryPoissonMatching.target_retained_density_add_gridBoundary_eq_one
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (ell : ℝ) (phase : Fin q → ℝ) :
    (legalMarkedTargetUnitMeanPlan q M.law)
        {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1} +
      legalWeightedGridTargetBoundaryLoss M ell phase = 1 := by
  let K : Set (LegalMarkedPhysicalEdge q) :=
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}
  have hK : MeasurableSet K := measurableSet_legalWeightedGridRetained ell phase
  have heq : legalWeightedGridTargetBoundaryLoss M ell phase =
      (legalMarkedTargetUnitMeanPlan q M.law) Kᶜ := by
    simpa [legalWeightedGridTargetBoundaryLoss, K, Set.indicator] using
      (lintegral_indicator_const (μ := legalMarkedTargetUnitMeanPlan q M.law)
        hK.compl (1 : ℝ≥0∞))
  rw [heq, measure_add_measure_compl hK]
  exact measure_univ

/-- The actual target-side unmatched density vanishes by bounded dominated
convergence on its internally normalized target-unit mean measure. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_target_gridBoundary_density_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ phase, legalWeightedGridTargetBoundaryLoss M (R n) phase
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  simpa only [legalWeightedGridTargetBoundaryLoss, ENNReal.ofReal_one] using
    tendsto_lintegral_shiftedGrid_crossing_integrable_weight_zero q
      (legalMarkedTargetUnitMeanPlan q M.law) (fun _ ↦ 1) measurable_const
      (integrable_const 1) R hRpos hR

/-- Target deficit is a measurable function of the SAME independent grid phase. -/
theorem measurable_legalWeightedGridTargetBoundaryLoss
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (ell : ℝ) :
    Measurable (legalWeightedGridTargetBoundaryLoss M ell) := by
  have hs : Measurable (fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      shiftedGridCells ell p.1 p.2.1.1) :=
    (measurable_joint_shiftedGridCells ell).comp (measurable_fst.prodMk measurable_snd.fst.fst)
  have ht : Measurable (fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      shiftedGridCells ell p.1 p.2.2.1) :=
    (measurable_joint_shiftedGridCells ell).comp (measurable_fst.prodMk measurable_snd.snd.fst)
  have hm : Measurable (fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      if shiftedGridCells ell p.1 p.2.1.1 ≠ shiftedGridCells ell p.1 p.2.2.1
        then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite (measurableSet_eq_fun hs ht).compl measurable_const
  exact hm.lintegral_prod_right'

/-- The target boundary quantity is exactly the expected count of the SAME
original cut edges in the actual target unit window of each original scene. -/
theorem legalWeightedGridTargetBoundaryLoss_eq_actual_scene
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (ell : ℝ) (phase : Fin q → ℝ) :
    legalWeightedGridTargetBoundaryLoss M ell phase =
      ∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        {e | e.2.1 ∈ palmUnitCube (Fin q) ∧
          shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1}
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let K : Set (LegalMarkedPhysicalEdge q) :=
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}
  let W : Set (LegalMarkedPhysicalEdge q) := {e | e.2.1 ∈ palmUnitCube (Fin q)}
  have hK : MeasurableSet K := measurableSet_legalWeightedGridRetained ell phase
  have hW : MeasurableSet W :=
    (measurableSet_palmUnitCube (Fin q)).preimage measurable_snd.fst
  let P := (legalMarkedInputPairLaw q M.law :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
  have hm : Measurable (fun scene :
      CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      (scene.1 : Measure (LegalMarkedPhysicalEdge q)) (Kᶜ ∩ W)) :=
    (Measure.measurable_coe (hK.compl.inter hW)).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst)
  have heq : legalWeightedGridTargetBoundaryLoss M ell phase =
      (legalMarkedTargetUnitMeanPlan q M.law) Kᶜ := by
    simpa [legalWeightedGridTargetBoundaryLoss, K, Set.indicator] using
      (lintegral_indicator_const (μ := legalMarkedTargetUnitMeanPlan q M.law)
        hK.compl (1 : ℝ≥0∞))
  calc
    _ = physicalSceneMeanPlan P (Kᶜ ∩ W) := heq.trans (Measure.restrict_apply hK.compl)
    _ = ∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q)) (Kᶜ ∩ W) ∂P := by
      rw [physicalSceneMeanPlan, Measure.bind_apply (hK.compl.inter hW)
        (Kernel.measurable _).aemeasurable]
      rfl
    _ = ∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Kᶜ ∩ W)
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := lintegral_map hm measurable_fst
    _ = _ := by
      apply lintegral_congr
      intro s
      congr 1
      ext e
      simp only [mem_inter_iff, mem_compl_iff, K, W, mem_ofPred_eq]
      exact and_comm

/-- One actual phase budget pays for BOTH original endpoint deficits and the
absolute original same-kernel signed-value loss of their ONE retained plan. -/
def legalWeightedBipartiteGridRecoveryBudget
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (ell : ℝ) (phase : Fin q → ℝ) (t : ℝ) : ℝ≥0∞ :=
  legalWeightedGridBoundaryLoss M ell phase (legalWeightedGridRecoveryWeight kin g t) +
    legalWeightedGridTargetBoundaryLoss M ell phase

/-- Both genuine endpoint deficits and the original weighted energy loss
vanish simultaneously under their shared original independent grid phase. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_bipartite_gridRecovery_budget_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ phase, legalWeightedBipartiteGridRecoveryBudget M (R n) phase t
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  have h := (M.tendsto_gridRecovery_loss_zero hk hg t R hRpos hR).add
    (M.tendsto_target_gridBoundary_density_zero R hRpos hR)
  have heq (n : ℕ) : (∫⁻ phase,
      legalWeightedBipartiteGridRecoveryBudget M (R n) phase t
        ∂shiftedGridPhaseLaw q (R n)) =
      (∫⁻ phase, legalWeightedGridBoundaryLoss M (R n) phase
        (legalWeightedGridRecoveryWeight kin g t) ∂shiftedGridPhaseLaw q (R n)) +
      (∫⁻ phase, legalWeightedGridTargetBoundaryLoss M (R n) phase
        ∂shiftedGridPhaseLaw q (R n)) :=
    lintegral_add_right _ (measurable_legalWeightedGridTargetBoundaryLoss M (R n))
  simpa only [zero_add] using h.congr' (.of_forall fun n ↦ (heq n).symm)

/-- The same deterministic phase simultaneously gives small actual source
ports, small actual target ports, and small original signed-value loss. Both
colors are retained from the same plan; no correlated leftover is called iid. -/
theorem LegalWeightedStationaryPoissonMatching.eventually_exists_bipartite_grid_core_recovery
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ phase : Fin q → ℝ,
      legalWeightedGridBoundaryLoss M (R n) phase (fun _ ↦ 1) < ENNReal.ofReal ε ∧
      legalWeightedGridTargetBoundaryLoss M (R n) phase < ENNReal.ofReal ε ∧
      ENNReal.ofReal |M.value t -
        ∫ e in {e : LegalMarkedPhysicalEdge q |
          shiftedGridCells (R n) phase e.1.1 = shiftedGridCells (R n) phase e.2.1},
          kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
          ∂legalMarkedSourceUnitMeanPlan q M.law| < ENNReal.ofReal ε := by
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hsmall := (M.tendsto_bipartite_gridRecovery_budget_zero hk hg t R hRpos hR).eventually
    (eventually_lt_nhds hε')
  filter_upwards [hsmall] with n hn
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q (R n)) :=
    shiftedGridPhaseLaw_probability q (hRpos n)
  have hex : ∃ phase, legalWeightedBipartiteGridRecoveryBudget M (R n) phase t <
      ENNReal.ofReal ε := by
    by_contra hnot
    have hall : ∀ phase, ENNReal.ofReal ε ≤
        legalWeightedBipartiteGridRecoveryBudget M (R n) phase t := by
      simpa only [not_exists, not_lt] using hnot
    have hb : ENNReal.ofReal ε ≤ ∫⁻ phase,
        legalWeightedBipartiteGridRecoveryBudget M (R n) phase t
          ∂shiftedGridPhaseLaw q (R n) := by
      calc
        _ = ∫⁻ _ : Fin q → ℝ, ENNReal.ofReal ε ∂shiftedGridPhaseLaw q (R n) := by simp
        _ ≤ _ := lintegral_mono hall
    exact hn.not_ge hb
  obtain ⟨phase, hphase⟩ := hex
  have hsrc : legalWeightedGridBoundaryLoss M (R n) phase (fun _ ↦ 1) ≤
      legalWeightedGridBoundaryLoss M (R n) phase (legalWeightedGridRecoveryWeight kin g t) := by
    apply legalWeightedGridBoundaryLoss_mono
    intro m
    dsimp [legalWeightedGridRecoveryWeight]
    linarith [abs_nonneg (kin m.1.1 m.1.2 m.2),
      mul_nonneg (abs_nonneg t) (abs_nonneg (g m.1.1 m.1.2))]
  have hcost : ENNReal.ofReal |M.value t -
      ∫ e in {e : LegalMarkedPhysicalEdge q |
        shiftedGridCells (R n) phase e.1.1 = shiftedGridCells (R n) phase e.2.1},
        kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
        ∂legalMarkedSourceUnitMeanPlan q M.law| ≤
      legalWeightedGridBoundaryLoss M (R n) phase (legalWeightedGridRecoveryWeight kin g t) := by
    apply (M.value_sub_retained_cost_le_boundary hk hg t (R n) phase).trans
      (legalWeightedGridBoundaryLoss_mono M (R n) phase _ _ ?_)
    intro m
    dsimp [legalWeightedGridRecoveryWeight]
    calc
      |kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2| ≤
          |kin m.1.1 m.1.2 m.2| + |t * g m.1.1 m.1.2| := abs_add_le _ _
      _ = |kin m.1.1 m.1.2 m.2| + |t| * |g m.1.1 m.1.2| := by rw [abs_mul]
      _ ≤ _ := by linarith
  refine ⟨phase, (hsrc.trans (le_add_right le_rfl)).trans_lt hphase,
    (le_add_left le_rfl).trans_lt hphase, (hcost.trans (le_add_right le_rfl)).trans_lt hphase⟩

/-- Target-window deficiency counts exactly the original partners whose sources
escape the retained source window; no independent target matching is selected. -/
theorem originalIndex_windowCore_target_deficit_eq_source_escape
    {m n : ℕ} (μ : LocalFiniteMeasure (LegalMarkedPhysicalEdge q))
    {U V : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (target : Fin n → LegalMarkedPhysicalPoint q) (σ : OTSelector.PartialMatching m n)
    (htarget : (μ : Measure (LegalMarkedPhysicalEdge q)).snd.restrict V =
      ∑ j, Measure.dirac (target j))
    (hmass : (μ : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ V) = (σ.card : ℝ≥0∞)) :
    ((n - σ.card : ℕ) : ℝ) = ((μ : Measure (LegalMarkedPhysicalEdge q)) (Uᶜ ×ˢ V)).toReal := by
  have ht : (μ : Measure (LegalMarkedPhysicalEdge q)).snd V = (n : ℝ≥0∞) := by
    have h := congrArg (fun ν : Measure (LegalMarkedPhysicalPoint q) ↦ ν univ) htarget
    simpa only [Measure.restrict_apply_univ, Measure.finsetSum_apply, Measure.dirac_apply_of_mem,
      mem_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h
  have hsplit : (μ : Measure (LegalMarkedPhysicalEdge q)).snd V =
      (μ : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ V) +
        (μ : Measure (LegalMarkedPhysicalEdge q)) (Uᶜ ×ˢ V) := by
    rw [Measure.snd, Measure.map_apply measurable_snd hV]
    have heq : (Prod.snd ⁻¹' V : Set (LegalMarkedPhysicalEdge q)) =
        (U ×ˢ V) ∪ (Uᶜ ×ˢ V) := by
      ext e
      simp only [mem_preimage, mem_union, mem_prod, mem_compl_iff]
      tauto
    rw [heq]
    exact measure_union (by
      apply disjoint_left.mpr
      intro e he he'
      exact he'.1 he.1) (hU.compl.prod hV)
  have hfinite : (μ : Measure (LegalMarkedPhysicalEdge q)) (Uᶜ ×ˢ V) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top n)
    rw [← ht, hsplit]
    exact le_add_left le_rfl
  rw [ht, hmass] at hsplit
  have h := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_natCast, ENNReal.toReal_add (ENNReal.natCast_ne_top _) hfinite,
    ENNReal.toReal_natCast] at h
  rw [Nat.cast_sub (σ.card_le.trans (min_le_right _ _))]
  linarith

/-- Inside one actual grid cell, restricting the retained core gives literally
the same original plan restriction, including its original signed matrix cost. -/
theorem legalWeightedGridRetainedPlan_restrict_same_cell
    (ell : ℝ) (phase : Fin q → ℝ) (s : LegalMarkedOptimalInputScene q)
    {U : Set (LegalMarkedPhysicalPoint q)} (cell : Fin q → ℤ)
    (hcell : ∀ x ∈ U, shiftedGridCells ell phase x.1 = cell) :
    (legalWeightedGridRetainedPlan ell phase s).restrict (U ×ˢ U) =
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U) := by
  apply Measure.restrict_restrict_of_subset
  intro e he
  exact (hcell e.1 he.1).trans (hcell e.2 he.2).symm

/-- A compact part of a genuine grid cell supplies an actual legal bipartite
core on the literal original Poisson window arrays. Both deficiencies are the
exact original cut-edge counts. The same original plan and cost are preserved. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalPoisson_bipartite_gridCellCore
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hq : 0 < q)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : IsCompact U)
    (ell : ℝ) (phase : Fin q → ℝ) (cell : Fin q → ℤ)
    (hcell : ∀ x ∈ U, shiftedGridCells ell phase x.1 = cell) (t : ℝ) :
    ∃ S > 0, ∃ R : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.snd = legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        let source := legalOriginalBlockRestriction U p.2.1
        let target := legalOriginalBlockRestriction U p.2.2
        ∃ σ : OTSelector.PartialMatching source.1 target.1,
          PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (source.2 i).2)
            (fun j ↦ (target.2 j).2)) σ ∧
          (legalWeightedGridRetainedPlan ell phase p.1).restrict (U ×ˢ U) =
            ∑ e ∈ σ.edges, Measure.dirac (source.2 e.1, target.2 e.2) ∧
          (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ U) = (σ.card : ℝ≥0∞) ∧
          Integrable (fun e ↦ kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2)
            ((legalWeightedGridRetainedPlan ell phase p.1).restrict (U ×ˢ U)) ∧
          (∫ e, kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
            ∂(legalWeightedGridRetainedPlan ell phase p.1).restrict (U ×ˢ U)) =
              σ.cost (fun i j ↦ kin (source.2 i).2 (target.2 j).2
                ((target.2 j).1 - (source.2 i).1) + t * g (source.2 i).2 (target.2 j).2) ∧
          ((source.1 - σ.card : ℕ) : ℝ) =
            ((p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)).toReal ∧
          ((target.1 - σ.card : ℕ) : ℝ) =
            ((p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Uᶜ ×ˢ U)).toReal := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← M.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← M.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  obtain ⟨S, hS, R, hleft, hright, hread⟩ :=
    M.exists_originalPoisson_windowCoupling (hU.prod isCompact_univ)
  have hfull : ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
      IsFullOriginalInputMatching q p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hleft]
    exact M.full_matching
  have hforward : ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
      ∀ e ∈ (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
    have h : ∀ᵐ s ∂(R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.fst, ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
            e.1.2 < e.2.2 := by
      rw [hleft]
      exact M.forward
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hinj : ∀ᵐ p ∂(R : Measure (LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
      Injective p.2.1.2 ∧ Injective p.2.2.2 := by
    have h : ∀ᵐ b ∂(R : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.snd, Injective b.1.2 ∧ Injective b.2.2 := by
      rw [hright]
      exact ae_injective_legalInputPoissonWindowLaw q hq hS α β
    exact ae_of_ae_map measurable_snd.aemeasurable h
  refine ⟨S, hS, R, hleft, hright, ?_⟩
  filter_upwards [hfull, hforward, hinj, hread] with p hp hf hi hr
  let source := legalOriginalBlockRestriction U p.2.1
  let target := legalOriginalBlockRestriction U p.2.2
  have hm := original_window_marginals_eq_of_colored_readout q p.1 hp p.2 hU.measurableSet hr
  have hs : (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst.restrict U =
      ∑ i : Fin source.1, Measure.dirac (source.2 i) := by
    exact hm.1.trans
      (legalInputBlockMeasure_legalOriginalBlockRestriction p.2.1 hU.measurableSet).symm
  have ht : (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd.restrict U =
      ∑ j : Fin target.1, Measure.dirac (target.2 j) := by
    exact hm.2.trans
      (legalInputBlockMeasure_legalOriginalBlockRestriction p.2.2 hU.measurableSet).symm
  have hc := ((isLegalSimpleCountingMeasure_iff (0 : LegalMarkedPhysicalEdge q) p.1.1.1).mp
    hp.simple_edges).1
  have ha : ∀ᵐ e ∂(p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2 := by
    filter_upwards [Measure.support_mem_ae (μ :=
      (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)))] with e he
    exact hf e he
  obtain ⟨σ, hσ, hmeasure, hmass, hcost, hvalue⟩ := exists_originalIndex_legal_windowCore_cost
    (0 : LegalMarkedPhysicalEdge q) p.1.1.1 hc hU.measurableSet hU.measurableSet
    source.2 target.2 (legalOriginalBlockRestriction_injective U p.2.1 hi.1)
    (legalOriginalBlockRestriction_injective U p.2.2 hi.2) hs ht
    (fun x y : LegalMarkedPhysicalPoint q ↦ x.2 < y.2) ha
    (fun e ↦ kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2)
  have heq := legalWeightedGridRetainedPlan_restrict_same_cell ell phase p.1 cell hcell
  refine ⟨σ, hσ, heq.trans hmeasure, hmass, ?_, ?_, ?_, ?_⟩
  · rwa [heq]
  · rwa [heq]
  · exact originalIndex_windowCore_source_deficit_eq_target_escape p.1.1.1
      hU.measurableSet hU.measurableSet source.2 σ hs hmass
  · exact originalIndex_windowCore_target_deficit_eq_source_escape p.1.1.1
      hU.measurableSet hU.measurableSet target.2 σ ht hmass

end OTSelector.Reconstruction
