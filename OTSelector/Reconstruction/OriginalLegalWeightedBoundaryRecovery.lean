import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWeightedGridTail

/-!
# Actual retained grid cores for arbitrary weighted stationary matchings

The original full matching is cut only between different finite grid cells.
Its original input deficit is exactly the discarded edge mass. A single grid
phase makes both that density and the original same-kernel signed-cost loss
arbitrarily small, without any displacement moment assumption.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
local instance boundaryRecoveryPlanPolish :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace
local instance boundaryRecoveryInputPolish :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Keep exactly the original matching edges lying within one unchanged grid cell. -/
def legalWeightedGridRetainedPlan (ell : ℝ) (phase : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) : Measure (LegalMarkedPhysicalEdge q) :=
  (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}

/-- Measurability of the exact original same-cell edge set. -/
theorem measurableSet_legalWeightedGridRetained (ell : ℝ) (phase : Fin q → ℝ) :
    MeasurableSet {e : LegalMarkedPhysicalEdge q |
      shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1} :=
  measurableSet_eq_fun
    ((measurable_joint_shiftedGridCells ell).comp (measurable_const.prodMk measurable_fst.fst))
    ((measurable_joint_shiftedGridCells ell).comp (measurable_const.prodMk measurable_snd.fst))

/-- A source-unit readout counts the actual removed original edges, under the
SAME matching mean plan, with their complete clocks and displacement retained. -/
def legalWeightedGridBoundaryLoss
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (ell : ℝ) (phase : Fin q → ℝ) (w : PhysicalPairPalmMark (Fin q) → ℝ) : ℝ≥0∞ :=
  ∫⁻ e, (if shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1
    then ENNReal.ofReal (w (physicalPairAnchor e).2) else 0)
    ∂legalMarkedSourceUnitMeanPlan q M.law

/-- Cutting the real matching produces exactly these unmatched original source
points. This is a whole-input identity, not a law assigned to selected ports. -/
theorem IsFullOriginalInputMatching.source_unit_eq_retained_add_gridBoundary
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (ell : ℝ) (phase : Fin q → ℝ) :
    legalInputColorMeasure q s.2 0 {x | x.1 ∈ palmUnitCube (Fin q)} =
      legalWeightedGridRetainedPlan ell phase s {e | e.1.1 ∈ palmUnitCube (Fin q)} +
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        {e | e.1.1 ∈ palmUnitCube (Fin q) ∧
          shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1} := by
  let U : Set (LegalMarkedPhysicalPoint q) := {x | x.1 ∈ palmUnitCube (Fin q)}
  let W : Set (LegalMarkedPhysicalEdge q) := {e | e.1.1 ∈ palmUnitCube (Fin q)}
  let K : Set (LegalMarkedPhysicalEdge q) :=
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}
  have hU : MeasurableSet U := (measurableSet_palmUnitCube (Fin q)).preimage measurable_fst
  have hW : MeasurableSet W := hU.preimage measurable_fst
  have hK : MeasurableSet K := measurableSet_legalWeightedGridRetained ell phase
  have hinput : legalInputColorMeasure q s.2 0 U =
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) W := by
    rw [← hs.source_marginal, Measure.fst, Measure.map_apply measurable_fst hU]
    rfl
  rw [hinput]
  change _ = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict K W +
    (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (W \ K)
  rw [Measure.restrict_apply hW]
  exact (measure_inter_add_sdiff W hK).symm

/-- The exact unmatched original source density equals the mass of grid cuts.
The equality holds under every genuine weighted stationary matching law. -/
theorem LegalWeightedStationaryPoissonMatching.ae_source_unit_eq_retained_add_gridBoundary
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (ell : ℝ) (phase : Fin q → ℝ) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      legalInputColorMeasure q s.2 0 {x | x.1 ∈ palmUnitCube (Fin q)} =
        legalWeightedGridRetainedPlan ell phase s {e | e.1.1 ∈ palmUnitCube (Fin q)} +
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
          {e | e.1.1 ∈ palmUnitCube (Fin q) ∧
            shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1} :=
  M.full_matching.mono fun _ hs ↦ hs.source_unit_eq_retained_add_gridBoundary ell phase

/-- A nonnegative readout of the original cut mean plan is exactly its actual
source-window scene expectation; no independent port process is substituted. -/
theorem legalWeightedGridBoundaryLoss_eq_actual_scene
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (ell : ℝ) (phase : Fin q → ℝ) (w : PhysicalPairPalmMark (Fin q) → ℝ) (hw : Measurable w) :
    legalWeightedGridBoundaryLoss M ell phase w =
      ∫⁻ scene, ∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ palmUnitCube (Fin q)},
        (if shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1
          then ENNReal.ofReal (w (physicalPairAnchor e).2) else 0)
        ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q))
        ∂(legalMarkedInputPairLaw q M.law : Measure
          (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) := by
  have hm : Measurable (fun e : LegalMarkedPhysicalEdge q ↦
      if shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1
      then ENNReal.ofReal (w (physicalPairAnchor e).2) else 0) :=
    ((hw.comp measurable_physicalPairAnchor.snd).ennreal_ofReal).ite
      (measurableSet_legalWeightedGridRetained ell phase).compl measurable_const
  exact setLIntegral_physicalSceneMeanPlan _ hm (measurableSet_palmUnitCube (Fin q))

/-- The complete original input intensity is one. Its retained source-unit
mass and the actual unmatched boundary density partition that exact unit mass. -/
theorem LegalWeightedStationaryPoissonMatching.retained_density_add_gridBoundary_eq_one
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (ell : ℝ) (phase : Fin q → ℝ) :
    (legalMarkedSourceUnitMeanPlan q M.law)
        {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1} +
      legalWeightedGridBoundaryLoss M ell phase (fun _ ↦ 1) = 1 := by
  let K : Set (LegalMarkedPhysicalEdge q) :=
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}
  have hK : MeasurableSet K := measurableSet_legalWeightedGridRetained ell phase
  have heq : legalWeightedGridBoundaryLoss M ell phase (fun _ ↦ 1) =
      (legalMarkedSourceUnitMeanPlan q M.law) Kᶜ := by
    change (∫⁻ e, if shiftedGridCells ell phase e.1.1 ≠ shiftedGridCells ell phase e.2.1
      then ENNReal.ofReal (1 : ℝ) else 0 ∂legalMarkedSourceUnitMeanPlan q M.law) = _
    simpa [K, Set.indicator] using
      (lintegral_indicator_const (μ := legalMarkedSourceUnitMeanPlan q M.law)
        hK.compl (1 : ℝ≥0∞))
  rw [heq, measure_add_measure_compl hK]
  exact measure_univ

/-- The retained mean source density is exactly the expectation of restricting
EACH original scene plan, before taking the mean or discarding input records. -/
theorem legalWeightedGridRetained_density_eq_actual_scene
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (ell : ℝ) (phase : Fin q → ℝ) :
    (legalMarkedSourceUnitMeanPlan q M.law)
      {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1} =
      ∫⁻ s, legalWeightedGridRetainedPlan ell phase s
        {e | e.1.1 ∈ palmUnitCube (Fin q)}
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let K : Set (LegalMarkedPhysicalEdge q) :=
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}
  let W : Set (LegalMarkedPhysicalEdge q) := {e | e.1.1 ∈ palmUnitCube (Fin q)}
  have hK : MeasurableSet K := measurableSet_legalWeightedGridRetained ell phase
  have hW : MeasurableSet W :=
    (measurableSet_palmUnitCube (Fin q)).preimage measurable_fst.fst
  let P := (legalMarkedInputPairLaw q M.law :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
  have hm : Measurable (fun scene :
      CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ↦
      (scene.1 : Measure (LegalMarkedPhysicalEdge q)) (K ∩ W)) :=
    (Measure.measurable_coe (hK.inter hW)).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst)
  calc
    _ = physicalSceneMeanPlan P (K ∩ W) := Measure.restrict_apply hK
    _ = ∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q)) (K ∩ W) ∂P := by
      rw [physicalSceneMeanPlan, Measure.bind_apply (hK.inter hW)
        (Kernel.measurable _).aemeasurable]
      rfl
    _ = ∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (K ∩ W)
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) :=
      lintegral_map hm measurable_fst
    _ = _ := by
      apply lintegral_congr
      intro s
      exact (congrArg (fun A ↦ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) A)
        (inter_comm K W)).trans (Measure.restrict_apply hW).symm

/-- Monotonicity keeps every estimate on the same actual original cut edges. -/
theorem legalWeightedGridBoundaryLoss_mono
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (ell : ℝ) (phase : Fin q → ℝ) (w₁ w₂ : PhysicalPairPalmMark (Fin q) → ℝ)
    (hle : ∀ m, w₁ m ≤ w₂ m) :
    legalWeightedGridBoundaryLoss M ell phase w₁ ≤
      legalWeightedGridBoundaryLoss M ell phase w₂ := by
  apply lintegral_mono
  intro e
  dsimp only
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (hle _)
  · rfl

/-- The original input-deficit density vanishes as finite grid cells grow.
The probability Palm alone supplies the required constant integrability. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_gridBoundary_density_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ phase, legalWeightedGridBoundaryLoss M (R n) phase (fun _ ↦ 1)
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  exact tendsto_lintegral_shiftedGrid_crossing_integrable_weight_zero q
    (legalMarkedSourceUnitMeanPlan q M.law) (fun _ ↦ 1) measurable_const
    (integrable_const 1) R hRpos hR

/-- One integrable actual Palm weight pays simultaneously for unmatched
original input density and the absolute original same-matrix tilted cost. -/
def legalWeightedGridRecoveryWeight (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (m : PhysicalPairPalmMark (Fin q)) : ℝ :=
  1 + |kin m.1.1 m.1.2 m.2| + |t| * |g m.1.1 m.1.2|

/-- The actual weighted class supplies this recovery weight without an
unweighted displacement second-moment assumption. -/
theorem LegalWeightedStationaryPoissonMatching.integrable_gridRecoveryWeight
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) :
    Integrable (legalWeightedGridRecoveryWeight kin g t) (legalMarkedJointPalm q M.law) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  exact ((integrable_const 1).add M.kinetic_integrable.abs).add
    (M.probe_integrable.abs.const_mul |t|)

/-- The actual source-unit mean plan computes precisely the original weighted
stationary value, with the unchanged full q-dimensional kinetic kernel. -/
theorem LegalWeightedStationaryPoissonMatching.integral_sourceUnit_cost_eq_value
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    (∫ e, kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
      ∂legalMarkedSourceUnitMeanPlan q M.law) = M.value t := by
  let w : PhysicalPairPalmMark (Fin q) → ℝ := fun m ↦
    kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
  have hm : Measurable w := hk.add ((hg.comp measurable_fst).const_mul t)
  have heq := integral_map (μ := legalMarkedSourceUnitMeanPlan q M.law)
    measurable_physicalPairAnchor.snd.aemeasurable hm.aestronglyMeasurable
  rw [map_legalMarkedSourceUnitMeanPlan_pairMark] at heq
  change (∫ m, w m ∂legalMarkedJointPalm q M.law) =
    (∫ e, w (physicalPairAnchor e).2 ∂legalMarkedSourceUnitMeanPlan q M.law) at heq
  calc
    _ = ∫ m, w m ∂legalMarkedJointPalm q M.law := heq.symm
    _ = _ := by
      rw [integral_add M.kinetic_integrable (M.probe_integrable.const_mul t), integral_const_mul]
      rfl

/-- Removing actual boundary edges changes the original signed value by at
most their actual absolute signed cost; no replacement endpoint law is used. -/
theorem LegalWeightedStationaryPoissonMatching.value_sub_retained_cost_le_boundary
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t ell : ℝ) (phase : Fin q → ℝ) :
    ENNReal.ofReal |M.value t -
      ∫ e in {e : LegalMarkedPhysicalEdge q |
        shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1},
        kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
        ∂legalMarkedSourceUnitMeanPlan q M.law| ≤
      legalWeightedGridBoundaryLoss M ell phase
        (fun m ↦ |kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2|) := by
  let Γ := legalMarkedSourceUnitMeanPlan q M.law
  let K : Set (LegalMarkedPhysicalEdge q) :=
    {e | shiftedGridCells ell phase e.1.1 = shiftedGridCells ell phase e.2.1}
  let f : LegalMarkedPhysicalEdge q → ℝ := fun e ↦
    kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
  have hK : MeasurableSet K := measurableSet_legalWeightedGridRetained ell phase
  have hi : Integrable f Γ :=
    integrable_sourceUnitMeanPlan_palm_readout M _
      (M.kinetic_integrable.add (M.probe_integrable.const_mul t))
  have hpart : (∫ e, f e ∂Γ) - ∫ e in K, f e ∂Γ = ∫ e in Kᶜ, f e ∂Γ := by
    have hp := integral_add_compl hK hi
    linarith
  have hnorm : |∫ e in Kᶜ, f e ∂Γ| ≤ ∫ e in Kᶜ, |f e| ∂Γ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := f)
      (μ := (Γ.restrict Kᶜ))
  rw [← M.integral_sourceUnit_cost_eq_value hk hg t]
  change ENNReal.ofReal |(∫ e, f e ∂Γ) - ∫ e in K, f e ∂Γ| ≤ _
  rw [hpart]
  calc
    _ ≤ ENNReal.ofReal (∫ e in Kᶜ, |f e| ∂Γ) := ENNReal.ofReal_le_ofReal hnorm
    _ = ∫⁻ e in Kᶜ, ENNReal.ofReal |f e| ∂Γ :=
      ofReal_integral_eq_lintegral_ofReal hi.abs.restrict (.of_forall (fun _ ↦ abs_nonneg _))
    _ = _ := by
      rw [← lintegral_indicator hK.compl]
      apply lintegral_congr
      intro e
      simp only [Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq, K, f,
        physicalPairAnchor]

/-- Actual finite-cell boundaries lose simultaneously vanishing source
input density and original absolute signed cost for every weighted matching. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_gridRecovery_loss_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ phase,
      legalWeightedGridBoundaryLoss M (R n) phase (legalWeightedGridRecoveryWeight kin g t)
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  have hm : Measurable (legalWeightedGridRecoveryWeight kin g t) :=
    (measurable_const.add hk.abs).add ((hg.comp measurable_fst).abs.const_mul |t|)
  exact tendsto_lintegral_shiftedGrid_crossing_integrable_weight_zero q
    (legalMarkedSourceUnitMeanPlan q M.law)
    (fun e ↦ legalWeightedGridRecoveryWeight kin g t (physicalPairAnchor e).2)
    (hm.comp measurable_physicalPairAnchor.snd)
    (integrable_sourceUnitMeanPlan_palm_readout M _ (M.integrable_gridRecoveryWeight t))
    R hRpos hR

/-- The actual retained original cores recover the same weighted stationary
value in expected absolute error under the genuine independent grid phase.
This is a density statement for the original random-grid cutting operation. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_retained_grid_cost_error_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ phase, ENNReal.ofReal |M.value t -
      ∫ e in {e : LegalMarkedPhysicalEdge q |
        shiftedGridCells (R n) phase e.1.1 = shiftedGridCells (R n) phase e.2.1},
        kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
        ∂legalMarkedSourceUnitMeanPlan q M.law|
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (M.tendsto_gridRecovery_loss_zero hk hg t R hRpos hR) (fun _ ↦ zero_le)
  intro n
  apply lintegral_mono
  intro phase
  apply (M.value_sub_retained_cost_le_boundary hk hg t (R n) phase).trans
    (legalWeightedGridBoundaryLoss_mono M (R n) phase _ _ ?_)
  intro m
  dsimp [legalWeightedGridRecoveryWeight]
  calc
    |kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2| ≤
        |kin m.1.1 m.1.2 m.2| + |t * g m.1.1 m.1.2| := abs_add_le _ _
    _ = |kin m.1.1 m.1.2 m.2| + |t| * |g m.1.1 m.1.2| := by rw [abs_mul]
    _ ≤ _ := by linarith

/-- At every sufficiently large finite-cell scale one deterministic common
phase retains almost all original source density and recovers the original
same-kernel signed value. No second moment or reverse pressure inequality is
assumed, and the original matching and immutable input colors are unchanged. -/
theorem LegalWeightedStationaryPoissonMatching.eventually_exists_grid_core_recovery
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ phase : Fin q → ℝ,
      legalWeightedGridBoundaryLoss M (R n) phase (fun _ ↦ 1) < ENNReal.ofReal ε ∧
      ENNReal.ofReal |M.value t -
        ∫ e in {e : LegalMarkedPhysicalEdge q |
          shiftedGridCells (R n) phase e.1.1 = shiftedGridCells (R n) phase e.2.1},
          kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
          ∂legalMarkedSourceUnitMeanPlan q M.law| < ENNReal.ofReal ε := by
  have hε' : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hsmall := (M.tendsto_gridRecovery_loss_zero hk hg t R hRpos hR).eventually
    (eventually_lt_nhds hε')
  filter_upwards [hsmall] with n hn
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q (R n)) :=
    shiftedGridPhaseLaw_probability q (hRpos n)
  have hex : ∃ phase, legalWeightedGridBoundaryLoss M (R n) phase
      (legalWeightedGridRecoveryWeight kin g t) < ENNReal.ofReal ε := by
    by_contra hnot
    have hall : ∀ phase, ENNReal.ofReal ε ≤ legalWeightedGridBoundaryLoss M (R n) phase
        (legalWeightedGridRecoveryWeight kin g t) := by simpa only [not_exists, not_lt] using hnot
    have hb : ENNReal.ofReal ε ≤ ∫⁻ phase,
        legalWeightedGridBoundaryLoss M (R n) phase (legalWeightedGridRecoveryWeight kin g t)
        ∂shiftedGridPhaseLaw q (R n) := by
      calc
        _ = ∫⁻ _ : Fin q → ℝ, ENNReal.ofReal ε ∂shiftedGridPhaseLaw q (R n) := by simp
        _ ≤ _ := lintegral_mono hall
    exact hn.not_ge hb
  obtain ⟨phase, hphase⟩ := hex
  refine ⟨phase, ?_, ?_⟩
  · apply lt_of_le_of_lt (legalWeightedGridBoundaryLoss_mono M (R n) phase _ _ ?_) hphase
    intro m
    dsimp [legalWeightedGridRecoveryWeight]
    linarith [abs_nonneg (kin m.1.1 m.1.2 m.2),
      mul_nonneg (abs_nonneg t) (abs_nonneg (g m.1.1 m.1.2))]
  · apply lt_of_le_of_lt ((M.value_sub_retained_cost_le_boundary hk hg t (R n) phase).trans
      (legalWeightedGridBoundaryLoss_mono M (R n) phase _ _ ?_)) hphase
    intro m
    dsimp [legalWeightedGridRecoveryWeight]
    calc
      |kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2| ≤
          |kin m.1.1 m.1.2 m.2| + |t * g m.1.1 m.1.2| := abs_add_le _ _
      _ = |kin m.1.1 m.1.2 m.2| + |t| * |g m.1.1 m.1.2| := by rw [abs_mul]
      _ ≤ _ := by linarith

end OTSelector.Reconstruction
