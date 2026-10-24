import OTSelector.Reconstruction.OriginalLegalWeightedBipartiteCoreRecovery
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowBoundary
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalWeightedSourceReadout
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Actual growing original-window core recovery

The physical source cube is normalized by its literal volume `(2 R)^q`.
The original Campbell factorization averages its actual two-endpoint core,
including both original clock cutoffs, over the true normalized Haar root.
No source-unit phase witness is extrapolated to a whole finite window.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
local instance windowCoreRecoveryPlanPolish :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace
local instance windowCoreRecoveryInputPolish :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace

/-- A compact original physical window retains the spatial cube and unchanged
clock interval; growing the clock interval ultimately retains every clock. -/
def legalWeightedPhysicalWindow (q : ℕ) (R K : ℝ) : Set (LegalMarkedPhysicalPoint q) :=
  haarRootCube (Fin q) R ×ˢ Icc (-K) K

theorem isCompact_legalWeightedPhysicalWindow (q : ℕ) (R K : ℝ) :
    IsCompact (legalWeightedPhysicalWindow q R K) := isCompact_Icc.prod isCompact_Icc

/-- The original mean plan before any spatial or clock restriction. -/
def legalWeightedOriginalMeanPlan
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    Measure (LegalMarkedPhysicalEdge q) :=
  physicalSceneMeanPlan (legalMarkedInputPairLaw q M.law :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))

/-- Original source position and complete original mark identify the unchanged
mean edge measure with the true Campbell measure. -/
theorem legalWeightedOriginalMeanPlan_map_anchor
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    (legalWeightedOriginalMeanPlan M).map physicalPairAnchor =
      (volume : Measure (Fin q → ℝ)).prod (legalMarkedJointPalm q M.law) := by
  rw [← M.campbell_eq_volume_prod_palm]
  ext B hB
  rw [Measure.map_apply measurable_physicalPairAnchor hB, legalWeightedOriginalMeanPlan,
    physicalSceneMeanPlan, Measure.bind_apply (hB.preimage measurable_physicalPairAnchor)
      (Kernel.measurable _).aemeasurable,
    physicalScenePairCampbell, Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
  apply lintegral_congr
  intro s
  rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor hB]
  rfl

/-- Normalize the actual original source-cube plan by its true spatial volume. -/
def legalWeightedNormalizedSourceWindowPlan
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (R : ℝ) :
    Measure (LegalMarkedPhysicalEdge q) :=
  (ENNReal.ofReal ((2 * R) ^ q))⁻¹ •
    (legalWeightedOriginalMeanPlan M).restrict {e | e.1.1 ∈ haarRootCube (Fin q) R}

/-- Exact finite-window averaging: the normalized SAME original plan has the
literal Haar root times its own full q-dimensional Palm mark, with every clock
and displacement retained. The normalization is `(2 R)^(-q)`. -/
theorem legalWeightedNormalizedSourceWindowPlan_map_anchor
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (R : ℝ) :
    (legalWeightedNormalizedSourceWindowPlan M R).map physicalPairAnchor =
      (haarCubeRootLaw (Fin q) R).prod (legalMarkedJointPalm q M.law) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have hpre : physicalPairAnchor ⁻¹'
      (haarRootCube (Fin q) R ×ˢ (univ : Set (PhysicalPairPalmMark (Fin q)))) =
      {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ haarRootCube (Fin q) R} := by
    ext e
    simp only [mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]
    rfl
  rw [legalWeightedNormalizedSourceWindowPlan, Measure.map_smul, ← hpre,
    ← Measure.restrict_map measurable_physicalPairAnchor
      (show MeasurableSet (haarRootCube (Fin q) R ×ˢ
        (univ : Set (PhysicalPairPalmMark (Fin q)))) from measurableSet_Icc.prod .univ),
    legalWeightedOriginalMeanPlan_map_anchor, ← Measure.restrict_prod_eq_prod_univ]
  rw [haarCubeRootLaw, cavityRootMeasure, Measure.prod_smul_left, Fintype.card_fin]

/-- Every fixed original displacement leaves a vanishing fraction of the true
normalized growing root cube, without any displacement moment assumption. -/
theorem tendsto_haarCubeRootLaw_displacement_escape_zero
    (d : Fin q → ℝ) (R : ℕ → ℝ) (_hR : ∀ n, 0 < R n)
    (hlarge : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ haarCubeRootLaw (Fin q) (R n)
      {x | x + d ∉ haarRootCube (Fin q) (R n)}) atTop (𝓝 0) := by
  have hb := (tendsto_haarCubeRootLaw_inner_compl q (norm_nonneg d)).comp hlarge
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ ↦ bot_le)
  intro n
  apply measure_mono
  intro x hx hinner
  apply hx
  constructor <;> intro i
  · have hi := (abs_le.mp (show |d i| ≤ ‖d‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm d i)).1
    have hi' := hinner.1 i
    change -(R n - ‖d‖) ≤ x i at hi'
    change -(R n) ≤ x i + d i
    linarith
  · have hi := (abs_le.mp (show |d i| ≤ ‖d‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm d i)).2
    have hi' := hinner.2 i
    change x i ≤ R n - ‖d‖ at hi'
    change x i + d i ≤ R n
    linarith

/-- Whether the same original anchored edge survives BOTH clock cutoffs and
the actual target-spatial boundary of the original source cube. -/
def legalWeightedWindowKeep (R K : ℝ)
    (p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) : Prop :=
  p.1 ∈ haarRootCube (Fin q) R ∧ p.2.1.1 ∈ Icc (-K) K ∧
    p.2.1.2 ∈ Icc (-K) K ∧ p.1 + p.2.2 ∈ haarRootCube (Fin q) R

theorem measurableSet_legalWeightedWindowKeep (R K : ℝ) :
    MeasurableSet {p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) |
      legalWeightedWindowKeep R K p} :=
  (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd.fst.fst).inter
      ((measurableSet_Icc.preimage measurable_snd.fst.snd).inter
        (measurableSet_Icc.preimage (measurable_fst.add measurable_snd.snd))))

/-- The true normalized finite-window removed-weight budget, averaged over the
original paired mark and the actual finite-cube root. -/
def legalWeightedWindowRecoveryLoss
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (R K : ℝ) (w : PhysicalPairPalmMark (Fin q) → ℝ) : ℝ≥0∞ :=
  ∫⁻ m, ∫⁻ x, if legalWeightedWindowKeep R K (x, m) then 0 else ENNReal.ofReal (w m)
    ∂haarCubeRootLaw (Fin q) R ∂legalMarkedJointPalm q M.law

/-- The actual window budget tends to zero for every original integrable Palm
weight. Clock cutoffs are removed and the root boundary vanishes internally. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_windowRecoveryLoss_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (w : PhysicalPairPalmMark (Fin q) → ℝ) (hw : Measurable w)
    (hi : Integrable w (legalMarkedJointPalm q M.law))
    (R K : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hlarge : Tendsto R atTop atTop) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n ↦ legalWeightedWindowRecoveryLoss M (R n) (K n) w) atTop (𝓝 0) := by
  let F (n : ℕ) (m : PhysicalPairPalmMark (Fin q)) :=
    ∫⁻ x, if legalWeightedWindowKeep (R n) (K n) (x, m) then 0
      else ENNReal.ofReal (w m) ∂haarCubeRootLaw (Fin q) (R n)
  have hFm (n : ℕ) : Measurable (F n) := by
    let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) (R n)) :=
      isProbabilityMeasure_haarCubeRootLaw (Fin q) (hR n)
    have hm : Measurable (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
        if legalWeightedWindowKeep (R n) (K n) p then (0 : ℝ≥0∞)
          else ENNReal.ofReal (w p.2)) :=
      measurable_const.ite (measurableSet_legalWeightedWindowKeep (R n) (K n))
        ((hw.comp measurable_snd).ennreal_ofReal)
    exact (hm.comp measurable_swap).lintegral_prod_right'
  have hbound (n : ℕ) (m : PhysicalPairPalmMark (Fin q)) :
      F n m ≤ ENNReal.ofReal (w m) := by
    let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) (R n)) :=
      isProbabilityMeasure_haarCubeRootLaw (Fin q) (hR n)
    calc
      _ ≤ ∫⁻ _, ENNReal.ofReal (w m) ∂haarCubeRootLaw (Fin q) (R n) := by
        apply lintegral_mono
        intro x
        dsimp only
        split_ifs <;> simp
      _ = _ := by simp
  have hpoint (m : PhysicalPairPalmMark (Fin q)) :
      Tendsto (fun n ↦ F n m) atTop (𝓝 0) := by
    have hclock := hK.eventually (eventually_ge_atTop (max |m.1.1| |m.1.2|))
    have hb := tendsto_haarCubeRootLaw_displacement_escape_zero m.2 R hR hlarge
    have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (w m)) hb (Or.inr ENNReal.ofReal_ne_top)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hclock] with n hn
    have hs : m.1.1 ∈ Icc (-(K n)) (K n) :=
      abs_le.mp ((le_max_left _ _).trans hn)
    have ht : m.1.2 ∈ Icc (-(K n)) (K n) :=
      abs_le.mp ((le_max_right _ _).trans hn)
    have hm : MeasurableSet {x : Fin q → ℝ | x + m.2 ∉ haarRootCube (Fin q) (R n)} :=
      (measurableSet_Icc.preimage (measurable_id.add measurable_const)).compl
    have hroot : ∀ᵐ x ∂haarCubeRootLaw (Fin q) (R n),
        x ∈ haarRootCube (Fin q) (R n) := by
      rw [haarCubeRootLaw, cavityRootMeasure]
      exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
    calc
      _ = ∫⁻ x, if x + m.2 ∈ haarRootCube (Fin q) (R n) then 0
          else ENNReal.ofReal (w m) ∂haarCubeRootLaw (Fin q) (R n) := by
        simpa only [Set.indicator, mem_ofPred_eq, ite_not] using
          (lintegral_indicator_const (μ := haarCubeRootLaw (Fin q) (R n)) hm
            (ENNReal.ofReal (w m))).symm
      _ = F n m := by
        apply lintegral_congr_ae
        filter_upwards [hroot] with x hx
        simp only [legalWeightedWindowKeep, hx, hs, ht, true_and]

  have hfin : (∫⁻ m, ENNReal.ofReal (w m) ∂legalMarkedJointPalm q M.law) ≠ ⊤ := by
    have h := (hasFiniteIntegral_iff_ofReal
      (.of_forall (fun m ↦ le_max_right (w m) 0))).mp hi.pos_part.hasFiniteIntegral
    simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show (0 : ℝ≥0∞) ≤ _ from zero_le)] using h.ne
  have h := tendsto_lintegral_of_dominated_convergence (fun m ↦ ENNReal.ofReal (w m)) hFm
    (fun n ↦ .of_forall (hbound n)) hfin (.of_forall hpoint)
  simpa only [legalWeightedWindowRecoveryLoss, F, lintegral_zero] using h

/-- The anchored survivor predicate is exactly the literal two-endpoint
physical window, including both unchanged original scalar clocks. -/
theorem legalWeightedWindowKeep_anchor_iff (R K : ℝ) (e : LegalMarkedPhysicalEdge q) :
    legalWeightedWindowKeep R K (physicalPairAnchor e) ↔
      e ∈ legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K := by
  simp only [legalWeightedWindowKeep, legalWeightedPhysicalWindow, mem_prod,
    physicalPairAnchor, add_sub_cancel]
  tauto

/-- The true root/Palm removed-weight budget equals the complement integral of
the SAME normalized original source-window mean plan. -/
theorem legalWeightedWindowRecoveryLoss_eq_normalized_plan
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (K : ℝ) (w : PhysicalPairPalmMark (Fin q) → ℝ) (hw : Measurable w) :
    legalWeightedWindowRecoveryLoss M R K w =
      ∫⁻ e in (legalWeightedPhysicalWindow q R K ×ˢ
        legalWeightedPhysicalWindow q R K)ᶜ, ENNReal.ofReal (w (physicalPairAnchor e).2)
          ∂legalWeightedNormalizedSourceWindowPlan M R := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) R) :=
    isProbabilityMeasure_haarCubeRootLaw (Fin q) hR
  let F : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞ :=
    fun p ↦ if legalWeightedWindowKeep R K p then 0 else ENNReal.ofReal (w p.2)
  have hF : Measurable F := measurable_const.ite
    (measurableSet_legalWeightedWindowKeep R K) ((hw.comp measurable_snd).ennreal_ofReal)
  have hswap : legalWeightedWindowRecoveryLoss M R K w =
      ∫⁻ p, F p ∂(haarCubeRootLaw (Fin q) R).prod (legalMarkedJointPalm q M.law) := by
    rw [lintegral_prod _ hF.aemeasurable]
    exact lintegral_lintegral_swap (hF.comp measurable_swap).aemeasurable
  rw [hswap, ← legalWeightedNormalizedSourceWindowPlan_map_anchor M R,
    lintegral_map hF measurable_physicalPairAnchor,
    ← lintegral_indicator
      ((isCompact_legalWeightedPhysicalWindow q R K).measurableSet.prod
        (isCompact_legalWeightedPhysicalWindow q R K).measurableSet).compl]
  apply lintegral_congr
  intro e
  simp only [F, legalWeightedWindowKeep_anchor_iff, Set.indicator, mem_compl_iff]
  split_ifs <;> rfl

/-- Every nonnegative original edge observable averages literally over the
same original scene law, before any finite-window extraction. -/
theorem lintegral_legalWeightedOriginalMeanPlan
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (f : LegalMarkedPhysicalEdge q → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ e, f e ∂legalWeightedOriginalMeanPlan M) =
      ∫⁻ s, ∫⁻ e, f e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  rw [legalWeightedOriginalMeanPlan, lintegral_physicalSceneMeanPlan _ hf]
  exact lintegral_map (hf.lintegral_kernel (κ := physicalScenePlanKernel)) measurable_fst

/-- Exact actual finite-window budget with the literal inverse spatial volume.
The outer measure is the original M.law; its selected ports receive no new law. -/
theorem legalWeightedWindowRecoveryLoss_eq_actual_scene
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (K : ℝ) (w : PhysicalPairPalmMark (Fin q) → ℝ) (hw : Measurable w) :
    legalWeightedWindowRecoveryLoss M R K w = (ENNReal.ofReal ((2 * R) ^ q))⁻¹ *
      ∫⁻ s, ∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ haarRootCube (Fin q) R},
        (if e ∈ legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K
          then 0 else ENNReal.ofReal (w (physicalPairAnchor e).2))
        ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))
          ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hU := (isCompact_legalWeightedPhysicalWindow q R K).measurableSet
  let f : LegalMarkedPhysicalEdge q → ℝ≥0∞ :=
    fun e ↦ if e ∈ legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K
      then 0 else ENNReal.ofReal (w (physicalPairAnchor e).2)
  have hf : Measurable f := measurable_const.ite (hU.prod hU)
    ((hw.comp measurable_physicalPairAnchor.snd).ennreal_ofReal)
  have hW : MeasurableSet {e : LegalMarkedPhysicalEdge q |
      e.1.1 ∈ haarRootCube (Fin q) R} := measurableSet_Icc.preimage measurable_fst.fst
  rw [legalWeightedWindowRecoveryLoss_eq_normalized_plan M hR K w hw,
    ← lintegral_indicator (hU.prod hU).compl]
  have heq : (legalWeightedPhysicalWindow q R K ×ˢ
      legalWeightedPhysicalWindow q R K)ᶜ.indicator
        (fun e ↦ ENNReal.ofReal (w (physicalPairAnchor e).2)) = f := by
    funext e
    simp only [f, Set.indicator, mem_compl_iff]
    split_ifs <;> rfl
  rw [heq, legalWeightedNormalizedSourceWindowPlan, lintegral_smul_measure]
  congr 1
  rw [← lintegral_indicator hW, lintegral_legalWeightedOriginalMeanPlan M _ (hf.indicator hW)]
  apply lintegral_congr
  intro s
  exact lintegral_indicator hW f

/-- The original normalized source-window plan is probability, produced from
its actual Campbell law and its actual positive physical volume. -/
theorem LegalWeightedStationaryPoissonMatching.normalizedSourceWindowPlan_probability
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (legalWeightedNormalizedSourceWindowPlan M R) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) R) :=
    isProbabilityMeasure_haarCubeRootLaw (Fin q) hR
  have : IsProbabilityMeasure ((legalWeightedNormalizedSourceWindowPlan M R).map
      physicalPairAnchor) := by
    rw [legalWeightedNormalizedSourceWindowPlan_map_anchor]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map physicalPairAnchor

/-- Any actual edge set inside the source cube has its literal original
mean count divided by the exact physical cube volume. -/
theorem legalWeightedNormalizedSourceWindowPlan_apply
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (R : ℝ)
    {A : Set (LegalMarkedPhysicalEdge q)} (hA : MeasurableSet A)
    (hsub : A ⊆ {e | e.1.1 ∈ haarRootCube (Fin q) R}) :
    legalWeightedNormalizedSourceWindowPlan M R A =
      (ENNReal.ofReal ((2 * R) ^ q))⁻¹ * legalWeightedOriginalMeanPlan M A := by
  rw [legalWeightedNormalizedSourceWindowPlan, Measure.smul_apply,
    Measure.restrict_apply hA, inter_eq_left.mpr hsub, smul_eq_mul]

/-- Actual original retained mass per true spatial volume. -/
def legalWeightedWindowCoreDensity
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (R K : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ((2 * R) ^ q))⁻¹ * legalWeightedOriginalMeanPlan M
    (legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K)

theorem legalWeightedWindowCoreDensity_eq_normalized_plan
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (R K : ℝ) :
    legalWeightedWindowCoreDensity M R K = legalWeightedNormalizedSourceWindowPlan M R
      (legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K) := by
  symm
  exact legalWeightedNormalizedSourceWindowPlan_apply M R
    ((isCompact_legalWeightedPhysicalWindow q R K).measurableSet.prod
      (isCompact_legalWeightedPhysicalWindow q R K).measurableSet) (fun _ he ↦ he.1.1)

/-- The actual retained finite-window density and its complete removed mass
partition one, with the exact same original window and volume normalization. -/
theorem legalWeightedWindowCoreDensity_add_recoveryLoss_eq_one
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (K : ℝ) :
    legalWeightedWindowCoreDensity M R K + legalWeightedWindowRecoveryLoss M R K (fun _ ↦ 1) = 1 := by
  let : IsProbabilityMeasure (legalWeightedNormalizedSourceWindowPlan M R) :=
    M.normalizedSourceWindowPlan_probability hR
  rw [legalWeightedWindowCoreDensity_eq_normalized_plan,
    legalWeightedWindowRecoveryLoss_eq_normalized_plan M hR K _ measurable_const]
  simp only [ENNReal.ofReal_one, lintegral_const, Measure.restrict_apply_univ, one_mul]
  rw [measure_add_measure_compl
    ((isCompact_legalWeightedPhysicalWindow q R K).measurableSet.prod
      (isCompact_legalWeightedPhysicalWindow q R K).measurableSet), measure_univ]

/-- The exact complementary actual finite-window mass. -/
theorem legalWeightedWindowRecoveryLoss_one_eq_sub_density
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (K : ℝ) :
    legalWeightedWindowRecoveryLoss M R K (fun _ ↦ 1) =
      1 - legalWeightedWindowCoreDensity M R K := by
  exact ENNReal.eq_sub_of_add_eq' (by simp)
    (by simpa only [add_comm] using legalWeightedWindowCoreDensity_add_recoveryLoss_eq_one M hR K)

/-- The normalized number of actual original source ports of the finite
window is bounded by the genuine whole-window removed-mass budget. -/
theorem legalWeightedWindow_source_ports_le_recoveryLoss
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (K : ℝ) :
    (ENNReal.ofReal ((2 * R) ^ q))⁻¹ * legalWeightedOriginalMeanPlan M
      (legalWeightedPhysicalWindow q R K ×ˢ (legalWeightedPhysicalWindow q R K)ᶜ) ≤
        legalWeightedWindowRecoveryLoss M R K (fun _ ↦ 1) := by
  have hU := (isCompact_legalWeightedPhysicalWindow q R K).measurableSet
  rw [← legalWeightedNormalizedSourceWindowPlan_apply M R (hU.prod hU.compl)
      (fun _ he ↦ he.1.1),
    legalWeightedWindowRecoveryLoss_eq_normalized_plan M hR K _ measurable_const]
  simp only [ENNReal.ofReal_one, lintegral_const, Measure.restrict_apply_univ, one_mul]
  apply measure_mono
  intro e he he'
  exact he.2 he'.2

/-- The SAME original retained core also has vanishing target ports. The
actual target intensity bounds the entire target-window count; its unchanged
core cardinality is the same as the source cardinality. -/
theorem legalWeightedWindow_target_ports_le_recoveryLoss
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (K : ℝ) :
    (ENNReal.ofReal ((2 * R) ^ q))⁻¹ * legalWeightedOriginalMeanPlan M
      ((legalWeightedPhysicalWindow q R K)ᶜ ×ˢ legalWeightedPhysicalWindow q R K) ≤
        legalWeightedWindowRecoveryLoss M R K (fun _ ↦ 1) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure β := by
    rw [← M.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  let U := legalWeightedPhysicalWindow q R K
  let Γ := legalWeightedOriginalMeanPlan M
  have hU : MeasurableSet U := (isCompact_legalWeightedPhysicalWindow q R K).measurableSet
  have htarget : Γ.snd = (volume : Measure (Fin q → ℝ)).prod β := by
    exact (physicalSceneMeanPlan_map_snd _).trans
      (M.targetIntensity_eq_inputColorIntensity.trans M.inputColorIntensities_eq_volume_prod.2)
  have hsplit : Γ (U ×ˢ U) + Γ (Uᶜ ×ˢ U) = Γ.snd U := by
    rw [Measure.snd, Measure.map_apply measurable_snd hU]
    have heq : Prod.snd ⁻¹' U = (U ×ˢ U) ∪ (Uᶜ ×ˢ U) := by
      ext e
      simp only [mem_preimage, mem_union, mem_prod, mem_compl_iff]
      tauto
    rw [heq]
    exact (measure_union (by
      apply disjoint_left.mpr
      intro e he he'
      exact he'.1 he.1) (hU.compl.prod hU)).symm
  have hscaled : legalWeightedWindowCoreDensity M R K +
      (ENNReal.ofReal ((2 * R) ^ q))⁻¹ * Γ (Uᶜ ×ˢ U) ≤ 1 := by
    change (ENNReal.ofReal ((2 * R) ^ q))⁻¹ * Γ (U ×ˢ U) + _ ≤ _
    rw [← mul_add, hsplit, htarget]
    change (ENNReal.ofReal ((2 * R) ^ q))⁻¹ *
      ((volume : Measure (Fin q → ℝ)).prod β)
        (haarRootCube (Fin q) R ×ˢ Icc (-K) K) ≤ 1
    rw [Measure.prod_prod, volume_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    calc
      _ ≤ (ENNReal.ofReal ((2 * R) ^ q))⁻¹ * (ENNReal.ofReal ((2 * R) ^ q) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (prob_le_one (μ := β)) zero_le) zero_le
      _ = 1 := by
        rw [mul_one, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) q)).ne'
          ENNReal.ofReal_ne_top]
  have hfinite : legalWeightedWindowCoreDensity M R K ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) ((le_add_right le_rfl).trans hscaled)
  rw [legalWeightedWindowRecoveryLoss_one_eq_sub_density M hR K]
  exact ENNReal.le_sub_of_add_le_left hfinite hscaled

/-- The actual whole-window retained density tends to one under the literal
normalization, without a displacement second moment or any reserve repair. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_windowCoreDensity_one
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (R K : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hlarge : Tendsto R atTop atTop) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n ↦ legalWeightedWindowCoreDensity M (R n) (K n)) atTop (𝓝 1) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have h := M.tendsto_windowRecoveryLoss_zero (fun _ ↦ 1) measurable_const
    (integrable_const 1) R K hR hlarge hK
  have hsub := (ENNReal.continuous_sub_left (a := 1) (by simp)).continuousAt.tendsto.comp h
  have hsub' : Tendsto (fun n ↦ 1 - legalWeightedWindowRecoveryLoss M (R n) (K n)
      (fun _ ↦ 1)) atTop (𝓝 1) := by simpa only [Function.comp_def, tsub_zero] using hsub
  apply hsub'.congr'
  filter_upwards [] with n
  have heq := legalWeightedWindowCoreDensity_add_recoveryLoss_eq_one M (hR n) (K n)
  simpa only [tsub_zero] using (ENNReal.sub_eq_of_eq_add' (by simp) heq.symm)

/-- Both actual original finite-window escape densities tend to zero for the
same retained matching and the same real growing physical windows. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_both_window_ports_zero
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (R K : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hlarge : Tendsto R atTop atTop) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n ↦ (ENNReal.ofReal ((2 * R n) ^ q))⁻¹ * legalWeightedOriginalMeanPlan M
      (legalWeightedPhysicalWindow q (R n) (K n) ×ˢ
        (legalWeightedPhysicalWindow q (R n) (K n))ᶜ)) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ (ENNReal.ofReal ((2 * R n) ^ q))⁻¹ * legalWeightedOriginalMeanPlan M
      ((legalWeightedPhysicalWindow q (R n) (K n))ᶜ ×ˢ
        legalWeightedPhysicalWindow q (R n) (K n))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have h := M.tendsto_windowRecoveryLoss_zero (fun _ ↦ 1) measurable_const
    (integrable_const 1) R K hR hlarge hK
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
      (fun n ↦ legalWeightedWindow_source_ports_le_recoveryLoss M (hR n) (K n))
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
      (fun n ↦ legalWeightedWindow_target_ports_le_recoveryLoss M (hR n) (K n))

/-- Integrable original Palm observables remain integrable on the actual
normalized finite source cube, without a second-moment assumption. -/
theorem integrable_normalizedSourceWindowPlan_palm_readout
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (w : PhysicalPairPalmMark (Fin q) → ℝ)
    (hi : Integrable w (legalMarkedJointPalm q M.law)) :
    Integrable (fun e ↦ w (physicalPairAnchor e).2)
      (legalWeightedNormalizedSourceWindowPlan M R) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) R) :=
    isProbabilityMeasure_haarCubeRootLaw (Fin q) hR
  have h : Integrable (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦ w p.2)
      ((legalWeightedNormalizedSourceWindowPlan M R).map physicalPairAnchor) := by
    rw [legalWeightedNormalizedSourceWindowPlan_map_anchor]
    exact hi.comp_snd _
  exact h.comp_measurable measurable_physicalPairAnchor

/-- The full original signed Palm readout is exactly its normalized actual
source-cube mean, for every positive true cube radius. -/
theorem integral_normalizedSourceWindowPlan_palm_readout
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (w : PhysicalPairPalmMark (Fin q) → ℝ) (hw : Measurable w) :
    (∫ e, w (physicalPairAnchor e).2 ∂legalWeightedNormalizedSourceWindowPlan M R) =
      ∫ m, w m ∂legalMarkedJointPalm q M.law := by
  let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) R) :=
    isProbabilityMeasure_haarCubeRootLaw (Fin q) hR
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  have he := integral_map (μ := legalWeightedNormalizedSourceWindowPlan M R)
    measurable_physicalPairAnchor.aemeasurable
    ((hw.comp measurable_snd).aestronglyMeasurable)
  rw [legalWeightedNormalizedSourceWindowPlan_map_anchor] at he
  simp only [Function.comp_def] at he
  rw [integral_fun_snd, probReal_univ, one_smul] at he
  exact he.symm

/-- The original same-matrix signed cost of the actual retained window core,
normalized only by its true source-cube volume. -/
def legalWeightedWindowCoreCost
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (R K t : ℝ) : ℝ :=
  ∫ e in legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K,
    kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
      ∂legalWeightedNormalizedSourceWindowPlan M R

/-- Exact measure restriction removes no original coordinates and introduces
only the literal inverse cube-volume normalization. -/
theorem legalWeightedNormalizedSourceWindowPlan_restrict_core
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (R K : ℝ) :
    (legalWeightedNormalizedSourceWindowPlan M R).restrict
        (legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K) =
      (ENNReal.ofReal ((2 * R) ^ q))⁻¹ • (legalWeightedOriginalMeanPlan M).restrict
        (legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K) := by
  rw [legalWeightedNormalizedSourceWindowPlan, Measure.restrict_smul]
  congr 1
  exact Measure.restrict_restrict_of_subset (fun _ he ↦ he.1.1)

/-- The retained signed mean cost is the actual original core integral divided
by `(2 R)^q`, with its complete original matrix kernel and paired probe. -/
theorem legalWeightedWindowCoreCost_eq_normalized_original_integral
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) {R : ℝ} (hR : 0 < R)
    (K t : ℝ) :
    legalWeightedWindowCoreCost M R K t = ((2 * R) ^ q)⁻¹ *
      ∫ e in legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K,
        kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
          ∂legalWeightedOriginalMeanPlan M := by
  rw [legalWeightedWindowCoreCost, legalWeightedNormalizedSourceWindowPlan_restrict_core,
    integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- Actual removed original absolute signed cost bounds the error of the SAME
finite core's original signed cost, with no desired-value callback. -/
theorem LegalWeightedStationaryPoissonMatching.value_sub_windowCoreCost_le_loss
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) {R : ℝ} (hR : 0 < R) (K t : ℝ) :
    ENNReal.ofReal |M.value t - legalWeightedWindowCoreCost M R K t| ≤
      legalWeightedWindowRecoveryLoss M R K
        (fun m ↦ |kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2|) := by
  let w : PhysicalPairPalmMark (Fin q) → ℝ :=
    fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
  have hw : Measurable w := hk.add ((hg.comp measurable_fst).const_mul t)
  have hi : Integrable w (legalMarkedJointPalm q M.law) :=
    M.kinetic_integrable.add (M.probe_integrable.const_mul t)
  let Γ := legalWeightedNormalizedSourceWindowPlan M R
  let A := legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K
  have hA : MeasurableSet A := (isCompact_legalWeightedPhysicalWindow q R K).measurableSet.prod
    (isCompact_legalWeightedPhysicalWindow q R K).measurableSet
  let f : LegalMarkedPhysicalEdge q → ℝ := fun e ↦ w (physicalPairAnchor e).2
  have hfi : Integrable f Γ := integrable_normalizedSourceWindowPlan_palm_readout M hR w hi
  have hvalue : (∫ e, f e ∂Γ) = M.value t := by
    rw [integral_normalizedSourceWindowPlan_palm_readout M hR w hw]
    rw [integral_add M.kinetic_integrable (M.probe_integrable.const_mul t), integral_const_mul]
    rfl
  have hpart : (∫ e, f e ∂Γ) - ∫ e in A, f e ∂Γ = ∫ e in Aᶜ, f e ∂Γ := by
    have hp := integral_add_compl hA hfi
    linarith
  have hnorm : |∫ e in Aᶜ, f e ∂Γ| ≤ ∫ e in Aᶜ, |f e| ∂Γ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f := f) (μ := Γ.restrict Aᶜ)
  rw [legalWeightedWindowRecoveryLoss_eq_normalized_plan M hR K _ hw.abs]
  change ENNReal.ofReal |M.value t - ∫ e in A, f e ∂Γ| ≤
    ∫⁻ e in Aᶜ, ENNReal.ofReal |f e| ∂Γ
  rw [← hvalue, hpart]
  exact (ENNReal.ofReal_le_ofReal hnorm).trans_eq
    (ofReal_integral_eq_lintegral_ofReal hfi.abs.restrict (.of_forall (fun _ ↦ abs_nonneg _)))

/-- The actual original finite-window signed core value converges to the
SAME weighted candidate's value under the literal spatial normalization. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_windowCoreCost_value
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (R K : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hlarge : Tendsto R atTop atTop) (hK : Tendsto K atTop atTop) :
    Tendsto (fun n ↦ legalWeightedWindowCoreCost M (R n) (K n) t) atTop (𝓝 (M.value t)) := by
  have hw : Measurable (fun m : PhysicalPairPalmMark (Fin q) ↦
      |kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2|) :=
    (hk.add ((hg.comp measurable_fst).const_mul t)).abs
  have hi := (M.kinetic_integrable.add (M.probe_integrable.const_mul t)).abs
  have hbudget := M.tendsto_windowRecoveryLoss_zero _ hw hi R K hR hlarge hK
  have hzero : Tendsto (fun n ↦ ENNReal.ofReal
      |M.value t - legalWeightedWindowCoreCost M (R n) (K n) t|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbudget (fun _ ↦ bot_le)
      (fun n ↦ M.value_sub_windowCoreCost_le_loss hk hg (hR n) (K n) t)
  have habs := (ENNReal.tendsto_toReal (by simp)).comp hzero
  simp only [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_zero] at habs
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr
    (by simpa only [Real.norm_eq_abs, abs_sub_comm] using habs)

/-- Exact expected original set counts are unchanged by any genuine joining
whose scene marginal is the complete original M.law. -/
theorem legalWeightedOriginalMeanPlan_apply_eq_joining
    {Z : Type*} [MeasurableSpace Z]
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (J : Measure (LegalMarkedOptimalInputScene q × Z))
    (hleft : J.map Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)))
    {A : Set (LegalMarkedPhysicalEdge q)} (hA : MeasurableSet A) :
    legalWeightedOriginalMeanPlan M A =
      ∫⁻ p, (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) A ∂J := by
  have hmean := lintegral_legalWeightedOriginalMeanPlan M
    (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) (measurable_const.indicator hA)
  simp only [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ,
    one_mul] at hmean
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) A) :=
    (Measure.measurable_coe hA).comp
      (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  have he := lintegral_map (μ := J) hm measurable_fst
  rw [hleft] at he
  exact hmean.trans he

/-- Integrable original edge observables have their actual original scene
expectation, with integrability of that scene observable produced internally. -/
theorem integral_legalWeightedOriginalMeanPlan
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (f : LegalMarkedPhysicalEdge q → ℝ) (hi : Integrable f (legalWeightedOriginalMeanPlan M)) :
    Integrable (fun s : LegalMarkedOptimalInputScene q ↦
      ∫ e, f e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)))
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    (∫ e, f e ∂legalWeightedOriginalMeanPlan M) =
      ∫ s, ∫ e, f e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let P := (legalMarkedInputPairLaw q M.law :
    Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
  have hki : Integrable f (physicalScenePlanKernel ∘ₘ P) := hi
  rw [Measure.comp_eq_comp_const_apply] at hki
  have hscene : Integrable (fun scene ↦ ∫ e, f e ∂physicalScenePlanKernel scene) P := by
    simpa only [Kernel.const_apply] using hki.integral_comp
  have he := integral_bind_kernel_vector_eq_integral_integral P physicalScenePlanKernel hi
  have hmap := integral_map (μ := (M.law : Measure (LegalMarkedOptimalInputScene q)))
    measurable_fst.aemeasurable hscene.aestronglyMeasurable
  exact ⟨hscene.comp_measurable measurable_fst, he.trans hmap⟩

/-- The actual finite-core scene signed cost is integrable and its normalized
expectation is exactly the same original window core value. -/
theorem LegalWeightedStationaryPoissonMatching.windowCoreCost_eq_actual_scene
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {R : ℝ} (hR : 0 < R) (K t : ℝ) :
    Integrable (fun s : LegalMarkedOptimalInputScene q ↦
      ∫ e in legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K,
        kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
          ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)))
      (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
    legalWeightedWindowCoreCost M R K t = ((2 * R) ^ q)⁻¹ *
      ∫ s, ∫ e in legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K,
        kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
          ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))
            ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let A := legalWeightedPhysicalWindow q R K ×ˢ legalWeightedPhysicalWindow q R K
  have hA : MeasurableSet A := (isCompact_legalWeightedPhysicalWindow q R K).measurableSet.prod
    (isCompact_legalWeightedPhysicalWindow q R K).measurableSet
  let f : LegalMarkedPhysicalEdge q → ℝ :=
    fun e ↦ kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
  have hi : Integrable f (legalWeightedNormalizedSourceWindowPlan M R) :=
    integrable_normalizedSourceWindowPlan_palm_readout M hR _
      (M.kinetic_integrable.add (M.probe_integrable.const_mul t))
  have hcore := hi.restrict (s := A)
  rw [legalWeightedNormalizedSourceWindowPlan_restrict_core] at hcore
  have hc0 : (ENNReal.ofReal ((2 * R) ^ q))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hcfin : (ENNReal.ofReal ((2 * R) ^ q))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) q)).ne'
  have hfi : Integrable (A.indicator f) (legalWeightedOriginalMeanPlan M) := by
    apply (integrable_indicator_iff hA).mpr
    exact (integrable_smul_measure hc0 hcfin).mp hcore
  have h := integral_legalWeightedOriginalMeanPlan M (A.indicator f) hfi
  simp only [integral_indicator hA] at h
  refine ⟨h.1, ?_⟩
  rw [legalWeightedWindowCoreCost_eq_normalized_original_integral M hR K t, h.2]

/-- An actual finite-index core witness records the SAME original plan on the
literal original Poisson window arrays and exact source/target port counts. -/
def IsOriginalLegalWeightedWindowCore
    (q : ℕ) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    (R K t : ℝ)
    (p : LegalMarkedOptimalInputScene q ×
      (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))) : Prop :=
  let U := legalWeightedPhysicalWindow q R K
  let source := legalOriginalBlockRestriction U p.2.1
  let target := legalOriginalBlockRestriction U p.2.2
  ∃ σ : OTSelector.PartialMatching source.1 target.1,
    PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (source.2 i).2)
      (fun j ↦ (target.2 j).2)) σ ∧
    (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U) =
      ∑ e ∈ σ.edges, Measure.dirac (source.2 e.1, target.2 e.2) ∧
    (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ U) = (σ.card : ℝ≥0∞) ∧
    Integrable (fun e ↦ kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2)
      ((p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U)) ∧
    (∫ e in U ×ˢ U, kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
      ∂(p.1.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
      σ.cost (fun i j ↦ kin (source.2 i).2 (target.2 j).2
        ((target.2 j).1 - (source.2 i).1) + t * g (source.2 i).2 (target.2 j).2) ∧
    ((source.1 - σ.card : ℕ) : ℝ) =
      ((p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)).toReal ∧
    ((target.1 - σ.card : ℕ) : ℝ) =
      ((p.1.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Uᶜ ×ˢ U)).toReal

/-- A complete growing compact physical window lies inside one concrete grid
cell. This only reuses the already proved exact original finite-core producer;
the whole-window budget is proved separately from Campbell averaging. -/
theorem legalWeightedPhysicalWindow_in_one_grid_cell {R : ℝ} (hR : 0 < R) (K : ℝ) :
    ∀ x ∈ legalWeightedPhysicalWindow q R K,
      shiftedGridCells (4 * R) (fun _ ↦ -2 * R) x.1 = (fun _ ↦ 0) := by
  intro x hx
  funext i
  change ⌊(x.1 i - -2 * R) / (4 * R)⌋ = 0
  rw [Int.floor_eq_zero_iff]
  have hlo := hx.1.1 i
  have hhi := hx.1.2 i
  change -R ≤ x.1 i at hlo
  change x.1 i ≤ R at hhi
  exact ⟨div_nonneg (by linarith) (by positivity),
    (div_lt_one (by positivity : 0 < 4 * R)).mpr (by linarith)⟩

/-- Every true window admits a literal original-Poisson joining and an exact
legal core σ. Both capacities, signed cost and port counts come from the same
original plan; the clock laws are normalized internally from M. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalPoisson_windowCore
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hq : 0 < q) {R : ℝ} (hR : 0 < R) (K t : ℝ) :
    ∃ S > 0, ∃ J : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (J : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (J : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.snd = legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(J : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        IsOriginalLegalWeightedWindowCore q kin g R K t p := by
  have hcell := legalWeightedPhysicalWindow_in_one_grid_cell (q := q) hR K
  obtain ⟨S, hS, J, hl, hr, hc⟩ := M.exists_originalPoisson_bipartite_gridCellCore hq
    (isCompact_legalWeightedPhysicalWindow q R K) (4 * R) (fun _ ↦ -2 * R) (fun _ ↦ 0) hcell t
  refine ⟨S, hS, J, hl, hr, ?_⟩
  filter_upwards [hc] with p hp
  have heq := legalWeightedGridRetainedPlan_restrict_same_cell
    (4 * R) (fun _ ↦ -2 * R) p.1 (fun _ ↦ 0) hcell
  simpa only [IsOriginalLegalWeightedWindowCore, heq] using hp

/-- Genuine original finite Poisson window cores recover BOTH actual port
budgets and the SAME candidate's original signed matrix value. Each joining
retains the complete original law and literal input arrays, with an actual σ
on those arrays. No reserve completion or hcore inequality is assumed. -/
theorem LegalWeightedStationaryPoissonMatching.exists_recovering_originalPoisson_windowCores
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 0 < q)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (R K : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hlarge : Tendsto R atTop atTop) (hK : Tendsto K atTop atTop) :
    ∃ S : ℕ → ℝ, ∃ J : ℕ → ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (∀ n, 0 < S n) ∧
      (∀ n, (J n : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∀ n, (J n : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.snd = legalInputPoissonWindowLaw q (haarRootCube (Fin q) (S n)) α β) ∧
      (∀ n, ∀ᵐ p ∂(J n : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        IsOriginalLegalWeightedWindowCore q kin g (R n) (K n) t p) ∧
      Tendsto (fun n ↦ (ENNReal.ofReal ((2 * R n) ^ q))⁻¹ *
        ∫⁻ p, (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q))
          (legalWeightedPhysicalWindow q (R n) (K n) ×ˢ
            (legalWeightedPhysicalWindow q (R n) (K n))ᶜ)
          ∂(J n : Measure (LegalMarkedOptimalInputScene q ×
            (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))))
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ (ENNReal.ofReal ((2 * R n) ^ q))⁻¹ *
        ∫⁻ p, (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q))
          ((legalWeightedPhysicalWindow q (R n) (K n))ᶜ ×ˢ
            legalWeightedPhysicalWindow q (R n) (K n))
          ∂(J n : Measure (LegalMarkedOptimalInputScene q ×
            (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))))
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ (ENNReal.ofReal ((2 * R n) ^ q))⁻¹ *
        ∫⁻ p, (p.1.1.1 : Measure (LegalMarkedPhysicalEdge q))
          (legalWeightedPhysicalWindow q (R n) (K n) ×ˢ
            legalWeightedPhysicalWindow q (R n) (K n))
          ∂(J n : Measure (LegalMarkedOptimalInputScene q ×
            (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))))
        atTop (𝓝 1) ∧
      Tendsto (fun n ↦ ((2 * R n) ^ q)⁻¹ *
        ∫ p, ∫ e in legalWeightedPhysicalWindow q (R n) (K n) ×ˢ
            legalWeightedPhysicalWindow q (R n) (K n),
          kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
            ∂(p.1.1.1 : Measure (LegalMarkedPhysicalEdge q))
          ∂(J n : Measure (LegalMarkedOptimalInputScene q ×
            (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))))
        atTop (𝓝 (M.value t)) := by
  choose S hS J hl hr hc using (fun n ↦ M.exists_originalPoisson_windowCore hq (hR n) (K n) t)
  refine ⟨S, J, hS, hl, hr, hc, ?_, ?_, ?_, ?_⟩
  · apply (M.tendsto_both_window_ports_zero R K hR hlarge hK).1.congr'
    filter_upwards [] with n
    congr 1
    have hU := (isCompact_legalWeightedPhysicalWindow q (R n) (K n)).measurableSet
    exact legalWeightedOriginalMeanPlan_apply_eq_joining M
      (J n : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))) (hl n) (hU.prod hU.compl)
  · apply (M.tendsto_both_window_ports_zero R K hR hlarge hK).2.congr'
    filter_upwards [] with n
    congr 1
    have hU := (isCompact_legalWeightedPhysicalWindow q (R n) (K n)).measurableSet
    exact legalWeightedOriginalMeanPlan_apply_eq_joining M
      (J n : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))) (hl n) (hU.compl.prod hU)
  · apply (M.tendsto_windowCoreDensity_one R K hR hlarge hK).congr'
    filter_upwards [] with n
    change (ENNReal.ofReal ((2 * R n) ^ q))⁻¹ * legalWeightedOriginalMeanPlan M _ = _
    congr 1
    have hU := (isCompact_legalWeightedPhysicalWindow q (R n) (K n)).measurableSet
    exact legalWeightedOriginalMeanPlan_apply_eq_joining M
      (J n : Measure (LegalMarkedOptimalInputScene q ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))) (hl n) (hU.prod hU)
  · apply (M.tendsto_windowCoreCost_value hk hg t R K hR hlarge hK).congr'
    filter_upwards [] with n
    have hscene := M.windowCoreCost_eq_actual_scene (hR n) (K n) t
    rw [hscene.2]
    congr 1
    have hm : AEStronglyMeasurable
        (fun s : LegalMarkedOptimalInputScene q ↦
          ∫ e in legalWeightedPhysicalWindow q (R n) (K n) ×ˢ
              legalWeightedPhysicalWindow q (R n) (K n),
            kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2
              ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)))
        ((J n : Measure (LegalMarkedOptimalInputScene q ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
            Prod.fst) := by
      rw [hl n]
      exact hscene.1.aestronglyMeasurable
    have he := integral_map measurable_fst.aemeasurable hm
    rw [hl n] at he
    exact he

end OTSelector.Reconstruction
