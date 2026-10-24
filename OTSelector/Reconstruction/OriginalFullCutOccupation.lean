import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic
import OTSelector.Reconstruction.OriginalCompletePathSlabDivergence

/-!
# Full original active-cut occupation

Strictly active original edges use the same complete paths as the finite cut
measure. Source and target anchors are unrestricted. The true Campbell law
identifies their spatial occupation from the original two clock marginals.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Strict active cuts retain the original half-open prefix convention, even
when either original clock marginal has atoms at the cut. -/
theorem measure_strict_forward_clock_crossing_add_target_prefix
    (q : ℕ) (η : Measure (PhysicalPairPalmMark (Fin q))) (α β : Measure ℝ)
    (hsource : η.map (fun m ↦ m.1.1) = α) (htarget : η.map (fun m ↦ m.1.2) = β)
    (hforward : ∀ᵐ m ∂η, m.1.1 < m.1.2) (t : ℝ) :
    η {m | m.1.1 < t ∧ t < m.1.2} + β (Iic t) = α (Iio t) := by
  have hs : η {m | m.1.1 < t} = α (Iio t) := by
    rw [← hsource,Measure.map_apply measurable_fst.fst measurableSet_Iio]
    rfl
  have ht : η {m | m.1.2 ≤ t} = β (Iic t) := by
    rw [← htarget,Measure.map_apply measurable_fst.snd measurableSet_Iic]
    rfl
  rw [← hs,← ht,← measure_union]
  · apply measure_congr
    filter_upwards [hforward] with m hm
    apply propext
    change ((m.1.1 < t ∧ t < m.1.2) ∨ m.1.2 ≤ t) ↔ m.1.1 < t
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hm.trans_le h
    · intro h
      by_cases ht : m.1.2 ≤ t
      · exact Or.inr ht
      · exact Or.inl ⟨h,lt_of_not_ge ht⟩
  · exact disjoint_left.mpr (fun _ hm hn ↦ (not_lt_of_ge hn) hm.2)
  · exact measurableSet_le measurable_fst.snd measurable_const

/-- The SAME actual original probability Palm identifies the complete cut
intensity from its original two prefix masses. -/
theorem LegalWeightedStationaryPoissonMatching.strict_cut_palm_mass
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) :
    (legalMarkedJointPalm q Q.law {m | m.1.1 < t ∧ t < m.1.2}).toReal =
      α.real (Iio t) - β.real (Iic t) := by
  let _inst : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  have h := measure_strict_forward_clock_crossing_add_target_prefix q
    (legalMarkedJointPalm q Q.law) α β Q.source_clock Q.target_clock Q.ae_palm_forward t
  have hβ : β (Iic t) ≠ ⊤ := by
    rw [← Q.target_clock,Measure.map_apply measurable_fst.snd measurableSet_Iic]
    exact measure_ne_top _ _
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top _ _) hβ] at hreal
  exact eq_sub_iff_add_eq.mpr hreal

/-- Full-cut spatial intensity is nonnegative and at most one, with no
selected-cloud Poisson assertion or atomlessness requirement. -/
theorem LegalWeightedStationaryPoissonMatching.strict_cut_intensity_bounds
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) :
    0 ≤ α.real (Iio t) - β.real (Iic t) ∧ α.real (Iio t) - β.real (Iic t) ≤ 1 := by
  let _inst : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  rw [← Q.strict_cut_palm_mass t]
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

/-- A fixed mark-dependent path position has the true nonnegative Campbell
factorization under the unchanged original matching law. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_pathWindow_nonnegative
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ} (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (hd : Measurable d)
    {η : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) → ℝ≥0∞}
    (hη : Measurable η) (hf : Measurable f) :
    (∫⁻ scene, ∫⁻ p, η (p.1+d p.2)*f p.2 ∂physicalScenePairKernel scene.1
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
      (∫⁻ x, η x ∂(volume : Measure (Fin q → ℝ))) *
        ∫⁻ m, f m ∂legalMarkedJointPalm q Q.law := by
  let _inst : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  let P := legalMarkedInputPairLaw q Q.law
  let G : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞ :=
    fun p ↦ η (p.1+d p.2)*f p.2
  have hG : Measurable G :=
    (hη.comp (measurable_fst.add (hd.comp measurable_snd))).mul (hf.comp measurable_snd)
  have hi := Measure.lintegral_bind (m := (P : Measure _))
    (Kernel.measurable (physicalScenePairKernel : Kernel
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))
      ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)))).aemeasurable hG.aemeasurable
  have hm := lintegral_map (hG.lintegral_kernel (κ := physicalScenePairKernel))
    (measurable_fst : Measurable (Prod.fst : LegalMarkedOptimalInputScene q → _))
    (μ := (Q.law : Measure (LegalMarkedOptimalInputScene q)))
  change (∫⁻ p, G p ∂physicalScenePairCampbell (P : Measure _)) = _ at hi
  rw [Q.campbell_eq_volume_prod_palm] at hi
  exact hm.symm.trans (hi.symm.trans
    (lintegral_markDependentAnchorTranslation _ d hd hη hf))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The full active-cut measure extends the existing finite-edge active cut
by the same restriction and actual path pushforward on the original first plan. -/
def originalFullCompletePathActiveCut (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (t : ℝ) : Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  ((scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).restrict
    {e | e.1.2 < t ∧ t < e.2.2}).map
      (fun e ↦ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t)


/-- The full-plan restriction agrees exactly with the old finite active cut
whenever the actual first plan is a finite original edge array. -/
theorem originalFullCompletePathActiveCut_eq_finite
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    {I : Type*} [Fintype I] (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (hplan : (scene.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) =
      ∑ i, Measure.dirac (edges i)) (t : ℝ) :
    originalFullCompletePathActiveCut S w scene t = originalCompletePathActiveCut S w edges t := by
  classical
  have hpath : Measurable (fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) :=
    (measurable_originalSeedCompletePath S hF hw).comp
      (measurable_physicalPairAnchor.prodMk measurable_const)
  have hactive : MeasurableSet
      {e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) | e.1.2<t ∧ t<e.2.2} :=
    (measurableSet_lt measurable_fst.snd measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd.snd)
  ext W hW
  have hSet : MeasurableSet
      ((fun e ↦ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) ⁻¹' W ∩
        {e | e.1.2<t ∧ t<e.2.2}) := (hW.preimage hpath).inter hactive
  rw [originalFullCompletePathActiveCut,Measure.map_apply hpath hW,
    Measure.restrict_apply (hW.preimage hpath),hplan]
  simp only [Measure.finsetSum_apply]
  unfold originalCompletePathActiveCut
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (edges i).1.2 < t ∧ t < (edges i).2.2
  · simp only [hi,and_true,ite_true]
    rw [Measure.dirac_apply' _ hSet,Measure.dirac_apply' _ hW]
    by_cases hx : originalSeedCompletePath S w (edges i).1.1
        (physicalPairAnchor (edges i)).2 t ∈ W
    · have hin : edges i ∈
          ((fun e ↦ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) ⁻¹' W ∩
            {e | e.1.2<t ∧ t<e.2.2}) := ⟨hx,hi⟩
      rw [indicator_of_mem hin,indicator_of_mem hx]
      rfl
    · have hn : edges i ∉
          ((fun e ↦ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) ⁻¹' W ∩
            {e | e.1.2<t ∧ t<e.2.2}) := fun h ↦ hx h.1
      rw [indicator_of_notMem hn,indicator_of_notMem hx]
  · simp only [hi,ite_false,Measure.coe_zero,Pi.zero_apply]
    rw [Measure.dirac_apply' _ hSet]
    exact indicator_of_notMem (fun h ↦ hi h.2) _

/-- Nonnegative observations of the full cut are the same actual original
pair-kernel readout at the complete path position and strict active clocks. -/
theorem lintegral_originalFullCompletePathActiveCut_eq_pairKernel
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (t : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hη : Measurable η)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    (∫⁻ x, η x ∂originalFullCompletePathActiveCut S w scene t) =
      ∫⁻ p, η (p.1+originalSeedPathOffset S w t p.2)*
        ({m | m.1.1<t ∧ t<m.1.2}.indicator (fun _ ↦ (1:ℝ≥0∞)) p.2)
        ∂physicalScenePairKernel scene.1 := by
  let A : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) :=
    {e | e.1.2<t ∧ t<e.2.2}
  have hA : MeasurableSet A := (measurableSet_lt measurable_fst.snd measurable_const).inter
    (measurableSet_lt measurable_const measurable_snd.snd)
  have hpath : Measurable (fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) :=
    (measurable_originalSeedCompletePath S hF hw).comp
      (measurable_physicalPairAnchor.prodMk measurable_const)
  have hm : MeasurableSet {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) |
      m.1.1<t ∧ t<m.1.2} := (measurableSet_lt measurable_fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst.snd)
  have hG : Measurable (fun p : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      η (p.1+originalSeedPathOffset S w t p.2)*
        ({m | m.1.1<t ∧ t<m.1.2}.indicator (fun _ ↦ (1:ℝ≥0∞)) p.2)) :=
    (hη.comp (measurable_fst.add
      ((measurable_originalSeedPathOffset S hF hw t).comp measurable_snd))).mul
      ((measurable_const.indicator hm).comp measurable_snd)
  rw [originalFullCompletePathActiveCut,lintegral_map hη hpath,
    ← lintegral_indicator hA,physicalScenePairKernel_apply,
    lintegral_map hG measurable_physicalPairAnchor]
  apply lintegral_congr
  intro e
  by_cases he : e ∈ A
  · have hm : (physicalPairAnchor e).2 ∈ {m | m.1.1<t ∧ t<m.1.2} := he
    rw [indicator_of_mem he,indicator_of_mem hm,mul_one,
      originalSeedCompletePath_eq_anchor_add_offset]
    rfl
  · have hm : (physicalPairAnchor e).2 ∉ {m | m.1.1<t ∧ t<m.1.2} := he
    rw [indicator_of_notMem he,indicator_of_notMem hm,mul_zero]

/-- The full cut occupation is a measurable actual-scene observable. -/
theorem measurable_lintegral_originalFullCompletePathActiveCut
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) (t : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hη : Measurable η) :
    Measurable (fun scene ↦ ∫⁻ x, η x ∂originalFullCompletePathActiveCut S w scene t) := by
  have hm : MeasurableSet {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) |
      m.1.1<t ∧ t<m.1.2} := (measurableSet_lt measurable_fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst.snd)
  have hG : Measurable (fun p : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      η (p.1+originalSeedPathOffset S w t p.2)*
        ({m | m.1.1<t ∧ t<m.1.2}.indicator (fun _ ↦ (1:ℝ≥0∞)) p.2)) :=
    (hη.comp (measurable_fst.add
      ((measurable_originalSeedPathOffset S hF hw t).comp measurable_snd))).mul
      ((measurable_const.indicator hm).comp measurable_snd)
  have heq := funext (lintegral_originalFullCompletePathActiveCut_eq_pairKernel S hF hw t hη)
  rw [heq]
  exact hG.lintegral_kernel.comp measurable_fst

/-- Full original cut intensity is its literal Haar spatial mass times the
original prefix difference; endpoints are unrestricted in space. -/
theorem lintegral_originalFullCompletePathActiveCut
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (t : ℝ) {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hη : Measurable η) :
    (∫⁻ scene, ∫⁻ x, η x ∂originalFullCompletePathActiveCut S w scene t
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
        ENNReal.ofReal (α.real (Iio t)-β.real (Iic t)) := by
  let _inst : IsProbabilityMeasure (legalMarkedJointPalm _ Q.law) := Q.palm_probability
  have hm : MeasurableSet {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) |
      m.1.1<t ∧ t<m.1.2} := (measurableSet_lt measurable_fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst.snd)
  simp_rw [lintegral_originalFullCompletePathActiveCut_eq_pairKernel S hF hw t hη]
  rw [Q.lintegral_pathWindow_nonnegative _ (measurable_originalSeedPathOffset S hF hw t)
    hη (measurable_const.indicator hm),lintegral_indicator hm]
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
  rw [← Q.strict_cut_palm_mass t,ENNReal.ofReal_toReal (measure_ne_top _ _)]


/-- Finite original spatial mass gives finite full cut occupation in almost
every original scene at each fixed physical cut. -/
theorem ae_lintegral_originalFullCompletePathActiveCut_lt_top
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (t : ℝ) {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞} (hη : Measurable η)
    (hfinite : (∫⁻ x, η x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) ≠ ⊤) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (∫⁻ x, η x ∂originalFullCompletePathActiveCut S w scene t) < ⊤ := by
  apply ae_lt_top (measurable_lintegral_originalFullCompletePathActiveCut S hF hw t hη)
  rw [lintegral_originalFullCompletePathActiveCut S hF hw Q t hη]
  exact ENNReal.mul_ne_top hfinite ENNReal.ofReal_ne_top

/-- Compact spatial windows have finite full original cut counts almost surely. -/
theorem ae_originalFullCompletePathActiveCut_apply_lt_top
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (t : ℝ) {K : Set (Fin (finrank ℝ S.covector.ker) → ℝ)} (hK : MeasurableSet K)
    (hfinite : volume K ≠ ⊤) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      originalFullCompletePathActiveCut S w scene t K < ⊤ := by
  have hf : (∫⁻ x, K.indicator (fun _ ↦ (1:ℝ≥0∞)) x ∂volume) ≠ ⊤ := by
    simpa only [lintegral_indicator hK,lintegral_const,Measure.restrict_apply_univ,one_mul]
      using hfinite
  simpa only [lintegral_indicator hK,lintegral_const,Measure.restrict_apply_univ,one_mul]
    using ae_lintegral_originalFullCompletePathActiveCut_lt_top S hF hw Q t
      (measurable_const.indicator hK) hf

/-- At each deterministic cut the complete original cut process is locally
finite on one event of full original-scene probability. -/
theorem ae_originalFullCompletePathActiveCut_locallyFinite
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g) (t : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsLocallyFiniteMeasure (originalFullCompletePathActiveCut S w scene t) := by
  have hballs := ae_all_iff.mpr (fun n : ℕ ↦
    ae_originalFullCompletePathActiveCut_apply_lt_top S hF hw Q t
      (K := Metric.closedBall 0 (n:ℝ)) measurableSet_closedBall
      (isCompact_closedBall _ _).measure_ne_top)
  filter_upwards [hballs] with scene hs
  constructor
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt ‖x‖
  refine ⟨Metric.closedBall 0 (n:ℝ),?_,hs n⟩
  apply Metric.closedBall_mem_nhds_of_mem
  simpa only [Metric.mem_ball,dist_zero_right] using hn

/-- A countable deterministic cut family shares one event of local finiteness;
no intersection over an uncountable test or cut family is taken. -/
theorem ae_originalFullCompletePathActiveCut_countable_locallyFinite
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    {J : Type*} [Countable J] (t : J → ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ j, IsLocallyFiniteMeasure (originalFullCompletePathActiveCut S w scene (t j)) :=
  ae_all_iff.mpr (fun j ↦ ae_originalFullCompletePathActiveCut_locallyFinite S hF hw Q (t j))


/-- The existing real path-window readout has the exact full-cut mean, so
screening can consume the same observable without introducing a new current. -/
theorem original_full_cut_readout_integrable_and_integral
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (t : ℝ) {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Integrable η (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) :
    let readout := legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
      (originalSeedPathOffset S w t) η
      ({m | m.1.1<t ∧ t<m.1.2}.indicator (fun _ ↦ (1:ℝ)))
    Integrable readout (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ scene, readout scene
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
        (∫ x, η x ∂volume)*(α.real (Iio t)-β.real (Iic t)) := by
  let _inst : IsProbabilityMeasure (legalMarkedJointPalm _ Q.law) := Q.palm_probability
  have hm : MeasurableSet {m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) |
      m.1.1<t ∧ t<m.1.2} := (measurableSet_lt measurable_fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_fst.snd)
  have hi : Integrable ({m | m.1.1<t ∧ t<m.1.2}.indicator (fun _ ↦ (1:ℝ)))
      (legalMarkedJointPalm _ Q.law) := (integrable_const 1).indicator hm
  obtain ⟨hread,heq⟩ := Q.pathWindowReadout_integrable_and_integral
    (originalSeedPathOffset S w t) (measurable_originalSeedPathOffset S hF hw t) hη hi
  refine ⟨hread,?_⟩
  rw [integral_indicator hm,setIntegral_const] at heq
  simpa only [smul_eq_mul,mul_one,measureReal_def,Q.strict_cut_palm_mass t] using heq

/-- Any measurable retained-edge family gives a positive residual part of the
FULL actual cut. This is an exact measure decomposition before any cube cutoff. -/
theorem originalFullCompletePathActiveCut_eq_kept_add_omitted
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) (t : ℝ)
    (H : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) (hH : MeasurableSet H) :
    let active := {e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) |
      e.1.2<t ∧ t<e.2.2}
    let path := fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t
    originalFullCompletePathActiveCut S w scene t =
      ((scene.1.1 : Measure _).restrict (active ∩ H)).map path +
        ((scene.1.1 : Measure _).restrict (active \ H)).map path := by
  dsimp only [originalFullCompletePathActiveCut]
  have hpath : Measurable (fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) :=
    (measurable_originalSeedCompletePath S hF hw).comp
      (measurable_physicalPairAnchor.prodMk measurable_const)
  rw [← Measure.map_add _ _ hpath,Measure.restrict_inter_add_sdiff _ hH]


/-- The actual full-cut count in every measurable spatial window has exactly
the original prefix-difference Haar intensity. -/
theorem lintegral_originalFullCompletePathActiveCut_apply
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β kin g)
    (t : ℝ) {W : Set (Fin (finrank ℝ S.covector.ker) → ℝ)} (hW : MeasurableSet W) :
    (∫⁻ scene, originalFullCompletePathActiveCut S w scene t W
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) =
      volume W * ENNReal.ofReal (α.real (Iio t)-β.real (Iic t)) := by
  simpa only [lintegral_indicator hW,lintegral_const,Measure.restrict_apply_univ,one_mul]
    using lintegral_originalFullCompletePathActiveCut S hF hw Q t
      (η := W.indicator (fun _ ↦ (1:ℝ≥0∞))) (measurable_const.indicator hW)

/-- Every positive omitted-edge cut measure is dominated by the same full
original cut, so the already proved local finiteness applies to that residual. -/
theorem originalFullCompletePathActiveCut_omitted_le
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w ∈ S.labels)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) (t : ℝ)
    (H : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) :
    ((scene.1.1 : Measure _).restrict
      ({e | e.1.2<t ∧ t<e.2.2} \ H)).map
      (fun e ↦ originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) ≤
        originalFullCompletePathActiveCut S w scene t := by
  have hpath : Measurable (fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 t) :=
    (measurable_originalSeedCompletePath S hF hw).comp
      (measurable_physicalPairAnchor.prodMk measurable_const)
  exact Measure.map_mono (Measure.restrict_mono_set _ sdiff_subset) hpath

end OTSelector.Reconstruction
