import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanLaw
import OTSelector.Probability.ProbabilityMeasureWeakSecondCountable
import OTSelector.Probability.DirichletWeightedLLN

/-!
# Original weighted target marginals in global plan-law weak limits

The original iid targets and Dirichlet weights determine each realized target
marginal. Their signed centered second moment vanishes. Bounded continuous
target tests pass this fact to a weak law limit, and a fixed countable family
of compact tests identifies the full target marginal almost surely.
-/

open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ProperSpace M] [PolishSpace M]

local instance : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
  probabilityMeasure_weakSecondCountable
local instance : BorelSpace (ProbabilityMeasure (M × M)) :=
  probabilityMeasure_weakBorelSpace

/-- The original target-first iid and Dirichlet experiment. -/
def originalTargetEnvironmentLaw (n : ℕ) (ν : Measure M) :
    Measure ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) :=
  (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)

instance (n : ℕ) (ν : Measure M) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (originalTargetEnvironmentLaw n ν) := by
  unfold originalTargetEnvironmentLaw
  infer_instance

/-- A bounded continuous target test read directly on the original plan. -/
def originalPlanTargetTest (f : M →ᵇ ℝ) : ProbabilityMeasure (M × M) → ℝ :=
  fun π ↦ ∫ p : M × M, f p.2 ∂(π : Measure (M × M))

theorem continuous_originalPlanTargetTest (f : M →ᵇ ℝ) :
    Continuous (originalPlanTargetTest f) :=
  ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (f.compContinuous ⟨Prod.snd, continuous_snd⟩)

theorem abs_originalPlanTargetTest_le (f : M →ᵇ ℝ) (π : ProbabilityMeasure (M × M)) :
    |originalPlanTargetTest f π| ≤ ‖f‖ := by
  calc
    |originalPlanTargetTest f π| ≤ ‖f.compContinuous ⟨Prod.snd, continuous_snd⟩‖ :=
      (f.compContinuous ⟨(Prod.snd : M × M → M), continuous_snd⟩).norm_integral_le_norm
        (μ := (π : Measure (M × M)))
    _ ≤ ‖f‖ := BoundedContinuousFunction.norm_compContinuous_le _ _

/-- Feasibility and simplex weights give the literal signed weighted target
readout, on the unchanged original experiment. -/
theorem ae_originalPlanTargetTest_eq_weighted
    (n : ℕ) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (alloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂originalTargetEnvironmentLaw n ν,
      IsSemidiscreteAllocation μ w.2 (alloc w)) (f : M →ᵇ ℝ) :
    (fun w ↦ originalPlanTargetTest f
      (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν alloc Prod.fst w))
      =ᵐ[originalTargetEnvironmentLaw n ν] originalDirichletWeightedTargetTest n f := by
  have hsimplex : ∀ᵐ w ∂originalTargetEnvironmentLaw n ν,
      w.2 ∈ stdSimplex ℝ (Fin (n + 1)) := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa only [originalTargetEnvironmentLaw, Measure.map_snd_prod, measure_univ, one_smul]
      using ae_mem_stdSimplex_dirichletOne n
  filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
      (originalTargetEnvironmentLaw n ν) μ ν alloc Prod.fst Prod.snd hfeas,
    physicalSceneGlobalAllocationFamily_ae_eq (originalTargetEnvironmentLaw n ν)
      μ alloc Prod.fst Prod.snd hfeas, hfeas, hsimplex] with w heq hraw hw hp
  unfold originalPlanTargetTest
  rw [heq, hraw, ← integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable]
  change (∫ y, f y ∂(physicalSceneAllocationPlan μ (alloc w) w.1).snd) = _
  rw [physicalSceneAllocationPlan_snd hw w.1,
    integral_map (measurable_of_finite w.1).aemeasurable f.continuous.aestronglyMeasurable]
  unfold semidiscreteLabelMeasure
  rw [integral_finsetSum_measure (fun i _ ↦
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp.1 _),
    smul_eq_mul, originalDirichletWeightedTargetTest]

/-- The squared target-test error is a genuine bounded continuous plan readout. -/
def originalPlanTargetSquareError (ν : Measure M) (f : M →ᵇ ℝ) :
    ProbabilityMeasure (M × M) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun π ↦ (originalPlanTargetTest f π - ∫ x, f x ∂ν) ^ 2)
    (((continuous_originalPlanTargetTest f).sub continuous_const).pow 2)
    ((‖f‖ + |∫ x, f x ∂ν|) ^ 2)
    (fun π ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs]
      apply pow_le_pow_left₀ (abs_nonneg _) _ 2
      calc
        |originalPlanTargetTest f π - ∫ x, f x ∂ν| ≤
            |originalPlanTargetTest f π| + |∫ x, f x ∂ν| := abs_sub _ _
        _ ≤ ‖f‖ + |∫ x, f x ∂ν| := add_le_add (abs_originalPlanTargetTest_le f π) le_rfl)

/-- Vanishing squared target error passes through an actual weak plan-law
limit, and forces the target readout to equal its population value almost surely. -/
theorem ae_originalPlanTargetTest_eq_of_weak_of_square_tendsto
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (P : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (π : S → ProbabilityMeasure (M × M)) (hπ : Continuous π)
    (ν : Measure M) (f : M →ᵇ ℝ)
    (hweak : Tendsto P atTop (𝓝 Q))
    (hzero : Tendsto (fun n ↦ ∫ s, originalPlanTargetSquareError ν f (π s)
      ∂(P n : Measure S)) atTop (𝓝 0)) :
    ∀ᵐ s ∂(Q : Measure S), originalPlanTargetTest f (π s) = ∫ x, f x ∂ν := by
  let G : S →ᵇ ℝ := (originalPlanTargetSquareError ν f).compContinuous ⟨π, hπ⟩
  have hlim := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) G
  have hz : (∫ s, G s ∂(Q : Measure S)) = 0 := tendsto_nhds_unique hlim hzero
  have hnonneg (s : S) : 0 ≤ G s := sq_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg
    (G.integrable (μ := (Q : Measure S)))).mp hz
  filter_upwards [hae] with s hs
  exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hs)

/-- A fixed countable family of actual compact tests promotes almost-sure
target readout equality to equality of the entire original target marginal. -/
theorem ae_snd_eq_of_originalPlanTargetTest_eq
    {S : Type*} [MeasurableSpace S] (R : Measure S)
    (π : S → ProbabilityMeasure (M × M)) (ν : Measure M) [IsProbabilityMeasure ν]
    (htest : ∀ f : M →ᵇ ℝ,
      ∀ᵐ s ∂R, originalPlanTargetTest f (π s) = ∫ x, f x ∂ν) :
    ∀ᵐ s ∂R, (π s : Measure (M × M)).snd = ν := by
  let K := CompactExhaustion.choice M
  have hcount : ∀ᵐ s ∂R, ∀ i : ℕ ⊕ (ℕ × ℕ),
      originalPlanTargetTest (LocalFiniteMeasure.separatingTest K i).toBoundedContinuousFunction
        (π s) = ∫ x, LocalFiniteMeasure.separatingTest K i x ∂ν := by
    exact ae_all_iff.mpr (fun i ↦ htest
      (LocalFiniteMeasure.separatingTest K i).toBoundedContinuousFunction)
  filter_upwards [hcount] with s hs
  let πt : LocalFiniteMeasure M := ⟨(π s : Measure (M × M)).snd, inferInstance⟩
  let νt : LocalFiniteMeasure M := ⟨ν, inferInstance⟩
  have hcode : LocalFiniteMeasure.separatingTestCode K πt =
      LocalFiniteMeasure.separatingTestCode K νt := by
    funext i
    change (∫ x, LocalFiniteMeasure.separatingTest K i x
      ∂Measure.map Prod.snd (π s : Measure (M × M))) = _
    rw [integral_map (f := fun x ↦ LocalFiniteMeasure.separatingTest K i x)
      measurable_snd.aemeasurable
      (LocalFiniteMeasure.separatingTest K i).continuous.aestronglyMeasurable]
    exact hs i
  exact congrArg Subtype.val (LocalFiniteMeasure.separatingTestCode_injective K hcode)

/-- Either member of the original paired plan, on the same experiment. -/
def originalPlanPairProjection (side : Bool)
    (p : ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)) :
    ProbabilityMeasure (M × M) := if side then p.1 else p.2

theorem continuous_originalPlanPairProjection (side : Bool) :
    Continuous (originalPlanPairProjection (M := M) side) := by
  cases side <;> first | exact continuous_snd | exact continuous_fst

/-- The expected squared target error of each actual original plan is exactly
the signed original Dirichlet variance, independently of the allocation rule. -/
theorem integral_originalAllocationPlanPairLaw_targetSquareError
    (n : ℕ) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am z.1 z.2 k))
    (hfp : ∀ᵐ w ∂originalTargetEnvironmentLaw n ν, IsSemidiscreteAllocation μ w.2 (ap w))
    (hfm : ∀ᵐ w ∂originalTargetEnvironmentLaw n ν, IsSemidiscreteAllocation μ w.2 (am w))
    (side : Bool) (f : M →ᵇ ℝ) :
    (∫ p, originalPlanTargetSquareError ν f (originalPlanPairProjection side p)
      ∂(physicalSceneOriginalAllocationPlanPairLaw (originalTargetEnvironmentLaw n ν)
        μ ν ap am hpm hmm Prod.fst (fun k ↦ (measurable_pi_apply k).comp measurable_fst) :
        Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) =
      (2 / ((n : ℝ) + 2)) * ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2) := by
  let pair : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
      ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M) := fun w ↦
    (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Prod.fst w,
      physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Prod.fst w)
  have hm : Measurable pair :=
    (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap hpm Prod.fst
      (fun k ↦ (measurable_pi_apply k).comp measurable_fst)).prodMk
    (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am hmm Prod.fst
      (fun k ↦ (measurable_pi_apply k).comp measurable_fst))
  let G := (originalPlanTargetSquareError ν f).compContinuous
    ⟨originalPlanPairProjection side, continuous_originalPlanPairProjection side⟩
  change (∫ p, G p ∂Measure.map pair (originalTargetEnvironmentLaw n ν)) = _
  rw [integral_map hm.aemeasurable G.continuous.aestronglyMeasurable]
  have heq : (fun w ↦ G (pair w)) =ᵐ[originalTargetEnvironmentLaw n ν]
      (fun w ↦ (originalDirichletWeightedTargetTest n f w - ∫ x, f x ∂ν) ^ 2) := by
    have hp := ae_originalPlanTargetTest_eq_weighted n μ ν ap hfp f
    have hm := ae_originalPlanTargetTest_eq_weighted n μ ν am hfm f
    filter_upwards [hp, hm] with w hpw hmw
    cases side
    · change (originalPlanTargetTest f
        (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Prod.fst w) - _) ^ 2 = _
      rw [hmw]
    · change (originalPlanTargetTest f
        (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Prod.fst w) - _) ^ 2 = _
      rw [hpw]
  rw [integral_congr_ae heq]
  exact (originalDirichletWeightedTargetTest_centered_sq n ν f.continuous.measurable
    (norm_nonneg f) (fun x ↦ f.norm_coe_le_norm x)).2

/-- Every weak limit of the actual original paired plan laws has the original
target marginal in both coordinates almost surely. The sample sizes may be
any sequence tending to infinity, including an extracted sample subsequence. -/
theorem ae_snd_eq_of_originalAllocationPlanPairLaw_tendsto
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ∀ k, ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) →
      M → Fin (m k + 1) → ℝ)
    (hpm : ∀ k i, Measurable (fun z :
      ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) × M ↦ ap k z.1 z.2 i))
    (hmm : ∀ k i, Measurable (fun z :
      ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) × M ↦ am k z.1 z.2 i))
    (hfp : ∀ k, ∀ᵐ w ∂originalTargetEnvironmentLaw (m k) ν,
      IsSemidiscreteAllocation μ w.2 (ap k w))
    (hfm : ∀ k, ∀ᵐ w ∂originalTargetEnvironmentLaw (m k) ν,
      IsSemidiscreteAllocation μ w.2 (am k w))
    (Q : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (hweak : Tendsto (fun k ↦ physicalSceneOriginalAllocationPlanPairLaw
      (originalTargetEnvironmentLaw (m k) ν) μ ν (ap k) (am k) (hpm k) (hmm k)
      Prod.fst (fun i ↦ (measurable_pi_apply i).comp measurable_fst)) atTop (𝓝 Q)) :
    ∀ᵐ p ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (p.1 : Measure (M × M)).snd = ν ∧ (p.2 : Measure (M × M)).snd = ν := by
  have hside (side : Bool) :
      ∀ᵐ p ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
        (originalPlanPairProjection side p : Measure (M × M)).snd = ν := by
    apply ae_snd_eq_of_originalPlanTargetTest_eq _ _ ν
    intro f
    apply ae_originalPlanTargetTest_eq_of_weak_of_square_tendsto _ Q
      (originalPlanPairProjection side) (continuous_originalPlanPairProjection side) ν f hweak
    have hden : Tendsto (fun k ↦ ((m k : ℕ) : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop.comp hm)
    have hrate : Tendsto (fun k ↦ (2 / ((m k : ℝ) + 2)) *
        ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, Function.comp_def, mul_zero, zero_mul] using
        ((tendsto_const_nhds (x := (2 : ℝ))).mul
          (tendsto_inv_atTop_zero.comp hden)).mul_const
            ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)
    convert hrate using 1
    funext k
    exact integral_originalAllocationPlanPairLaw_targetSquareError (m k) μ ν
      (ap k) (am k) (hpm k) (hmm k) (hfp k) (hfm k) side f
  filter_upwards [hside true, hside false] with p hp hm
  exact ⟨hp, hm⟩

/-- Exact target marginals remain almost sure under a further weak limit of
the paired plan laws, so the original target identification survives the
separate outer stage. -/
theorem ae_snd_pair_eq_of_tendsto_of_ae
    (P : ℕ → ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (Q : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (ν : Measure M) [IsProbabilityMeasure ν]
    (hweak : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n, ∀ᵐ p ∂(P n :
      Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (p.1 : Measure (M × M)).snd = ν ∧ (p.2 : Measure (M × M)).snd = ν) :
    ∀ᵐ p ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (p.1 : Measure (M × M)).snd = ν ∧ (p.2 : Measure (M × M)).snd = ν := by
  have hside (side : Bool) :
      ∀ᵐ p ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
        (originalPlanPairProjection side p : Measure (M × M)).snd = ν := by
    apply ae_snd_eq_of_originalPlanTargetTest_eq _ _ ν
    intro f
    apply ae_originalPlanTargetTest_eq_of_weak_of_square_tendsto P Q
      (originalPlanPairProjection side) (continuous_originalPlanPairProjection side) ν f hweak
    have hzero (n : ℕ) :
        (∫ p, originalPlanTargetSquareError ν f (originalPlanPairProjection side p)
          ∂(P n : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hP n] with p hp
      have hs : (originalPlanPairProjection side p : Measure (M × M)).snd = ν := by
        cases side
        · exact hp.2
        · exact hp.1
      have hi : originalPlanTargetTest f (originalPlanPairProjection side p) = ∫ x, f x ∂ν := by
        rw [← hs]
        exact (integral_map measurable_snd.aemeasurable f.continuous.aestronglyMeasurable).symm
      change (originalPlanTargetTest f (originalPlanPairProjection side p) - ∫ x, f x ∂ν) ^ 2 = 0
      rw [hi, sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    simpa only [hzero] using (tendsto_const_nhds (x := (0 : ℝ)))
  filter_upwards [hside true, hside false] with p hp hm
  exact ⟨hp, hm⟩

end OTSelector.Reconstruction
