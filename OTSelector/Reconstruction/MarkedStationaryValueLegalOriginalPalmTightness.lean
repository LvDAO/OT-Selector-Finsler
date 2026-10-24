import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalUniformFirstMoment
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Actual original Palm subsequences for the weighted stationary direct method

Bounded original kinetic means give uniform first moments of the complete true
Palm marks. Prokhorov therefore supplies actual probability-Palm subsequences.
Both fixed original clock laws and the closed forward order survive weak
convergence; original separated supports recover strict positive clock gap and
the genuine open coefficient domain of the same limiting Palm.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

/-- The unchanged complete original Palm, packaged with its produced actual
probability mass. No clock or displacement coordinate is discarded. -/
def LegalWeightedStationaryPoissonMatching.truePalmProbability
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ProbabilityMeasure (PhysicalPairPalmMark (Fin q)) :=
  ⟨legalMarkedJointPalm q Q.law, Q.palm_probability⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Any original family with a bounded actual weighted kinetic expectation
has tight complete true Palm laws; no unweighted second moment is assumed. -/
theorem isTight_truePalm_of_original_kinetic_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {J : Type*} {g : ℝ → ℝ → ℝ}
    (Q : J → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (B : ℝ) (hB : ∀ j, (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) (Q j).law) ≤ B) :
    IsTightMeasureSet (range (fun j ↦
      (Q j).truePalmProbability.toMeasure)) := by
  obtain ⟨C, _hC, hmean⟩ := D.exists_uniform_wholePalm_firstMoment_bound hF hw hbounds
  apply isTightMeasureSet_of_uniform_integral_norm_bound
    (fun j ↦ (Q j).truePalmProbability.toMeasure)
    (fun j ↦ (hmean (Q j)).1) (B + C)
  intro j
  exact (hmean (Q j)).2.trans (add_le_add (hB j) le_rfl)

/-- Both original scalar laws survive convergence of their complete true
Palm probabilities. This is equality of the actual pushforward measures. -/
theorem clock_marginals_of_truePalm_weak
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : ℕ → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (η : ProbabilityMeasure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (hweak : Tendsto (fun n ↦ (Q n).truePalmProbability) atTop (𝓝 η)) :
    (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map (fun m ↦ m.1.1) = μ ∧
      (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map (fun m ↦ m.1.2) = ν := by
  let μP : ProbabilityMeasure ℝ := ⟨μ, D.support.source.probability⟩
  let νP : ProbabilityMeasure ℝ := ⟨ν, D.support.target.probability⟩
  have hs (n : ℕ) : (Q n).truePalmProbability.map
      (continuous_fst.fst : Continuous (fun m : PhysicalPairPalmMark
        (Fin (finrank ℝ S.covector.ker)) ↦ m.1.1)).measurable.aemeasurable = μP := by
    apply ProbabilityMeasure.toMeasure_injective
    exact (Q n).source_clock
  have ht (n : ℕ) : (Q n).truePalmProbability.map
      (continuous_fst.snd : Continuous (fun m : PhysicalPairPalmMark
        (Fin (finrank ℝ S.covector.ker)) ↦ m.1.2)).measurable.aemeasurable = νP := by
    apply ProbabilityMeasure.toMeasure_injective
    exact (Q n).target_clock
  have hsweak := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n ↦ (Q n).truePalmProbability) η hweak (continuous_fst.fst)
  have htweak := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n ↦ (Q n).truePalmProbability) η hweak (continuous_fst.snd)
  simp only [hs] at hsweak
  simp only [ht] at htweak
  have hseq := tendsto_nhds_unique hsweak (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ μP) atTop (𝓝 μP))
  have hteq := tendsto_nhds_unique htweak (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ νP) atTop (𝓝 νP))
  exact ⟨congrArg ProbabilityMeasure.toMeasure hseq, congrArg ProbabilityMeasure.toMeasure hteq⟩

/-- The actual weak probability Palm stays forward. The closed non-strict
order is used here; strictness is recovered below from original supports. -/
theorem ae_forward_order_of_truePalm_weak
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : ℕ → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (η : ProbabilityMeasure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (hweak : Tendsto (fun n ↦ (Q n).truePalmProbability) atTop (𝓝 η)) :
    ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))), m.1.1 ≤ m.1.2 := by
  let U : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) := {m | m.1.2 < m.1.1}
  have hU : IsOpen U := isOpen_lt continuous_fst.snd continuous_fst.fst
  have hn (n : ℕ) : ((Q n).truePalmProbability : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) U = 0 := by
    apply measure_mono_null (show U ⊆ {m | ¬ m.1.1 < m.1.2} from fun m hm ↦ not_lt_of_gt hm)
    exact ae_iff.mp (Q n).ae_palm_forward
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU
  simp only [hn, liminf_const] at hport
  have hzero : (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) U = 0 := le_antisymm hport bot_le
  have hae : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))), ¬ m.1.2 < m.1.1 := by
    apply ae_iff.mpr
    simpa only [not_not] using hzero
  exact hae.mono (fun _ hm ↦ le_of_not_gt hm)

/-- Both original laws, original open clock domain and original positive gap
are produced on the limiting true Palm from actual bounded-energy laws. -/
theorem exists_original_weighted_truePalm_subsequence
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (_hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : ℕ → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (B : ℝ) (hB : ∀ n, (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) (Q n).law) ≤ B) :
    ∃ η : ProbabilityMeasure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ (Q (φ n)).truePalmProbability) atTop (𝓝 η) ∧
        (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map (fun m ↦ m.1.1) = μ ∧
        (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map (fun m ↦ m.1.2) = ν ∧
        ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
          m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support ∧
          m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support ∧
          gap ≤ m.1.2 - m.1.1 := by
  obtain ⟨η, φ, hφ, hweak⟩ := exists_tendsto_subseq_probabilityMeasure_of_isTight
    (fun n ↦ (Q n).truePalmProbability) (D.isTight_truePalm_of_original_kinetic_bound hF hw hbounds Q B hB)
  have hweak' : Tendsto (fun n ↦ (Q (φ n)).truePalmProbability) atTop (𝓝 η) := hweak
  obtain ⟨hs, ht⟩ := D.clock_marginals_of_truePalm_weak (Q ∘ φ) η hweak'
  refine ⟨η, φ, hφ, hweak', hs, ht, ?_⟩
  have ha : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
      m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map (fun m ↦ m.1.1),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support := by
      rw [hs]
      exact D.support.source.ae_open.and μ.support_mem_ae
    exact ae_of_ae_map measurable_fst.fst.aemeasurable h
  have hb : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
      m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    have h : ∀ᵐ b ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map (fun m ↦ m.1.2),
        b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support := by
      rw [ht]
      exact D.support.target.ae_open.and ν.support_mem_ae
    exact ae_of_ae_map measurable_fst.snd.aemeasurable h
  filter_upwards [ha, hb, D.ae_forward_order_of_truePalm_weak (Q ∘ φ) η hweak'] with m ha hb hf
  refine ⟨ha.1, ha.2, hb.1, hb.2, ?_⟩
  have hsep := hbounds.separated m.1.1 ha.2 m.1.2 hb.2
  have hsep' : gap ≤ |m.1.2 - m.1.1| := by
    simpa only [Real.dist_eq, abs_sub_comm] using hsep
  rwa [abs_of_nonneg (sub_nonneg.mpr hf)] at hsep'

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
