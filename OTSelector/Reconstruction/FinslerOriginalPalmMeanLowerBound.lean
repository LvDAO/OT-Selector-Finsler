import OTSelector.Reconstruction.FocalPalmSignedMeanLimit
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalPalmTightness

/-! The actual original Finsler Palm limit has the minimizing-sequence energy bound. -/
open Set Function MeasureTheory Filter Topology Matrix Module Manifold
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Convergence of genuine original weighted values and true Palm laws gives
the original limiting signed value bound. Both marginal laws, the open clock
carrier and the positive gap are derived from the original data. -/
theorem integrable_original_focal_signedPalm_of_truePalm_weak
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgc : ContinuousOn (Function.uncurry g)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2})
    {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G)
    (Q : ℕ → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (η : ProbabilityMeasure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (hweak : Tendsto (fun n ↦ (Q n).truePalmProbability) atTop (𝓝 η))
    (t p : ℝ) (hmean : Tendsto (fun n ↦ (Q n).value t) atTop (𝓝 p)) :
    Integrable (fun m ↦ D.originalFocalKinetic gap m.1.1 m.1.2 m.2)
        (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) ∧
      Integrable (fun m ↦ g m.1.1 m.1.2)
        (η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) ∧
      (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
        ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))) +
        t * (∫ m, g m.1.1 m.1.2
          ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))) ≤ p := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let q := finrank ℝ S.covector.ker
  let J : Set ℝ := {a | a - S.level ∈ Ioo D.lo D.hi}
  let O : Set (ℝ × ℝ) := {p | p.1 ∈ J ∧ p.2 ∈ J ∧ p.1 < p.2}
  let W : Set (ℝ × ℝ) :=
    {p | (p.1 ∈ J ∧ p.1 ∈ μ.support) ∧
      (p.2 ∈ J ∧ p.2 ∈ ν.support) ∧ p.1 < p.2}
  have hJ : IsOpen J := isOpen_Ioo.preimage (continuous_id.sub continuous_const)
  have hO : IsOpen O := (hJ.preimage continuous_fst).inter
    ((hJ.preimage continuous_snd).inter (isOpen_lt continuous_fst continuous_snd))
  have hW (θ : Measure (PhysicalPairPalmMark (Fin q)))
      (hs : θ.map (fun m ↦ m.1.1) = μ) (ht : θ.map (fun m ↦ m.1.2) = ν)
      (hf : ∀ᵐ m ∂θ, m.1.1 ≤ m.1.2) : ∀ᵐ m ∂θ, m.1 ∈ W := by
    have ha : ∀ᵐ m ∂θ, m.1.1 ∈ J ∧ m.1.1 ∈ μ.support := by
      have h : ∀ᵐ a ∂θ.map (fun m ↦ m.1.1), a ∈ J ∧ a ∈ μ.support := by
        rw [hs]
        exact D.support.source.ae_open.and μ.support_mem_ae
      exact ae_of_ae_map measurable_fst.fst.aemeasurable h
    have hb : ∀ᵐ m ∂θ, m.1.2 ∈ J ∧ m.1.2 ∈ ν.support := by
      have h : ∀ᵐ b ∂θ.map (fun m ↦ m.1.2), b ∈ J ∧ b ∈ ν.support := by
        rw [ht]
        exact D.support.target.ae_open.and ν.support_mem_ae
      exact ae_of_ae_map measurable_fst.snd.aemeasurable h
    filter_upwards [ha, hb, hf] with m ha hb hf
    have hsep : gap ≤ |m.1.2 - m.1.1| := by
      simpa only [Real.dist_eq, abs_sub_comm] using
        hbounds.separated m.1.1 ha.2 m.1.2 hb.2
    rw [abs_of_nonneg (sub_nonneg.mpr hf)] at hsep
    exact ⟨ha, hb, by linarith⟩
  have hcarriers (n : ℕ) :
      ∀ᵐ m ∂((Q n).truePalmProbability : Measure (PhysicalPairPalmMark (Fin q))), m.1 ∈ W :=
    hW _ (Q n).source_clock (Q n).target_clock
      ((Q n).ae_palm_forward.mono fun _ hm ↦ hm.le)
  obtain ⟨hs, ht⟩ := D.clock_marginals_of_truePalm_weak Q η hweak
  have hcarrier := hW (η : Measure (PhysicalPairPalmMark (Fin q))) hs ht
    (D.ae_forward_order_of_truePalm_weak Q η hweak)
  have hIs (n : ℕ) : Integrable
      (fun m ↦ D.originalFocalKinetic gap m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
      ((Q n).truePalmProbability : Measure (PhysicalPairPalmMark (Fin q))) :=
    (Q n).kinetic_integrable.add ((Q n).probe_integrable.const_mul t)
  have hmean' : Tendsto (fun n ↦ ∫ m,
      D.originalFocalKinetic gap m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
      ∂((Q n).truePalmProbability : Measure (PhysicalPairPalmMark (Fin q))))
      atTop (𝓝 p) := by
    have heq (n : ℕ) : (∫ m,
        D.originalFocalKinetic gap m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
        ∂((Q n).truePalmProbability : Measure (PhysicalPairPalmMark (Fin q)))) =
          (Q n).value t := by
      change (∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2
        ∂legalMarkedJointPalm q (Q n).law) = (Q n).value t
      rw [integral_add (Q n).kinetic_integrable ((Q n).probe_integrable.const_mul t),
        integral_const_mul]
      rfl
    simpa only [heq] using hmean
  exact integrable_original_focal_signed_energy_le_of_weak_mean_limit q hO
    (fun _ hp ↦ ⟨hp.1.1, hp.2.1.1, hp.2.2⟩)
    (originalSeedPairCoefficient S w) (D.continuousOn_pair_coefficient_interior hF hw)
    (fun p hp ↦ (D.pair_compliance_posDef hF hw hp.1 hp.2.1 hp.2.2).2.posSemidef)
    (D.measurable_originalFocalKinetic hF hw gap) (D.originalFocalKinetic_nonneg hF hw hgap)
    (fun p hp v ↦ D.originalFocalKinetic_eq_of_original_support
      hbounds hp.1 hp.2.1 hp.2.2 v) hg hgc hgb t p
    (fun n ↦ (Q n).truePalmProbability) η hweak hcarriers hcarrier hIs hmean'

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
