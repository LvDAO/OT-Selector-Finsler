import OTSelector.Reconstruction.MarkedStationaryValueLegalGenuineTruePalmClosure
import OTSelector.Reconstruction.FinslerOriginalMinimizingPalm

/-!
# An actual original weighted stationary minimizer

The direct method closes the same original scene and full-displacement Palm.
The resulting law is a genuine full one-to-one stationary matching with the
prescribed original Poisson input, and attains the original weighted infimum.
-/
open Set Function MeasureTheory Filter Topology Module Manifold
open scoped ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original general Finsler conditional data produce a genuine weighted
stationary minimizer. Neither an external minimizing law, a displacement
second moment, nor a whole-marginal closure hypothesis is supplied. -/
theorem exists_original_weighted_stationary_minimizer
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (hgc : ContinuousOn (Function.uncurry g)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2}) (t : ℝ) :
    ∃ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g,
      R.value t = D.originalWeightedStationaryInf gap g t ∧
      ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
        (D.originalFocalKinetic gap) g, R.value t ≤ P.value t := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  obtain ⟨hinf, N, η, _hmean, _hB, hPalm, hsource, htarget, hkin, hprobe, henergy⟩ :=
    D.exists_original_minimizing_truePalm_energy_le hF hw hq hgap hbounds
      π hπ horder hg hgb hgc t
  have hηgap : ∀ᵐ m ∂(η : Measure
      (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))), gap ≤ m.1.2 - m.1.1 := by
    have ha : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
        m.1.1 ∈ μ.support := by
      have h : ∀ᵐ a ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map
          (fun m ↦ m.1.1), a ∈ μ.support := by
        rw [hsource]
        exact μ.support_mem_ae
      exact ae_of_ae_map measurable_fst.fst.aemeasurable h
    have hb : ∀ᵐ m ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))),
        m.1.2 ∈ ν.support := by
      have h : ∀ᵐ b ∂(η : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))).map
          (fun m ↦ m.1.2), b ∈ ν.support := by
        rw [htarget]
        exact ν.support_mem_ae
      exact ae_of_ae_map measurable_fst.snd.aemeasurable h
    filter_upwards [ha, hb, D.ae_forward_order_of_truePalm_weak N η hPalm] with m ha hb hf
    have hsep : gap ≤ |m.1.2 - m.1.1| := by
      simpa only [Real.dist_eq, abs_sub_comm] using hbounds.separated m.1.1 ha m.1.2 hb
    rwa [abs_of_nonneg (sub_nonneg.mpr hf)] at hsep
  obtain ⟨Q, φ, hφ, hweak, _hstat, _hlap⟩ :=
    exists_stationary_originalInput_subseq_canonicalFirstInputLaw N
  let L : ℕ → LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g := fun n ↦ (N (φ n)).canonicalFirstInput
  have hPalm' : Tendsto (fun n ↦ (L n).truePalmProbability) atTop (𝓝 η) := by
    have heq (n : ℕ) : (L n).truePalmProbability = (N (φ n)).truePalmProbability := by
      apply Subtype.ext
      exact legalMarkedJointPalm_canonicalFirstInputLaw _ _
    simpa only [heq, Function.comp_def] using hPalm.comp hφ.tendsto_atTop
  obtain ⟨R, _hRlaw, hRpalm⟩ := exists_genuineStationary_of_scene_and_truePalm_weak
    (by omega : 0 < finrank ℝ S.covector.ker) L Q hweak η hPalm' hsource htarget hgap
    hηgap hkin hprobe
  have hRle : R.value t ≤ D.originalWeightedStationaryInf gap g t := by
    simpa only [LegalWeightedStationaryPoissonMatching.value, hRpalm] using henergy
  have heq := le_antisymm hRle (hinf R)
  exact ⟨R, heq, fun P ↦ hRle.trans (hinf P)⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
