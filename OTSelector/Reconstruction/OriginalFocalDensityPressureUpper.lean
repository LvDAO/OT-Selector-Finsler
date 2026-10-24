import OTSelector.Reconstruction.OriginalFocalWindowPressureUpper
import OTSelector.Reconstruction.OriginalDensityWeightedPressureUpper
import OTSelector.MeasureTheory.RetainedLawVariation

/-! Expanding original clock windows retain the same full original focal
kernel. Original inverse-compliance comparison gives one bound before every
window, while actual retained original laws recover the full pressure upper. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Module Manifold
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual retained original pair mass and scalar retention recover the
full true Haar-weighted original pressure upper, including zero density. The
same original full focal coefficient controls every expanding clock screen. -/
theorem exists_original_retained_density_pressure_upper
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (π : Measure (ℝ × ℝ)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (χ : ℕ → Measure (ℝ × ℝ)) (hχ : ∀ n, χ n ≤ π)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ1 : ∀ n, δ n < 1)
    (hmass : ∀ n, 1 - δ n ≤ (χ n).real univ)
    {G : ℝ} (hG : 0 ≤ G) (g : ℝ → ℝ → ℝ)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (density : ℝ) (hdensity0 : 0 ≤ density)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0)) (hη1 : ∀ n, η n ≤ 1) :
    let _ : IsProbabilityMeasure μ := D.support.source.probability
    let _ : IsProbabilityMeasure ν := D.support.target.probability
    ∃ πret : ℕ → ProbabilityMeasure (ℝ × ℝ),
      (∀ n, (πret n : Measure (ℝ × ℝ)) = normalizedFiniteLaw (χ n)) ∧
    ∃ pref : ℝ → ℝ, ∃ p : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id μ ν
        (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a,b)) v) g R t)
          atTop (𝓝 (pref t))) ∧
      (∀ n t, Tendsto (fun R ↦ legalMarkedScalePressure (finrank ℝ S.covector.ker) id id
        ((πret n).map measurable_fst.aemeasurable : Measure ℝ)
        ((πret n).map measurable_snd.aemeasurable : Measure ℝ)
        (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a,b)) v) g R t)
          atTop (𝓝 (p n t))) ∧
      LipschitzWith ⟨G,hG⟩ pref ∧ (∀ n, LipschitzWith ⟨G,hG⟩ (p n)) ∧
      (∀ t ε, 0 < ε → ∀ᶠ n in atTop, p n t < pref t + ε) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop,
        (((1 - η n) * density) * (χ n).real univ) ^ (1 - 2 / (finrank ℝ S.covector.ker : ℝ)) *
          p n (t * (((1 - η n) * density) * (χ n).real univ) ^ (2 / (finrank ℝ S.covector.ker : ℝ))) <
        density ^ (1 - 2 / (finrank ℝ S.covector.ker : ℝ)) *
          pref (t * density ^ (2 / (finrank ℝ S.covector.ker : ℝ))) + ε := by
  letI : IsProbabilityMeasure μ := D.support.source.probability
  letI : IsProbabilityMeasure ν := D.support.target.probability
  haveI : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.symm ▸ D.support.source.probability
  haveI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  letI : ∀ n, IsFiniteMeasure (χ n) := fun n ↦ isFiniteMeasure_of_le π (hχ n)
  obtain ⟨πret,hπret,pref,p,href,hpt,hLipref,hLip,hupper⟩ :=
    D.exists_original_retained_pressure_upper hF hw hq hgap hbounds π hπ horder χ hχ
      δ hδ hδ0 hδ1 hmass hG g hg hgb
  have hmasslim : Tendsto (fun n ↦ (χ n).real univ) atTop (𝓝 1) :=
    tendsto_submeasure_mass_of_lost_mass π χ atTop δ hδ
      (Filter.Eventually.of_forall fun n ↦ ⟨hχ n,hmass n⟩)
  have hdensity : Tendsto (fun n ↦ ((1 - η n) * density) * (χ n).real univ)
      atTop (𝓝 density) := by
    have hconst : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := ((hconst.sub hη).mul_const density).mul hmasslim
    change Tendsto (fun n ↦ ((1 - η n) * density) * (χ n).real univ)
      atTop (𝓝 (((1 - 0) * density) * 1)) at hh
    simpa only [sub_zero,one_mul,mul_one] using hh
  have hnonneg n : 0 ≤ ((1 - η n) * density) * (χ n).real univ :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr (hη1 n)) hdensity0) measureReal_nonneg
  have hqR : (2 : ℝ) < (finrank ℝ S.covector.ker : ℝ) := by exact_mod_cast (by omega : 2 < finrank ℝ S.covector.ker)
  refine ⟨πret,hπret,pref,p,href,hpt,hLipref,hLip,hupper,?_⟩
  intro t ε hε
  exact eventually_density_weighted_pressure_lt atTop hqR p pref ⟨G,hG⟩ hLip hupper
    (fun n ↦ ((1 - η n) * density) * (χ n).real univ) density hdensity hnonneg t ε hε

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
