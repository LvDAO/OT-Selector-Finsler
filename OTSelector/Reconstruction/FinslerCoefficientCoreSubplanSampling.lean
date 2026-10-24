import OTSelector.Reconstruction.FinslerCoefficientCoreNormalizedLaw
import OTSelector.Probability.CommonSubplanSampling

/-!
# Actual Taylor-cell sampling with one fixed original residual

Both colors keep their exact original and frozen normalized marginal laws.
The common subplan belongs to the original coupling, so its complement retains
all original support and calibration properties.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

open Function Manifold OTSelector.Geometry
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Both actual color laws on one positive-mass Taylor cell retain the
marginals of one fixed original subplan. The discarded original mass controls
both common-sampling disagreements. -/
theorem PopulationLocalPressureCore.FrozenCellNormalizationData.original_subplan_sampling
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) (z₀ : ℚ → M)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hdata : D.FrozenCellNormalizationData hF hcomplete hu ha hinj i L hL hsub z₀ ε)
    (hmass : 0 < lambda.real L) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let μ := (κ C.seedIndex).restrict (R '' L)
    let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
    let actual := fun color : Fin 2 ↦ μ.withDensity ρ ⊗ₘ
      populationSeedCoordinateClockKernel S a ha
        (populationTwoColorClockKernel u a η₀ η₁ color)
    let frozen := fun color : Fin 2 ↦ (D.rootIntensity i z₀).toNNReal •
      μ.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)
    ∀ π : Measure ((S.covector.ker × ℝ) × (S.covector.ker × ℝ)),
      Vlasov.IsCoupling π (normalizedFiniteLaw (actual 0))
        (normalizedFiniteLaw (actual 1)) →
      ∃ χ : Measure ((S.covector.ker × ℝ) × (S.covector.ker × ℝ)),
        χ ≤ π ∧ χ.map Prod.fst ≤ normalizedFiniteLaw (frozen 0) ∧
        χ.map Prod.snd ≤ normalizedFiniteLaw (frozen 1) ∧
        (π - χ) univ ≤ ENNReal.ofReal (6 * ε / (1 - ε)) ∧
        ∃ γ₀ : Measure ((S.covector.ker × ℝ) × (S.covector.ker × ℝ)),
          ∃ γ₁ : Measure ((S.covector.ker × ℝ) × (S.covector.ker × ℝ)),
            IsProbabilityMeasure γ₀ ∧ IsProbabilityMeasure γ₁ ∧
            γ₀.map Prod.fst = normalizedFiniteLaw (actual 0) ∧
            γ₀.map Prod.snd = normalizedFiniteLaw (frozen 0) ∧
            γ₁.map Prod.fst = normalizedFiniteLaw (actual 1) ∧
            γ₁.map Prod.snd = normalizedFiniteLaw (frozen 1) ∧
            γ₀ {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
            γ₁ {p | p.1 ≠ p.2} ≤ (π - χ) univ := by
  let _instSamplingMetric : MetricSpace M := F.metricSpace
  let _instSamplingProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSamplingPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let μ := (κ C.seedIndex).restrict (R '' L)
  let ρ := populationSeedPieceHaarDensity P a κ lambda C.seedIndex
  let _instCellHaar := D.cell_haar_finite hF hcomplete hu ha hinj i hL hsub
  let _instCellIntensity := D.cell_intensity_finite hF hcomplete hu ha hinj i hL hsub
  let actual := fun color : Fin 2 ↦ μ.withDensity ρ ⊗ₘ
    populationSeedCoordinateClockKernel S a ha
      (populationTwoColorClockKernel u a η₀ η₁ color)
  let frozen := fun color : Fin 2 ↦ (D.rootIntensity i z₀).toNNReal •
    μ.prod (populationTwoColorClockKernel u a η₀ η₁ color z₀)
  have hactual (color : Fin 2) : 0 < (actual color).real univ := by
    have hm := (D.haar.cell_masses hF hcomplete hu ha hinj i hL hsub).1
    change (μ.withDensity ρ) univ = lambda L at hm
    simpa only [actual, measureReal_def, Measure.compProd_apply_univ, hm] using hmass
  have hfrozen (color : Fin 2) : 0 < (frozen color).real univ := by
    by_contra hn
    have hz : (frozen color).real univ = 0 :=
      le_antisymm (le_of_not_gt hn) measureReal_nonneg
    have he := (hdata color).mass_error
    change |(actual color).real univ - (frozen color).real univ| ≤
      ε * (frozen color).real univ at he
    rw [hz, sub_zero, mul_zero, abs_of_pos (hactual color)] at he
    exact (not_le_of_gt (hactual color)) he
  dsimp only
  intro π hπ
  let _instOriginal0 := normalizedFiniteLaw_probability (actual 0) (hactual 0)
  let _instOriginalMap : IsProbabilityMeasure (π.map Prod.fst) := hπ.1 ▸ inferInstance
  let _instOriginal := Measure.isProbabilityMeasure_of_map (μ := π) Prod.fst
  exact exists_normalized_freezing_subplan_sampling
    (actual 0) (frozen 0) (actual 1) (frozen 1) hε hε1
    (hdata 0) (hdata 1) (hfrozen 0) (hfrozen 1) π hπ

end
end OTSelector.Reconstruction
