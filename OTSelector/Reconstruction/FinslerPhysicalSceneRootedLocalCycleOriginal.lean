import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLocalCycle
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOptima
import OTSelector.Geometry.Finsler.DistanceLocalizationSupportBound

/-!
# Original Finsler inputs produce actual retained-column local optima

Compact source support makes every section of the original tilted physical
slack integrable. The same original global optimizer families consequently
remain optimal on each measurable physical source restriction, at their exact
retained random columns. No local optimization or cost integrability oracle
is required.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original compact source carrier gives every original physical target
section of the scaled and tilted slack an integrable cost. -/
theorem integrable_original_physical_tilted_cost_section
    (μ : Measure M) [IsFiniteMeasure μ]
    {A : Set M} (hA : IsCompact A) (hμA : ∀ᵐ x ∂μ, x ∈ A)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (scale tilt : ℝ) (y : M) :
    Integrable (fun x ↦ scale * ((F.lengthEDist x y).toReal - u y + u x) +
      tilt * g x y) μ := by
  let _inst : MetricSpace M := F.metricSpace
  have hslack : Integrable (fun x ↦ (F.lengthEDist x y).toReal - u y + u x) μ := by
    have hi : IntegrableOn (fun x ↦ (F.lengthEDist x y).toReal - u y + u x) A μ :=
      ((F.continuous_distance_slack hu).comp
        (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact hA
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμA] at hi
  have hprobe : Integrable (fun x ↦ g x y) μ :=
    Integrable.of_bound (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (G : ℝ) (Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using hbound x y)
  exact (hslack.const_mul scale).add (hprobe.const_mul tilt)

/-- A global optimum for the original physical tilted cost is automatically
optimal on the physical source cell, with its exact original retained columns. -/
theorem isOptimalSemidiscreteAllocation_original_physical_restrict
    (μ : Measure M) [IsFiniteMeasure μ]
    {A : Set M} (hA : IsCompact A) (hμA : ∀ᵐ x ∂μ, x ∈ A)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (scale tilt : ℝ)
    {n : ℕ} (Y : Fin (n + 1) → M) (p : Fin (n + 1) → ℝ)
    (a : M → Fin (n + 1) → ℝ)
    (hopt : IsOptimalSemidiscreteAllocation μ p
      (fun x j ↦ scale * ((F.lengthEDist x (Y j)).toReal - u (Y j) + u x) +
        tilt * g x (Y j)) a) (H : Set M) (hH : MeasurableSet H) :
    IsOptimalSemidiscreteAllocation (μ.restrict H) (physicalSceneRestrictedColumns μ H a)
      (fun x j ↦ scale * ((F.lengthEDist x (Y j)).toReal - u (Y j) + u x) +
        tilt * g x (Y j)) a :=
  isOptimalSemidiscreteAllocation_physicalScene_restrict hopt
    (fun j ↦ integrable_original_physical_tilted_cost_section μ hA hμA hu g hg G hbound
      scale tilt (Y j)) H hH

/-- All original tilt and sample indices retain the same source cell and the
same actual random columns. Integrability follows from original physical data. -/
theorem ae_original_finsler_opposite_allocations_source_restrict
    (μ : Measure M) [IsFiniteMeasure μ] (ν : Measure M)
    {A : Set M} (hA : IsCompact A) (hμA : ∀ᵐ x ∂μ, x ∈ A)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (scale t : ℕ → ℝ)
    (AP AM : ∀ (_k n : ℕ), (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) →
      Fin (n + 1) → ℝ)
    (hopt : ∀ k n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
      IsOptimalSemidiscreteAllocation μ z.2
        (fun x j ↦ scale n * ((F.lengthEDist x (z.1 j)).toReal - u (z.1 j) + u x) +
          t k * g x (z.1 j)) (fun x ↦ AP k n (z, x)) ∧
      IsOptimalSemidiscreteAllocation μ z.2
        (fun x j ↦ scale n * ((F.lengthEDist x (z.1 j)).toReal - u (z.1 j) + u x) +
          (-t k) * g x (z.1 j)) (fun x ↦ AM k n (z, x)))
    (H : Set M) (hH : MeasurableSet H) :
    ∀ k n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
      IsOptimalSemidiscreteAllocation (μ.restrict H)
        (physicalSceneRestrictedColumns μ H (fun x ↦ AP k n (z, x)))
        (fun x j ↦ scale n * ((F.lengthEDist x (z.1 j)).toReal - u (z.1 j) + u x) +
          t k * g x (z.1 j)) (fun x ↦ AP k n (z, x)) ∧
      IsOptimalSemidiscreteAllocation (μ.restrict H)
        (physicalSceneRestrictedColumns μ H (fun x ↦ AM k n (z, x)))
        (fun x j ↦ scale n * ((F.lengthEDist x (z.1 j)).toReal - u (z.1 j) + u x) +
          (-t k) * g x (z.1 j)) (fun x ↦ AM k n (z, x)) := by
  intro k n
  filter_upwards [hopt k n] with z hz
  exact ⟨isOptimalSemidiscreteAllocation_original_physical_restrict μ hA hμA hu
      g hg G hbound (scale n) (t k) z.1 z.2 _ hz.1 H hH,
    isOptimalSemidiscreteAllocation_original_physical_restrict μ hA hμA hu
      g hg G hbound (scale n) (-t k) z.1 z.2 _ hz.2 H hH⟩

/-- Original Finsler chart densities construct the SAME global opposite
optimizer families together with all their exact retained-column local optima. -/
theorem exists_finsler_original_opposite_global_and_restricted_allocations
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ n, scale n ≠ 0)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) :
    ∃ t : ℕ → ℝ,
    ∃ AP AM : ∀ (_k n : ℕ), (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) →
      Fin (n + 1) → ℝ,
      StrictAnti t ∧ (∀ k, 0 < t k) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ k n j, Measurable (fun z ↦ AP k n z j)) ∧
      (∀ k n j, Measurable (fun z ↦ AM k n z j)) ∧
      ∀ k n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
        let cp := fun x j ↦ scale n * ((F.lengthEDist x (z.1 j)).toReal - u (z.1 j) + u x) +
          t k * g x (z.1 j)
        let cm := fun x j ↦ scale n * ((F.lengthEDist x (z.1 j)).toReal - u (z.1 j) + u x) +
          (-t k) * g x (z.1 j)
        IsOptimalSemidiscreteAllocation μ z.2 cp (fun x ↦ AP k n (z, x)) ∧
        IsOptimalSemidiscreteAllocation μ z.2 cm (fun x ↦ AM k n (z, x)) ∧
        ∀ H : Set M, MeasurableSet H →
          IsOptimalSemidiscreteAllocation (μ.restrict H)
            (physicalSceneRestrictedColumns μ H (fun x ↦ AP k n (z, x))) cp
            (fun x ↦ AP k n (z, x)) ∧
          IsOptimalSemidiscreteAllocation (μ.restrict H)
            (physicalSceneRestrictedColumns μ H (fun x ↦ AM k n (z, x))) cm
            (fun x ↦ AM k n (z, x)) := by
  obtain ⟨t, AP, AM, ht, htpos, htzero, hAP, hAM, hopt⟩ :=
    exists_finsler_original_opposite_global_allocations hF hcomplete hdim m μ ν
      hμchart hνchart hA hB hμA hνB u hu scale hscale g hg G hbound
  refine ⟨t, AP, AM, ht, htpos, htzero, hAP, hAM, ?_⟩
  intro k n
  filter_upwards [hopt k n] with z hz
  refine ⟨hz.1, hz.2, ?_⟩
  intro H hH
  exact ⟨isOptimalSemidiscreteAllocation_original_physical_restrict μ hA hμA hu
      g hg G hbound (scale n) (t k) z.1 z.2 _ hz.1 H hH,
    isOptimalSemidiscreteAllocation_original_physical_restrict μ hA hμA hu
      g hg G hbound (scale n) (-t k) z.1 z.2 _ hz.2 H hH⟩

/-- Actual original global optimizers exclude every strict retained rooted
rectangle certificate in their physical tilted cost. Compact source support
supplies all cost-section integrability automatically. -/
theorem ae_original_finsler_rooted_strict_rectangle
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (Penv : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    {A : Set M} (hA : IsCompact A) (hμA : ∀ᵐ x ∂μ, x ∈ A)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (g : M → M → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ≥0) (hbound : ∀ x y, |g x y| ≤ G) (scale tilt : ℝ)
    {n : ℕ} (a : Ω → M → Fin (n + 1) → ℝ) (p : Ω → Fin (n + 1) → ℝ)
    (Y : Ω → Fin (n + 1) → M) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (N : ℝ) (A₀ A₁ B₀ B₁ : Set ((ι → ℝ) × ℝ))
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁) (hdisj : Disjoint A₀ A₁)
    (ε : ℝ) (hε : 0 < ε) :
    let c := fun w x j ↦ scale * ((F.lengthEDist x (Y w j)).toReal - u (Y w j) + u x) +
      tilt * g x (Y w j)
    (∀ᵐ w ∂Penv, IsOptimalSemidiscreteAllocation μ (p w) (c w) (a w)) →
    (∀ᵐ w ∂Penv, ∀ z : ι → ℝ, ∀ x ∈ H, ∀ x' ∈ H,
      (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
      ∀ j, (coord (Y w j) - z, u (Y w j)) ∈ B₀ →
      ∀ l, (coord (Y w l) - z, u (Y w l)) ∈ B₁ →
        ε ≤ c w x j + c w x' l - c w x l - c w x' j) →
    ∀ᵐ w ∂Penv, ∀ z : ι → ℝ,
      min
        (physicalSceneRootedPlan ((physicalSceneGlobalAllocationFamily μ a Y w).restrict
          (H ×ˢ univ)) coord u N z (A₀ ×ˢ B₀))
        (physicalSceneRootedPlan ((physicalSceneGlobalAllocationFamily μ a Y w).restrict
          (H ×ˢ univ)) coord u N z (A₁ ×ˢ B₁)) = 0 := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro hopt hgap
  exact ae_physicalSceneGlobalAllocationFamily_original_optimal_strict_rectangle Penv μ a _ p
    hopt (Eventually.of_forall fun w j ↦ integrable_original_physical_tilted_cost_section
      μ hA hμA hu g hg G hbound scale tilt (Y w j)) Y H hH coord hcoord
    u hu.continuous.measurable N A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj ε hε hgap

end OTSelector.Reconstruction
