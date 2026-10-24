import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationWholeReadoutFace
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Actual original probe-gap expectations give probability convergence

The experiments may change with the sample size. A positive real probe-gap
threshold is controlled directly by the original nonnegative expectation.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Vanishing expectations on changing original experiments control their
positive real threshold events on the unchanged index filter. -/
theorem tendsto_measure_ge_of_lintegral_ofReal_tendsto_zero
    {ι : Type*} (L : Filter ι) {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (Renv : ∀ i, Measure (Ω i)) (f : ∀ i, Ω i → ℝ)
    (hf : ∀ i, AEMeasurable (f i) (Renv i))
    (hmean : Tendsto (fun i ↦ ∫⁻ w, ENNReal.ofReal (f i w) ∂Renv i) L (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun i ↦ Renv i {w | ε ≤ f i w}) L (𝓝 0) := by
  have hεne : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hbound (i : ι) : Renv i {w | ε ≤ f i w} ≤
      (∫⁻ w, ENNReal.ofReal (f i w) ∂Renv i) / ENNReal.ofReal ε := by
    apply le_trans (measure_mono (fun w hw ↦ ENNReal.ofReal_le_ofReal hw))
    exact meas_ge_le_lintegral_div
      (ENNReal.measurable_ofReal.comp_aemeasurable (hf i)) hεne ENNReal.ofReal_ne_top
  have hlim : Tendsto
      (fun i ↦ (∫⁻ w, ENNReal.ofReal (f i w) ∂Renv i) / ENNReal.ofReal ε) L (𝓝 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hmean (Or.inr hεne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlim (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall hbound)

set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


/-- Every complete bounded continuous original endpoint probe has a vanishing
probability of any positive actual raw-plan gap, in the original two-index order. -/
theorem tendsto_originalAllocation_continuous_probe_gap_probability_zero_of_original_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 6 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M}
    (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    (hnormalization : ∀ n, scale n ^ (finrank ℝ E - 1) = (n : ℝ) + 1)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobeBound : ∀ x y, |probe x y| ≤ G)
    (t : ℕ → ℝ) (ht0 : ∀ ℓ, 0 ≤ t ℓ) (ht0lim : Tendsto t atTop (𝓝 0))
    (ap am : ∀ (_ℓ n : ℕ),
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 j))
    (hmm : ∀ ℓ n j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 j))
    (hp : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            t ℓ * probe x (w.1 j)) (ap ℓ n w))
    (hm : ∀ ℓ n,
      ∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            (-t ℓ) * probe x (w.1 j)) (am ℓ n w))
    (hμlaw : PopulationConditionalWindowLaw P a κ (μ.map a) μ ρ₀ v)
    (hνlaw : PopulationConditionalWindowLaw P a κ (μ.map a) ν ρ₁ v)
    (hAsupport : IsCompact A) (hBsupport : IsCompact B) (hAB : Disjoint A B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hbalance : μ.map a = ν.map a)
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    (hnearRadius : 0 < nearRadius)
    :
    let _inst : MetricSpace M := F.metricSpace
    ∀ (f : (M × M) →ᵇ ℝ) (ε : ℝ), 0 < ε →
      Tendsto (fun z : ℕ × ℕ ↦
        ((Measure.pi (fun _ : Fin (z.2 + 1) ↦ ν)).prod (dirichletOne z.2))
          {w | ε ≤ |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
              (ap z.1 z.2) (fun w ↦ w.1) w) -
            ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
              (am z.1 z.2) (fun w ↦ w.1) w|})
        ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  dsimp only
  intro f ε hε
  have hgap := tendsto_originalAllocation_continuous_probe_gap_curry_zero_of_original_face
    hF hcomplete hu ha hinj horder hdim m hμchart hνchart nearRadius
    scale hscalePos hscale hnormalization probe hprobe G hprobeBound t ht0 ht0lim
    ap am hpm hmm hp hm hμlaw hνlaw hAsupport hBsupport hAB hμreg hνreg
    hκ hbalance hcore hrecovery hface hμA hνB hnearRadius f
  exact tendsto_measure_ge_of_lintegral_ofReal_tendsto_zero
    ((atTop : Filter ℕ).curry atTop)
    (fun z : ℕ × ℕ ↦ (Measure.pi (fun _ : Fin (z.2 + 1) ↦ ν)).prod (dirichletOne z.2))
    (fun z w ↦ |(∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
        (ap z.1 z.2) (fun w ↦ w.1) w) -
      ∫ e, f e ∂physicalSceneGlobalAllocationFamily μ
        (am z.1 z.2) (fun w ↦ w.1) w|)
    (fun z ↦ (hgap.1 z.1 z.2).aemeasurable) hgap.2.2 ε hε

end OTSelector.Reconstruction
