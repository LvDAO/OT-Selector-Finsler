import OTSelector.Reconstruction.OriginalIIDUniformTiltEnergy

/-!
# Actual supported iid energy at the spatial normalization

The proved original supported pressure packet supplies the actual finite
spatial-energy budget required by fixed-seed tail and target-defect estimates.
The original finite-array product law and complete supported tilted edge cost
are retained literally.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped ENNReal Topology NNReal BoundedContinuousFunction Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The complete original supported tilted edge cost is jointly measurable,
including its original measurable support projections. -/
theorem measurable_originalIID_supported_tilt_cost
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (u : M → ℝ) (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (f : (K × K) →ᵇ ℝ) (scale t : ℝ) :
    Measurable (Function.uncurry (fun x y ↦ scale *
      ((F.lengthEDist x y).toReal - u y + u x) +
      t * finslerCarrierProbe μ ν K hK hμ hν f x y)) := by
  let supportedSpatialEnergyMetric : MetricSpace M := F.metricSpace
  let supportedSpatialEnergyProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let supportedSpatialEnergySecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace inferInstance
  have hb : Measurable (Function.uncurry (fun x y : M ↦ scale *
      ((F.lengthEDist x y).toReal - u y + u x))) :=
    (((measurable_fst.dist measurable_snd).sub
      (hu.continuous.measurable.comp measurable_snd)).add
      (hu.continuous.measurable.comp measurable_fst)).const_mul scale
  have hp : Measurable (Function.uncurry (finslerCarrierProbe μ ν K hK hμ hν f)) :=
    f.continuous.measurable.comp
      (((measurable_supportProjection μ K hK hμ).comp measurable_fst).prodMk
        ((measurable_supportProjection ν K hK hν).comp measurable_snd))
  exact hb.add (hp.const_mul t)

variable {u : M → ℝ} {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : ProbabilityMeasure M} {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
  {b : (ℚ → M) × ℝ → M} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual supported pressure packet gives a finite eventual true slack
energy bound at the exact spatial scale, under the literal original iid law.
No energy-budget or local-law callback is assumed. -/
theorem PopulationLocalPressureCore.exists_eventually_originalIID_supported_spatial_energy_bound
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (hdata : D.originalSupportedWeightUnitDensityPressureData γ originalGap Q U
      retentionError splitError K hK hμ hν f g ε probeError
      (fun n ↦ canonicalLaw μ ν n) (fun n ↦ canonicalX n) (fun n ↦ canonicalY n))
    (t : ℝ) (spatialScale : ℕ → ℝ)
    (hnorm : ∀ n, spatialScale n ^ 2 = finslerMeanScale E n) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale n ^ 2 *
          ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan
          (fun x y ↦ finslerMeanScale E n *
            ((F.lengthEDist x y).toReal - u y + u x) +
            t * finslerCarrierProbe μ ν K hK.measurableSet hμ hν f x y) 1 ξ
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (μ : Measure M))).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M)))) ≤ C := by
  obtain ⟨C, _hC, hbound⟩ :=
    PopulationLocalPressureCore.exists_eventually_originalIID_supported_uniform_tilt_energy_bound
      hcomplete hu γ originalGap D Q U retentionError splitError K hK hμ hν
      f g ε probeError hdata |t| (abs_nonneg t)
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [hbound] with n hn
  simpa only [hnorm n, canonicalLaw, twoColourLaw] using hn t le_rfl

end OTSelector.Reconstruction

