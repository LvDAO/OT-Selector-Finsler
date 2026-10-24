import OTSelector.Reconstruction.FinslerPhysicalSceneRootedPopulationSourceVariation

/-! Finite original conditional-clock references control every source observation without a supplied local freezing premise. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

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
namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The original density and intensity continuity construct finite reference
clock laws that are absolutely continuous. Their simultaneous setwise source
bounds hold for every measurable subcell and every actual measurable observation. -/
theorem exists_original_source_cell_observation_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover 1,
      (∀ z₀ ∈ T.centers, condDistrib u a η₀ z₀ ≪ (volume : Measure ℝ)) ∧
      ∀ z₀ ∈ T.centers, ∀ (L : Set (ℚ → M)) (_hL : MeasurableSet L)
        (_hsub : L ⊆ (D.haar.continuous.coefficient i).roots ∩ T.neighborhood z₀),
      ∀ {X : Type*} [MeasurableSpace X]
        (obs : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker × ℝ → X),
        Measurable obs → ∀ s : Set X, MeasurableSet s →
        ((η₀.restrict (a ⁻¹' L)).map (fun x ↦ obs (D.haar.sceneCoordinate i x))) s ≤
          (((D.rootIntensity i z₀).toNNReal •
            ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
              (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L)).prod
                (condDistrib u a η₀ z₀)).map obs) s +
            ENNReal.ofReal (2 * tolerance * D.rootIntensity i z₀) *
              (κ (D.haar.continuous.coefficient i).seedIndex)
                (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  obtain ⟨T, hT⟩ := D.exists_taylorRootCover_frozen_cell_laws hF hcomplete hu ha hinj i
    (by norm_num : (0 : ℝ) < 1) htolerance
  refine ⟨T, ?_, ?_⟩
  · intro z₀ hz₀
    have hpop : z₀ ∈ D.haar.continuous.population.roots :=
      D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, T.subset hz₀⟩
    have heq := (D.haar.continuous.population.density z₀ hpop (0 : Fin 2)).2.1
    simp only [populationTwoColorClockKernel, ite_true] at heq
    rw [← heq]
    exact withDensity_absolutelyContinuous _ _
  · intro z₀ hz₀ L hL hsub X _ obs hobs s hs
    exact D.original_source_cell_observation_le_frozen_add hF hcomplete hu ha hinj i hL
      (hsub.trans inter_subset_left) z₀ tolerance (hT z₀ hz₀ L hL hsub) obs hobs s hs
end PopulationLocalPressureCore
end OTSelector.Reconstruction
