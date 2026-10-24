import OTSelector.Reconstruction.FinslerRelativeLawOriginalTruncatedCanonicalTrace
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentModelUniformInput
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalSubcellObservation

/-! Original physical model means retain the same canonical choice on traced cells. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The literal original conditional split proves the same-label support needed
for exact macro/trace canonical model means. No endpoint or iid-selection
condition is supplied by the caller. -/
theorem PopulationLocalPressureCore.original_dependent_model_trace_integral
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    {C T : Type*} [Fintype C] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    {I : Set ℝ} {gap : ℝ} (coreIndex : C → Fin D.haar.continuous.count)
    (Q : C → FiniteScalarBins I gap)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (Kcell : C → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (Kcell c)]
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell Kcell z + Qglobal z)
      (condDistrib u a μ z) (condDistrib u a ν z))
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hχ : χ = (((lambda ⊗ₘ finiteCellPairKernel cell hcell Kcell).map
      sameLabelPopulationPair).map (Prod.map b b)))
    {q n : ℕ} {cost : M → M → ℝ} (Cst : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    {G : Set (ℚ → M)} (hG : MeasurableSet G) (f : M × M →ᵇ ℝ) (tilt : ℝ) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let law := (Cst.refineSubplan η hη).markedLaw n
    let original := D.originalClockClassOldModelValue (q := q) (n := n)
      coreIndex Q reference classify cell f tilt (T := T)
    let traced := D.originalClockClassOldModelValue (q := q) (n := n)
      coreIndex Q reference classify (fun c ↦ cell c ∩ G) f tilt (T := T)
    (Integrable traced law ↔ Integrable original law) ∧
      (∫ sample, traced sample ∂law) = (∫ sample, original sample ∂law) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  have hum : Measurable u := hu.continuous.measurable
  have hshared : ∀ᵐ p ∂χ, a p.1 = a p.2 := by
    rw [hχ]
    exact original_global_retained_shared_labels μ ν lambda a u ha hum b hb
      hμinv hνinv hlabel0 hlabel1 cell hcell Kcell Qglobal hwhole
  let model := fun c (sample : (Fin n → M × Option (Bool × T)) ×
      (Fin n → M × Option (Bool × T))) j k ↦
    (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c)
        (sample.1 j).1 (sample.2 k).1 +
      tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f
        (sample.1 j).1 (sample.2 k).1
  exact Cst.original_truncated_canonical_trace_integral χ ξ a ha hG hshared n cell
    (originalSubplanPhysicalGraph fun c ↦ D.originalClockClassAllowed (coreIndex c) (Q c) (classify c))
    model model

end OTSelector.Reconstruction
