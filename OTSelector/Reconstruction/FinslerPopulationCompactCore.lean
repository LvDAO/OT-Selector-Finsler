import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Probability.ConditionalLawCompactCore
import OTSelector.Geometry.Finsler.HopfRinow

/-!
# Common compact cores of both original physical conditional laws

The actual physical atlas densities construct one arbitrarily large compact label
core on which both original conditional probabilities vary continuously in total
variation. Every specified almost-everywhere geometric or moment property is retained.
The conditional laws remain the original full laws on the original labels.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The two explicit original physical label-clock densities, on their shared reference. -/
def populationTwoColorDensity (P : ℕ → F.CalibratedSeedWindow u) (a : M → (ℚ → M))
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure (ℚ → M))
    (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ) (i : Fin 2) : (ℚ → M) × ℝ → ℝ≥0∞ :=
  if i = 0 then populationConditionalDensity P a κ lambda ρ₀ v
  else populationConditionalDensity P a κ lambda ρ₁ v

/-- The two original scalar conditional kernels, with the fixed color indexing. -/
def populationTwoColorClockKernel (u : M → ℝ) (a : M → (ℚ → M))
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (i : Fin 2) :
    Kernel (ℚ → M) ℝ :=
  if i = 0 then condDistrib u a η₀ else condDistrib u a η₁

instance populationTwoColorClockKernel_isMarkov (u : M → ℝ) (a : M → (ℚ → M))
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (i : Fin 2) :
    IsMarkovKernel (populationTwoColorClockKernel u a η₀ η₁ i) := by
  unfold populationTwoColorClockKernel
  split <;> infer_instance

/-- Any finite label region has an arbitrarily large common compact continuity core
for both original laws, retaining every requested almost-everywhere property. -/
def PopulationConditionalCompactCoreLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ) : Prop :=
  let H := populationTwoColorDensity P a κ lambda ρ₀ ρ₁ v
  let k := populationTwoColorClockKernel u a η₀ η₁
  ∀ (Good : (ℚ → M) → Prop), (∀ᵐ z ∂lambda, Good z) →
    ∀ (s : Set (ℚ → M)), MeasurableSet s → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ (L : Fin 2 → (ℚ → M) → Lp ℝ 1 (volume : Measure ℝ)) (K : Set (ℚ → M)),
        (∀ i, @Measurable _ _ _ (borel _) (L i)) ∧ K ⊆ s ∧ IsCompact K ∧
        lambda (s \ K) < ε ∧ ContinuousOn (fun z i ↦ L i z) K ∧
        (∀ z ∈ K, Good z ∧ ∀ i,
          (∫⁻ t, H i (z, t)) = 1 ∧
          (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = k i z ∧
          (⇑(L i z)) =ᵐ[volume] (fun t ↦ (H i (z, t)).toReal)) ∧
        (∀ i, ∀ z ∈ K, ∀ z' ∈ K,
          ((k i z).toSignedMeasure - (k i z').toSignedMeasure).totalVariation univ =
            ENNReal.ofReal ‖L i z - L i z'‖) ∧
        ∀ i, ContinuousOn (fun p : (ℚ → M) × (ℚ → M) ↦
          ((k i p.1).toSignedMeasure - (k i p.2).toSignedMeasure).totalVariation univ)
          (K ×ˢ K)

omit [BorelSpace E] in
/-- Actual physical atlas laws supply compact total-variation cores for both colors
without an external conditional density, normalization or continuity hypothesis. -/
theorem PopulationConditionalWindowLaw.compact_core
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
    (hsource : PopulationConditionalWindowLaw P a κ lambda η₀ ρ₀ v)
    (htarget : PopulationConditionalWindowLaw P a κ lambda η₁ ρ₁ v)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) :
    PopulationConditionalCompactCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v := by
  classical
  let _instPhysicalCoreMetric : MetricSpace M := F.metricSpace
  let _instPhysicalCoreComplete : CompleteSpace M := hcomplete
  let _instPhysicalCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPhysicalCorePolish : PolishSpace M := inferInstance
  let _instPhysicalCoreLabelsPolish : PolishSpace (ℚ → M) := inferInstance
  let _instPhysicalCoreLabelsBorel : BorelSpace (ℚ → M) := inferInstance
  have hfinite : IsFiniteMeasure lambda := hsource.label_law ▸ inferInstance
  let H := populationTwoColorDensity P a κ lambda ρ₀ ρ₁ v
  let k := populationTwoColorClockKernel u a η₀ η₁
  have hH (i : Fin 2) : Measurable (H i) := by
    dsimp only [H, populationTwoColorDensity]
    split
    · exact hsource.density_measurable
    · exact htarget.density_measurable
  have hnorm (i : Fin 2) : ∀ᵐ z ∂lambda, ∫⁻ t, H i (z, t) = 1 := by
    dsimp only [H, populationTwoColorDensity]
    split
    · exact hsource.normalized
    · exact htarget.normalized
  have hk (i : Fin 2) : ∀ᵐ z ∂lambda,
      (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = k i z := by
    dsimp only [H, k, populationTwoColorDensity, populationTwoColorClockKernel]
    split
    · exact hsource.conditional_law
    · exact htarget.conditional_law
  intro Good hGood s hs ε hε
  exact exists_conditionalLaw_compact_core lambda H k hH hnorm hk hGood hs
    (measure_ne_top _ _) hε

end OTSelector.Reconstruction
