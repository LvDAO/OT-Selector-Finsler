import OTSelector.Geometry.Finsler.Calibration.PopulationConditionalLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSeedProbeDetermination
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests

/-!
# A fixed countable family of original seed probes determines the coupling

The tests are chosen solely from each original seed coordinate space. They do
not depend on a plan, a sample, a tilt, or an auxiliary accuracy core.
-/
open Set Function MeasureTheory Manifold Module TopologicalSpace OTSelector.Geometry
open scoped Topology ContDiff CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

section Observation
variable {S T : Type*} [MeasurableSpace S]
  [TopologicalSpace T] [MeasurableSpace T] [T2Space T] [LocallyCompactSpace T]
  [BorelSpace T] [PseudoMetrizableSpace T] [SigmaCompactSpace T]
  [SecondCountableTopology T]

/-- The fixed countable compact tests already determine every compact readout
of any finite measured observation. -/
theorem compact_probe_integral_eq_of_separating_probe_eq
    {f : S → T} (hf : Measurable f)
    {π₀ π₁ : Measure S} [IsFiniteMeasure π₀] [IsFiniteMeasure π₁]
    (htest : ∀ i : ℕ ⊕ (ℕ × ℕ),
      ∫ x, OTSelector.Probability.LocalFiniteMeasure.separatingTest
          (CompactExhaustion.choice T) i (f x) ∂π₀ =
      ∫ x, OTSelector.Probability.LocalFiniteMeasure.separatingTest
          (CompactExhaustion.choice T) i (f x) ∂π₁) :
    ∀ g : C_c(T, ℝ), ∫ x, g (f x) ∂π₀ = ∫ x, g (f x) ∂π₁ := by
  let ν₀ : OTSelector.Probability.LocalFiniteMeasure T := ⟨π₀.map f, inferInstance⟩
  let ν₁ : OTSelector.Probability.LocalFiniteMeasure T := ⟨π₁.map f, inferInstance⟩
  have hcode : OTSelector.Probability.LocalFiniteMeasure.separatingTestCode
      (CompactExhaustion.choice T) ν₀ =
      OTSelector.Probability.LocalFiniteMeasure.separatingTestCode
        (CompactExhaustion.choice T) ν₁ := by
    funext i
    let g := OTSelector.Probability.LocalFiniteMeasure.separatingTest
      (CompactExhaustion.choice T) i
    change ∫ x, g x ∂π₀.map f = ∫ x, g x ∂π₁.map f
    calc
      ∫ x, g x ∂π₀.map f = ∫ x, g (f x) ∂π₀ :=
        integral_map (f := fun x ↦ g x) hf.aemeasurable g.continuous.aestronglyMeasurable
      _ = ∫ x, g (f x) ∂π₁ := htest i
      _ = ∫ x, g x ∂π₁.map f :=
        (integral_map (f := fun x ↦ g x) hf.aemeasurable
          g.continuous.aestronglyMeasurable).symm
  have heq : π₀.map f = π₁.map f := congrArg Subtype.val
    (OTSelector.Probability.LocalFiniteMeasure.separatingTestCode_injective
      (CompactExhaustion.choice T) hcode)
  intro g
  calc
    ∫ x, g (f x) ∂π₀ = ∫ y, g y ∂π₀.map f :=
      (integral_map (f := fun x ↦ g x) hf.aemeasurable g.continuous.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂π₁.map f := by rw [heq]
    _ = ∫ x, g (f x) ∂π₁ :=
      integral_map (f := fun x ↦ g x) hf.aemeasurable g.continuous.aestronglyMeasurable
end Observation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}

/-- One fixed countable family in the unchanged original seed coordinate. -/
def physicalSceneOriginalSeedSeparatingProbe (j : ℕ) (i : ℕ ⊕ (ℕ × ℕ)) :
    C_c((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ), ℝ) :=
  OTSelector.Probability.LocalFiniteMeasure.separatingTest
    (CompactExhaustion.choice ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (ℝ × ℝ))) i

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- The fixed countable original probes determine the entire physical coupling,
using the original conditional population law and original regular ray carrier. -/
theorem original_coupling_eq_of_countable_seed_probe_eq
    {μ : Measure M} [IsFiniteMeasure μ] {ρ : M → ℝ} {v : ℕ → E → ℝ}
    (hlaw : PopulationConditionalWindowLaw P a κ lambda μ ρ v)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j))
    {π₀ π₁ : Measure (M × M)} [IsFiniteMeasure π₀] [IsFiniteMeasure π₁]
    (hsource₀ : π₀.fst = μ) (hsource₁ : π₁.fst = μ)
    (hπ₀ : ∀ᵐ p ∂π₀, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2)
    (hπ₁ : ∀ᵐ p ∂π₁, p.1 ∈ F.potentialRegularDomain u ∧
      p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2)
    (htest : ∀ j : ℕ, ∀ i : ℕ ⊕ (ℕ × ℕ),
      ∫ p, physicalSceneOriginalSeedSeparatingProbe (P := P) j i
          (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₀.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ) =
      ∫ p, physicalSceneOriginalSeedSeparatingProbe (P := P) j i
          (physicalSceneOriginalSeedPairReadout (P := P) (a := a) j p)
        ∂π₁.restrict (physicalSceneOriginalSeedSource
          (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ)) :
    π₀ = π₁ := by
  apply original_coupling_eq_of_seed_compact_probe_eq hF hcomplete hu ha hinj
    hlaw horder hκ hsource₀ hsource₁ hπ₀ hπ₁
  intro j
  exact compact_probe_integral_eq_of_separating_probe_eq
    (measurable_physicalSceneOriginalSeedPairReadout hF hcomplete hu ha hinj j) (htest j)

end OTSelector.Reconstruction
