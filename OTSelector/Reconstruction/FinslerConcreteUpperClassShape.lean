import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineDensity

/-!
The actual original finite class coefficient model has the sharp microscopic
shape comparison. Its literal pair-class law, original physical cost scale and
actual density-weighted count intensity are kept distinct throughout.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- All graph, measurability, homogeneity and kernel bounds in the physical
microscopic shape-pressure comparison are produced from the actual original
coefficient core. The error uses the literal original hole mass. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_affine_shape_comparison
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ (source target : Fin Q.count → ℝ) (rankBins : FiniteScalarBins
      (Icc (-((Q.count : ℝ) + 1)) 1) (1 / 2 : ℝ)) (K : ℝ),
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧ 0 ≤ K ∧
      ∀ (ambient density side : ℝ≥0), 0 < density → ∀ origin : Fin q → ℝ,
      ∀ S : Set (Fin q → ℝ), MeasurableSet S → ∀ tilt : ℝ,
      let countIntensity := ambient * density * side ^ q
      let law := (shapeBlockLaw q (α : Measure _) countIntensity S).prod
        (shapeBlockLaw q (β : Measure _) countIntensity S)
      let value := fun d : BlockData ((Fin q → ℝ) × Fin Q.count) × BlockData ((Fin q → ℝ) × Fin Q.count) ↦
        unclampedBlockLegalTilted q source target ambient (C.clockClassKinetic Q z₀)
          (C.clockClassProbe Q z₀ hz₀ f) tilt
          (mapBlockData (affineMarkedPoint origin side) d.1)
          (mapBlockData (affineMarkedPoint origin side) d.2)
      Integrable value law ∧
      |(∫ d, value d ∂law) - finiteClassLegalPressure q (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) countIntensity
        (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt| ≤
        (2 * (countIntensity : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
          (2 * ((rankBins.count : ℝ) + 1) *
            ((countIntensity : ℝ) ^ (2 / (q : ℝ)) *
              (((density : ℝ) ^ (-(2 / (q : ℝ))) * K) * q) + |tilt| * ‖f‖)) := by
  classical
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, hsep, hsource, htarget⟩ := C.exists_clockClass_strict_clocks Q
  obtain ⟨rankBins⟩ := exists_finiteScalarBins (show IsCompact (Icc (-((Q.count : ℝ) + 1)) 1) from
    isCompact_Icc) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  refine ⟨source, target, rankBins, K, hcode, hK, ?_⟩
  intro ambient density side hdensity origin S hS tilt
  have hs : Measurable source := measurable_of_countable _
  have ht : Measurable target := measurable_of_countable _
  have hk : Measurable (Function.uncurry (fun p : Fin Q.count × Fin Q.count ↦
      C.clockClassKinetic Q z₀ p.1 p.2)) := C.measurable_clockClassKinetic Q z₀
  have hp : Measurable (Function.uncurry (C.clockClassProbe Q z₀ hz₀ f)) :=
    C.measurable_clockClassProbe Q z₀ hz₀ f
  have hhom : ∀ j k (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      C.clockClassKinetic Q z₀ j k (fun l ↦ c * v l) =
        c ^ 2 * C.clockClassKinetic Q z₀ j k v :=
    fun j k c _ v ↦ C.clockClassKinetic_homogeneous Q z₀ j k c v
  have result := rankBins.integrable_density_affine_shapeBlockValue_compare
    (by norm_num : (0 : ℝ) < 1 / 2) q hq hs ht (α : Measure _) (β : Measure _)
    ambient density side hdensity origin hS
    (Filter.Eventually.of_forall hsource)
    (Filter.Eventually.of_forall (fun p ↦ hsep p.1 p.2)) hK (norm_nonneg f)
    hk (fun j k _ ↦ hbound j k) hhom hp
    (fun j k _ ↦ C.clockClassProbe_abs_le Q z₀ hz₀ f j k) tilt
  have hpressure := finiteClassLegalPressure_eq_clock q (C.clockClassAllowed Q) source target hcode
    (α : Measure _) (β : Measure _) (ambient * density * side ^ q)
    (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt
  have hkinScaled : C.densityClockClassKinetic Q z₀ (density : ℝ) =
      (fun j k v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * C.clockClassKinetic Q z₀ j k v) := by
    funext j k v
    simp only [OriginalPopulationCoefficientCore.densityClockClassKinetic, neg_div, q]
  dsimp only
  rw [hpressure, hkinScaled]
  exact result

end OTSelector.Reconstruction
