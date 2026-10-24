import OTSelector.Reconstruction.FinslerCoefficientCoreCoordinates
import OTSelector.Reconstruction.FinslerExpectedCoefficientFreezing
import OTSelector.Reconstruction.DistanceSlackSampling

/-!
# Original Finsler distance pressure with replacement only on core edges

The actual coordinate remainder and the same coefficient core produce a common
relative-error radius. Only selected edges use the frozen quadratic cost; every
other edge retains the original distance slack and the original probe.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ}
  {ε : ℝ}

namespace RelativeRootCover

/-- The original source-fixed distance cost is relatively close to every retained
reference coefficient, on one common coordinate radius. -/
def SourceRelativeBound (D : C.RelativeRootCover ε) (K : Set Z) (r : ℝ) : Prop :=
  let S := (P C.seedIndex).seed
  let w := populationSeedRootLabelValue S a
  let bW := Module.finBasis ℝ S.covector.ker
  ∀ z₀ ∈ D.centers, ∀ z ∈ K ∩ D.neighborhood z₀, ∀ p ∈ C.window.region,
    ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ, ‖v‖ < r →
      w z + bW.equivFun.symm v ∈ coefficientWindowLabels S C.window →
      |populationSeedPairDeficit S p (w z, w z + bW.equivFun.symm v) -
        matrixQuadratic (C.matrix z₀ p) v| ≤
          (2 * ε) * matrixQuadratic (C.matrix z₀ p) v

omit [BorelSpace E] in
/-- The produced coordinate remainder supplies the relative radius on the same
root set; no new root restriction or comparison coefficient is chosen. -/
theorem exists_source_relative_radius (D : C.RelativeRootCover ε) (hε : 0 < ε)
    {K : Set Z} (hK : K ⊆ C.roots)
    (hrem : ∀ η > 0, ∃ r > 0, ∀ z ∈ K, C.SourceCoordinateRemainderBound z η r) :
    ∃ r > 0, D.SourceRelativeBound K r := by
  obtain ⟨r, hr, hb⟩ := hrem (ε * D.lowerBound) (mul_pos hε D.lowerBound_pos)
  refine ⟨r, hr, ?_⟩
  intro z₀ hz₀ z hz p hp v hv hallowed
  exact D.relative_cost_of_quadratic_remainder hε.le hz₀ ⟨hK hz.1, hz.2⟩ hp v
    (hb z hz.1 p hp v hv hallowed)

omit [BorelSpace E] in
/-- Deterministic nonnegative pressure scaling preserves the actual relative
error, without changing the retained physical displacement. -/
theorem SourceRelativeBound.scaled {D : C.RelativeRootCover ε} {K : Set Z} {r : ℝ}
    (hb : D.SourceRelativeBound K r) {scale : ℝ} (hscale : 0 ≤ scale)
    {z₀ z : Z} (hz₀ : z₀ ∈ D.centers) (hz : z ∈ K ∩ D.neighborhood z₀)
    {p : ℝ × ℝ} (hp : p ∈ C.window.region)
    (v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (hv : ‖v‖ < r)
    (hallowed : populationSeedRootLabelValue (P C.seedIndex).seed a z +
      (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun.symm v ∈
        coefficientWindowLabels (P C.seedIndex).seed C.window) :
    let S := (P C.seedIndex).seed
    let w := populationSeedRootLabelValue S a z
    let bW := Module.finBasis ℝ S.covector.ker
    |scale * populationSeedPairDeficit S p (w, w + bW.equivFun.symm v) -
      scale * matrixQuadratic (C.matrix z₀ p) v| ≤
        (2 * ε) * (scale * matrixQuadratic (C.matrix z₀ p) v) := by
  dsimp only
  rw [← mul_sub, abs_mul, abs_of_nonneg hscale]
  calc
    _ ≤ scale * ((2 * ε) * matrixQuadratic (C.matrix z₀ p) v) :=
      mul_le_mul_of_nonneg_left (hb z₀ hz₀ z hz p hp v hv hallowed) hscale
    _ = _ := by ring

end RelativeRootCover

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]

/-- The actual geometric producer yields a large compact core, its finite relative
coefficient cover, and a common radius for the original distance cost. -/
theorem exists_source_relative_core [T2Space Z] [BorelSpace Z] [PolishSpace Z]
    [IsFiniteMeasure lambda] (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSpliceMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hε : 0 < ε)
    {loss : ℝ≥0∞} (hloss : loss ≠ 0) :
    ∃ D : C.RelativeRootCover ε, ∃ K ⊆ C.roots, IsCompact K ∧
      lambda (C.roots \ K) < loss ∧ ∃ r > 0, D.SourceRelativeBound K r := by
  obtain ⟨D⟩ := C.exists_relativeRootCover hε
  obtain ⟨K, hK, hcompact, hmass, _, hrem⟩ :=
    C.exists_uniform_source_coordinate_core hF hcomplete hu ha hinj hκ hloss
  obtain ⟨r, hr, hb⟩ := D.exists_source_relative_radius hε hK hrem
  exact ⟨D, K, hK, hcompact, hmass, r, hr, hb⟩

namespace RelativeRootCover

/-- Original compact-carrier samples admit the global spliced expected-pressure
comparison. Coordinate identities and geometric membership are needed only for
replaced edges; original edge integrability and nonnegativity are derived. -/
theorem expected_spliced_distance_pressure
    (D : C.RelativeRootCover ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSpliceMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {K : Set Z} {r : ℝ} (hrelative : D.SourceRelativeBound K r)
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} [IsProbabilityMeasure sample]
    {n : ℕ} (hn : 0 < n)
    (z₀ : Ω → Fin n → Fin n → Z)
    (hz₀ : ∀ i j, Measurable (fun ξ ↦ z₀ ξ i j))
    (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun ξ ↦ X ξ i))
    (hY : ∀ j, Measurable (fun ξ ↦ Y ξ j))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hXA : ∀ i, ∀ᵐ ξ ∂sample, X ξ i ∈ A)
    (hYB : ∀ j, ∀ᵐ ξ ∂sample, Y ξ j ∈ B)
    (Q : Ω → Set (Fin n × Fin n))
    (hQ : ∀ i j, MeasurableSet {ξ | (i, j) ∈ Q ξ})
    (z : Ω → Fin n → Fin n → Z)
    (p : Ω → Fin n → Fin n → ℝ × ℝ)
    (v : Ω → Fin n → Fin n → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (hp : ∀ i j, Measurable (fun ξ ↦ p ξ i j))
    (hv : ∀ i j, Measurable (fun ξ ↦ v ξ i j))
    (hlocal : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ →
      let S := (P C.seedIndex).seed
      let w := populationSeedRootLabelValue S a (z ξ i j)
      let bW := Module.finBasis ℝ S.covector.ker
      z₀ ξ i j ∈ D.centers ∧ z ξ i j ∈ K ∩ D.neighborhood (z₀ ξ i j) ∧ p ξ i j ∈ C.window.region ∧
        ‖v ξ i j‖ < r ∧ w + bW.equivFun.symm (v ξ i j) ∈
          coefficientWindowLabels S C.window ∧
        X ξ i = S.curve w ((p ξ i j).1 - S.level) ∧
        Y ξ j = S.curve (w + bW.equivFun.symm (v ξ i j)) ((p ξ i j).2 - S.level))
    (g h : Ω → Matrix (Fin n) (Fin n) ℝ) (t G probeError scale : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : 2 * ε < 1) (hscale : 0 ≤ scale) (hprobe : 0 ≤ probeError)
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hh : ∀ i j, Measurable (fun ξ ↦ h ξ i j))
    (hgb : ∀ᵐ ξ ∂sample, ∀ i j, |g ξ i j| ≤ G)
    (hhb : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ → |h ξ i j| ≤ G)
    (hgh : ∀ᵐ ξ ∂sample, ∀ i j, (i, j) ∈ Q ξ → |g ξ i j - h ξ i j| ≤ probeError) :
    let c := fun ξ i j ↦ scale *
      ((F.lengthEDist (X ξ i) (Y ξ j)).toReal - u (Y ξ j) + u (X ξ i))
    let d := fun ξ i j ↦ scale * matrixQuadratic (C.matrix (z₀ ξ i j) (p ξ i j)) (v ξ i j)
    let dQ := fun ξ ↦ spliceEdgeCost (Q ξ) (c ξ) (d ξ)
    let hQ := fun ξ ↦ spliceEdgeCost (Q ξ) (g ξ) (h ξ)
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / n) sample ∧
      Integrable (fun ξ ↦ perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n) sample ∧
      |(∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / n ∂sample) -
        ∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂sample| ≤
      (2 * ε) * ((∫ ξ, perturbedAssignmentValue (dQ ξ) (hQ ξ) t / n ∂sample) +
        |t| * G) + |t| * probeError := by
  let _instSpliceMetric : MetricSpace M := F.metricSpace
  let _instSpliceProper : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨hcm, hci, hcn⟩ := scaled_distanceSlack_sampling_data X Y u hu hX hY
    hA hB hXA hYB hscale
  have hdm (i j : Fin n) : Measurable (fun ξ ↦
      scale * matrixQuadratic (C.matrix (z₀ ξ i j) (p ξ i j)) (v ξ i j)) :=
    (C.measurable_quadratic_cost hF hcomplete hu ha hinj (hz₀ i j)
      (hp i j) (hv i j)).const_mul scale
  apply expected_spliced_perturbedAssignmentValue_div_abs_sub_le hn Q
    (fun ξ i j ↦ scale * distanceSlackEdgeCost (X ξ) (Y ξ) u i j) g
    (fun ξ i j ↦ scale * matrixQuadratic (C.matrix (z₀ ξ i j) (p ξ i j)) (v ξ i j)) h
    t (2 * ε) G probeError (mul_nonneg (by norm_num) hε0) hε1 hprobe
    hQ hcm hg hdm hh hci (Filter.Eventually.of_forall hcn) _ hgb hhb hgh
  filter_upwards [hlocal] with ξ hlocalξ
  intro i j hij
  obtain ⟨hcenter, hz, hpair, hsmall, hallowed, hsource, htarget⟩ := hlocalξ i j hij
  have hb := hrelative.scaled hscale hcenter hz hpair (v ξ i j) hsmall hallowed
  simpa only [distanceSlackEdgeCost, F.metricSpace_dist, hsource, htarget,
    populationSeedPairDeficit] using hb

end RelativeRootCover
end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
