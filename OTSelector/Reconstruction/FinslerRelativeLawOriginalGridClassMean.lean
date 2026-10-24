import OTSelector.Reconstruction.FinslerRelativeLawOriginalGridCubeSum
import OTSelector.Reconstruction.FinslerRelativeLawBinomialDensityMean

/-! The literal mask-valued original binomial grid mean has no clock-coding dependence. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry BoxIntegral
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators
  BoundedContinuousFunction Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

theorem positiveMicroscopicGrid_mass_le {q : ℕ} (hq : 0 < q) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (N : ℝ) * positiveMicroscopicGridSide q L N ^ q ≤ L ^ q := by
  by_cases hN : N = 0
  · subst N
    simp only [Nat.cast_zero, zero_mul]
    exact pow_nonneg hL.le q
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hside : positiveMicroscopicGridSide q L N = microscopicGridSide q L N := by
      unfold positiveMicroscopicGridSide microscopicGridSide
      rw [positiveMicroscopicGridOrder_eq_of_pos q hL hNpos]
    rw [hside]
    exact microscopicGrid_mass_le hq hL (Nat.cast_pos.mpr hNpos)

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The exact original finite-class binomial reference mean has the same
normalized grid sum limit, on its literal mask and actual P0 marginals. The
internal strict-clock encoding is eliminated from the conclusion. -/
theorem OriginalPopulationCoefficientCore.tendstoUniformlyOn_original_grid_classMean_error
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker)
    (density : ℝ≥0) (hdensity : 0 < density) {L : ℝ} (hL : 0 < L)
    (s : Set (Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    (hs : volume s ≠ (⊤ : ℝ≥0∞))
    (cells : ℕ → Finset (Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℤ))
    (hadded : Tendsto (fun N ↦ volume ((⋃ ν ∈ cells N,
      (unitPartition.box (positiveMicroscopicGridOrder
        (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) L N) ν : Set _)) \ s)) atTop (𝓝 0))
    {T : Set ℝ} (hT : IsCompact T) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
      ((cells N).card : ℝ) *
        (∫ cloud : TwoMarkedCloudSpace q (Fin Q.count) (Fin Q.count),
          finiteClassLegalTilted q (C.clockClassAllowed Q)
            ((N : ℝ) * density * positiveMicroscopicGridSide q L N ^ q)
            (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt cloud
          ∂twoMarkedCountLaw q (α : Measure _) (β : Measure _)
            (ProbabilityTheory.binomial N (positiveMicroscopicCubeProbability q density L N))) / (N : ℝ) -
      volume.real (⋃ ν ∈ cells N,
        (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) *
        (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
          (density * ⟨L ^ q, pow_nonneg hL.le q⟩) (C.densityClockClassKinetic Q z₀ density)
          (C.clockClassProbe Q z₀ hz₀ f) tilt / L ^ q)) (fun _ ↦ 0) atTop T := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, hsum⟩ :=
    C.exists_original_grid_fullCube_sum_error_tendstoUniformlyOn Q z₀ hz₀ f P₀ hP₀ hmass hq
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  let model := fun N tilt ↦
    ∫ cloud : TwoMarkedCloudSpace q (Fin Q.count) (Fin Q.count),
      finiteClassLegalTilted q (C.clockClassAllowed Q)
        ((N : ℝ) * density * positiveMicroscopicGridSide q L N ^ q)
        (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt cloud
      ∂twoMarkedCountLaw q (α : Measure _) (β : Measure _)
        (ProbabilityTheory.binomial N (positiveMicroscopicCubeProbability q density L N))
  have hkinEq : C.densityClockClassKinetic Q z₀ density =
      (fun j k v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * C.clockClassKinetic Q z₀ j k v) := by
    funext j k v
    simp only [OriginalPopulationCoefficientCore.densityClockClassKinetic, neg_div, q]
  have hmean (N : ℕ) (origin : Fin q → ℝ) (tilt : ℝ) :
      affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
        (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N) origin
        (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt = model N tilt := by
    rw [affineBinomialCubeExpectation_eq_density_count_model
      (kin := C.clockClassKinetic Q z₀) (probe := C.clockClassProbe Q z₀ hz₀ f)
      (density := (density : ℝ)) q hq
      (measurable_of_countable source) (measurable_of_countable target) (α : Measure _) (β : Measure _)
      N _ (by exact_mod_cast hdensity) (positiveMicroscopicGridSide_nonneg q L N) origin
      hK (norm_nonneg f) (C.measurable_clockClassKinetic Q z₀) hbound
      (fun j k c _ v ↦ C.clockClassKinetic_homogeneous Q z₀ j k c v)
      (C.measurable_clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f) tilt]
    dsimp only [model]
    rw [hkinEq]
    exact integral_congr_ae (.of_forall fun cloud ↦
      (finiteClassLegalTilted_eq_clock q _ source target hcode _ _ _ _ cloud).symm)
  have hresult := hsum density hdensity L hL s hs cells hadded T hT
  apply hresult.congr
  filter_upwards [] with N
  intro tilt _
  have heq : (∑ ν ∈ cells N, affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
      (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N)
      (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N)
      (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) =
      ((cells N).card : ℝ) * model N tilt := by
    simp_rw [hmean]
    simp only [Finset.sum_const, nsmul_eq_mul]
  exact congrArg (fun value : ℝ ↦ value / (N : ℝ) -
    volume.real (⋃ ν ∈ cells N, (unitPartition.box (positiveMicroscopicGridOrder q L N) ν : Set (Fin q → ℝ))) *
      (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
        (density * ⟨L ^ q, pow_nonneg hL.le q⟩) (C.densityClockClassKinetic Q z₀ density)
        (C.clockClassProbe Q z₀ hz₀ f) tilt / L ^ q)) heq

end OTSelector.Reconstruction
