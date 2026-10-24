import OTSelector.Reconstruction.FinslerPopulationSeedIntensityCore
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OTSelector.MeasureTheory.DensityPowerChangeOfMeasure

/-! The actual population root law and its original seed Haar reference
have different pressure weights. This module proves the exact measure change. -/
open Set Function MeasureTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  [IsFiniteMeasure lambda]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))

include hF hcomplete hu ha hinj

/-- The actual original root intensity is finite almost everywhere for the
original Haar measure of every retained coordinate image. This follows from
finite original population mass, without a lower density bound. -/
theorem ae_populationSeedCore_haar_density_lt_top
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j) :
    ∀ᵐ w ∂(κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K),
      populationSeedPieceHaarDensity P a κ lambda j w < ⊤ := by
  let r := populationSeedRootLabelValue (P j).seed a
  let d := populationSeedPieceHaarDensity P a κ lambda j
  let μH := (κ j).restrict (r '' K)
  have hd : Measurable d :=
    measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj j
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj
  have hmap := map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj j hK hsub
  have hmass : μH.withDensity d univ < ⊤ := by
    rw [← hmap,Measure.map_apply hr MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ]
    exact measure_lt_top lambda K
  have hmass' : (∫⁻ w, d w ∂μH) ≠ ⊤ := by
    have hh := hmass.ne
    rw [withDensity_apply d MeasurableSet.univ,Measure.restrict_univ] at hh
    exact hh
  exact ae_lt_top hd hmass'

/-- Signed integration against the actual original root law changes to the
original Haar coordinate image with exactly one density factor. The only
regularity input is ordinary measurability of the integrand for its own law. -/
theorem integral_populationSeedCore_eq_haar_weighted
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (g : (P j).seed.covector.ker → ℝ)
    (hg : AEStronglyMeasurable g
      ((lambda.restrict K).map (populationSeedRootLabelValue (P j).seed a))) :
    (∫ z in K, g (populationSeedRootLabelValue (P j).seed a z) ∂lambda) =
      ∫ w in populationSeedRootLabelValue (P j).seed a '' K,
        (populationSeedPieceHaarDensity P a κ lambda j w).toReal * g w ∂κ j := by
  let r := populationSeedRootLabelValue (P j).seed a
  let d := populationSeedPieceHaarDensity P a κ lambda j
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj
  have hd : Measurable d :=
    measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj j
  have hfinite := ae_populationSeedCore_haar_density_lt_top P a κ lambda hF hcomplete hu ha hinj j hK hsub
  have hmap := map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj j hK hsub
  calc
    _ = ∫ w, g w ∂((lambda.restrict K).map r) := (integral_map hr.aemeasurable hg).symm
    _ = ∫ w, g w ∂((κ j).restrict (r '' K)).withDensity d := by rw [hmap]
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul hd hfinite]
      rfl

/-- The actual original coordinate pressure has population exponent `-2/q`
and Haar exponent `1-2/q`. The change of measure produces the single density
factor internally and includes zero density. -/
theorem integral_populationSeedCore_pressure_eq_haar
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    {q : ℝ} (hq : 2 < q) (I : (P j).seed.covector.ker → ℝ → ℝ) (t : ℝ)
    (hI : AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        I w (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)))
      ((lambda.restrict K).map (populationSeedRootLabelValue (P j).seed a))) :
    (∫ z in K,
      (populationSeedPieceHaarDensity P a κ lambda j (populationSeedRootLabelValue (P j).seed a z)).toReal ^ (-2 / q) *
        I (populationSeedRootLabelValue (P j).seed a z)
          (t * (populationSeedPieceHaarDensity P a κ lambda j (populationSeedRootLabelValue (P j).seed a z)).toReal ^ (2 / q))
      ∂lambda) =
      ∫ w in populationSeedRootLabelValue (P j).seed a '' K,
        (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (1 - 2 / q) *
          I w (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)) ∂κ j := by
  let r := populationSeedRootLabelValue (P j).seed a
  let d := populationSeedPieceHaarDensity P a κ lambda j
  let g := fun w ↦ (d w).toReal ^ (-2 / q) * I w (t * (d w).toReal ^ (2 / q))
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj
  have hd : Measurable d :=
    measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj j
  have hfinite := ae_populationSeedCore_haar_density_lt_top P a κ lambda hF hcomplete hu ha hinj j hK hsub
  have hmap := map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj j hK hsub
  calc
    _ = ∫ w, g w ∂((lambda.restrict K).map r) := (integral_map hr.aemeasurable hI).symm
    _ = ∫ w, g w ∂((κ j).restrict (r '' K)).withDensity d := by rw [hmap]
    _ = _ := OTSelector.Probability.integral_withDensity_pressure_scale _ d hd.aemeasurable hfinite hq I t

/-- The same normalization identity in the original root labels. The seed
inverse is the original one, so the local pressure keeps its original root
argument; neither measure nor conditional clock law is replaced. -/
theorem integral_populationSeedCore_root_pressure_eq_haar
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    {q : ℝ} (hq : 2 < q) (I : Z → ℝ → ℝ) (t : ℝ)
    (hI : AEStronglyMeasurable
      (fun w ↦ (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (-2 / q) *
        I (a ((P j).seed.curve w 0))
          (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)))
      ((lambda.restrict K).map (populationSeedRootLabelValue (P j).seed a))) :
    (∫ z in K,
      (populationSeedPieceHaarDensity P a κ lambda j (populationSeedRootLabelValue (P j).seed a z)).toReal ^ (-2 / q) *
        I z (t * (populationSeedPieceHaarDensity P a κ lambda j (populationSeedRootLabelValue (P j).seed a z)).toReal ^ (2 / q))
      ∂lambda) =
      ∫ w in populationSeedRootLabelValue (P j).seed a '' K,
        (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (1 - 2 / q) *
          I (a ((P j).seed.curve w 0))
            (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)) ∂κ j := by
  have hinverse (z : Z) (hz : z ∈ K) :
      a ((P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) 0) = z := by
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z,hsub hz⟩]
    exact populationSeedPieceLabel_root P a κ lambda j ⟨z,hsub hz⟩
  calc
    _ = ∫ z in K,
      (populationSeedPieceHaarDensity P a κ lambda j (populationSeedRootLabelValue (P j).seed a z)).toReal ^ (-2 / q) *
        I (a ((P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) 0))
          (t * (populationSeedPieceHaarDensity P a κ lambda j (populationSeedRootLabelValue (P j).seed a z)).toReal ^ (2 / q))
      ∂lambda := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hK] with z hz
        rw [hinverse z hz]
    _ = _ := integral_populationSeedCore_pressure_eq_haar P a κ lambda hF hcomplete hu ha hinj j hK hsub hq
      (fun w ↦ I (a ((P j).seed.curve w 0))) t hI

end OTSelector.Reconstruction
