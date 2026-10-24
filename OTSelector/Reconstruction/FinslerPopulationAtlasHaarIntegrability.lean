import OTSelector.Reconstruction.FinslerPopulationAtlasPressure
import OTSelector.Probability.DensityPressureIntegrability

/-! Actual original atlas integrability follows from its Haar representation.
The upper intensity bound is used against Haar measure; no global positive
lower bound or uniform population-integrand bound is introduced. -/
open Set Function MeasureTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
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
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- On any original seed part with finite Haar coordinate mass, an upper
intensity bound and the true linear local pressure growth give integrability
of the corrected population and Haar expressions, together with their original
population L1 bound. The only pressure regularity input is its own composed
Haar measurability; zero and arbitrarily small positive densities are allowed. -/
theorem integrable_populationAtlasIntegrand_of_haar_upper
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    [IsFiniteMeasure ((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K))]
    (I : Z → ℝ → ℝ) {q t U Cb G : ℝ} (hq : 2 < q)
    (hCb : 0 ≤ Cb) (hG : 0 ≤ G)
    (hupper : ∀ᵐ w ∂(κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K),
      (populationSeedPieceHaarDensity P a κ lambda j w).toReal ≤ U)
    (hread : AEStronglyMeasurable
      (fun w ↦ I (a ((P j).seed.curve w 0))
        (t * (populationSeedPieceHaarDensity P a κ lambda j w).toReal ^ (2 / q)))
      ((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)))
    (hgrowth : ∀ᵐ w ∂(κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K),
      ∀ v, |I (a ((P j).seed.curve w 0)) v| ≤ Cb + |v| * G) :
    IntegrableOn (populationAtlasIntegrand P a κ lambda I j q t) K lambda ∧
      IntegrableOn (populationAtlasCoordinateHaarIntegrand P a κ lambda I j q t)
        (populationSeedRootLabelValue (P j).seed a '' K) (κ j) ∧
      (∫ z in K, |populationAtlasIntegrand P a κ lambda I j q t z| ∂lambda) ≤
        (Cb * U ^ (1 - 2 / q) + |t| * G * U) *
          ((κ j) (populationSeedRootLabelValue (P j).seed a '' K)).toReal := by
  let r := populationSeedRootLabelValue (P j).seed a
  let d := populationSeedPieceHaarDensity P a κ lambda j
  let μH := (κ j).restrict (r '' K)
  let g := fun w ↦ (d w).toReal ^ (-2 / q) *
    I (a ((P j).seed.curve w 0)) (t * (d w).toReal ^ (2 / q))
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj
  have hd : Measurable d :=
    measurable_populationSeedPieceHaarDensity P a κ lambda hF hcomplete hu ha hinj j
  have hfinite := ae_populationSeedCore_haar_density_lt_top P a κ lambda
    hF hcomplete hu ha hinj j hK hsub
  have hmap := map_populationSeedCore_eq_withDensity P a κ lambda
    hF hcomplete hu ha hinj j hK hsub
  have hdata := OTSelector.Probability.integrable_density_pressure_of_upper_bound
    μH d hd.aemeasurable hfinite hq (fun w ↦ I (a ((P j).seed.curve w 0))) t
    hCb hG hupper hread hgrowth
  have hg : Integrable g ((lambda.restrict K).map r) := by
    rw [hmap]
    exact hdata.1
  have heq : (fun z ↦ populationAtlasIntegrand P a κ lambda I j q t z) =ᵐ[lambda.restrict K]
      g ∘ r := by
    filter_upwards [ae_restrict_mem hK] with z hz
    have hi : a ((P j).seed.curve (r z) 0) = z := by
      dsimp only [r]
      rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hsub hz⟩]
      exact populationSeedPieceLabel_root P a κ lambda j ⟨z, hsub hz⟩
    change (d (r z)).toReal ^ (-2 / q) * I z (t * (d (r z)).toReal ^ (2 / q)) =
      (d (r z)).toReal ^ (-2 / q) * I (a ((P j).seed.curve (r z) 0))
        (t * (d (r z)).toReal ^ (2 / q))
    rw [hi]
  refine ⟨(hg.comp_measurable hr).congr heq.symm, hdata.2.1, ?_⟩
  calc
    _ = ∫ z, |g (r z)| ∂lambda.restrict K := by
      apply integral_congr_ae
      exact heq.mono fun z hz ↦ congrArg abs hz
    _ = ∫ w, |g w| ∂((lambda.restrict K).map r) :=
      (integral_map hr.aemeasurable hg.abs.aestronglyMeasurable).symm
    _ = ∫ w, |g w| ∂μH.withDensity d := by rw [hmap]
    _ ≤ (Cb * U ^ (1 - 2 / q) + |t| * G * U) * μH.real univ := hdata.2.2
    _ = _ := by simp only [Measure.real, μH, Measure.restrict_apply_univ, r]

end OTSelector.Reconstruction
