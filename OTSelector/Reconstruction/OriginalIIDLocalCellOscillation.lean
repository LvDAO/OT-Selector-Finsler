import OTSelector.Reconstruction.FinslerCoefficientCoreOscillation
import OTSelector.Reconstruction.FinslerOriginalCoordinateHaarPressure

/-! Actual compact original intensity and clock laws freeze in shrinking seed-coordinate cells. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

private theorem originalLocalCell_continuousOn_coordinateImage
    {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace T] {K : Set X} (hK : IsCompact K) {f : X → Y} {g : Y → T}
    (hf : ContinuousOn f K) (hinj : InjOn f K)
    (hg : ContinuousOn (g ∘ f) K) : ContinuousOn g (f '' K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he := (continuousOn_iff_continuous_domRestrict.mp hf).isClosedEmbedding
    (fun x y h ↦ Subtype.ext (hinj x.property y.property h))
  have himage : (fun z : K ↦ f z) '' univ = f '' K := by
    ext y
    simp
  rw [← himage]
  change ContinuousOn g (K.domRestrict f '' univ)
  exact he.isEmbedding.isInducing.continuousOn_image_iff.mpr
    (continuousOn_iff_continuous_domRestrict.mp hg).continuousOn

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Actual compact-core intensity and both clock laws freeze at every retained
reference root on bounded microscopic seed-coordinate windows. -/
theorem PopulationLocalPressureCore.original_cell_intensity_clock_oscillation
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count)
    {ref : ℚ → M} (href : ref ∈ (D.haar.continuous.coefficient i).roots)
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop) (B : ℝ) (hB : 0 < B) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ C.roots,
      ‖e (R z - R ref)‖ ≤ B / scale n →
        |D.rootIntensity i z - D.rootIntensity i ref| ≤ ε * D.rootIntensity i ref ∧
        ∀ color : Fin 2,
          ((populationTwoColorClockKernel u a η₀ η₁ color z).toSignedMeasure -
            (populationTwoColorClockKernel u a η₀ η₁ color ref).toSignedMeasure).totalVariation
              univ ≤ ENNReal.ofReal ε := by
  dsimp only
  let C := D.haar.continuous.coefficient i
  let I := D.haar.intensity i
  let pop := D.haar.continuous.population
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let coord := fun z ↦ e (R z)
  let recover := fun w ↦ a (S.curve (e.symm w) 0)
  have hI : I.roots = C.roots := D.haar.intensity_roots i
  have hsub : C.roots ⊆ pop.roots := fun z hz ↦
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
  have hlabel : ContinuousOn R C.roots := by
    rw [← hI]
    exact I.continuous_label
  have hcoord : ContinuousOn coord C.roots := e.continuous.comp_continuousOn hlabel
  have hrecover : ∀ z ∈ C.roots, recover (coord z) = z := by
    intro z hz
    simpa only [recover, coord, ContinuousLinearEquiv.symm_apply_apply] using
      I.root_identity z (hI.symm ▸ hz)
  have hinj : InjOn coord C.roots := by
    intro z hz z' hz' h
    exact (hrecover z hz).symm.trans ((congrArg recover h).trans (hrecover z' hz'))
  have hdensity : ContinuousOn (D.rootIntensity i) C.roots := by
    apply I.continuous_density.comp hlabel
    intro z hz
    exact mem_image_of_mem _ (hI.symm ▸ hz)
  let obs := fun z ↦ (D.rootIntensity i z, fun color ↦ pop.densityClass color z)
  have hobs : ContinuousOn obs C.roots :=
    hdensity.prodMk (pop.continuous_class.mono hsub)
  let obsCoord := obs ∘ recover
  have hobsCoord : ContinuousOn obsCoord (coord '' C.roots) := by
    apply originalLocalCell_continuousOn_coordinateImage C.roots_compact hcoord hinj
    apply hobs.congr
    intro z hz
    simp only [obsCoord, Function.comp_apply, hrecover z hz]
  have hrefcoord : coord ref ∈ coord '' C.roots := mem_image_of_mem coord href
  have hrefobs : obsCoord (coord ref) = obs ref := by
    simp only [obsCoord, Function.comp_apply, hrecover ref href]
  have hlo : I.lower ≤ D.rootIntensity i ref :=
    (I.bounds _ (mem_image_of_mem _ (hI.symm ▸ href))).1
  intro ε hε
  obtain ⟨radius, hradius, hsmall⟩ := Metric.continuousWithinAt_iff.mp
    (hobsCoord _ hrefcoord) (min (ε * I.lower) ε)
      (lt_min (mul_pos hε I.lower_pos) hε)
  have hshrink : Tendsto (fun n ↦ B / scale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hscale
  filter_upwards [hshrink.eventually (gt_mem_nhds hradius)] with n hn z hz hnear
  have hzobs : obsCoord (coord z) = obs z := by
    simp only [obsCoord, Function.comp_apply, hrecover z hz]
  have hdist : dist (coord z) (coord ref) < radius := by
    rw [dist_eq_norm]
    have hle : ‖coord z - coord ref‖ ≤ B / scale n := by
      simpa only [coord, ← map_sub] using hnear
    exact hle.trans_lt hn
  have hsmall := hsmall (mem_image_of_mem coord hz) hdist
  rw [hzobs, hrefobs, dist_eq_norm] at hsmall
  constructor
  · have hd := (norm_fst_le (obs z - obs ref)).trans_lt hsmall
    change ‖D.rootIntensity i z - D.rootIntensity i ref‖ < _ at hd
    rw [Real.norm_eq_abs] at hd
    exact hd.le.trans
      ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlo hε.le))
  · intro color
    rw [pop.variation color z (hsub hz) ref (hsub href)]
    apply ENNReal.ofReal_le_ofReal
    have hd := (norm_le_pi_norm (fun j ↦ pop.densityClass j z - pop.densityClass j ref) color).trans
      (norm_snd_le (obs z - obs ref))
    exact (hd.trans hsmall.le).trans (min_le_right _ _)

/-- Exact original native-Haar mass of the shrinking spatial ball, with the
mandatory Jacobian of the same actual finite seed basis. -/
theorem original_shrinking_seed_ball_haar_volume
    (S : F.CalibratedLevelSeedPatch u) (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure]
    (ref : S.covector.ker) {scale : ℝ} (hscale : 0 < scale) (B : ℝ) :
    let q := Module.finrank ℝ S.covector.ker
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    ENNReal.ofReal (scale ^ q) * κ {w | ‖e (w - ref)‖ ≤ B / scale} =
      (originalSeedCoordinateHaarFactor S κ : ℝ≥0∞) *
        (volume : Measure (Fin q → ℝ)) (Metric.closedBall 0 B) := by
  dsimp only
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let f := fun w ↦ scale • e w - scale • e ref
  have hf : Measurable f := by fun_prop
  have hball : MeasurableSet (Metric.closedBall (0 : Fin (finrank ℝ S.covector.ker) → ℝ) B) :=
    Metric.isClosed_closedBall.measurableSet
  have hset : f ⁻¹' Metric.closedBall 0 B = {w | ‖e (w - ref)‖ ≤ B / scale} := by
    ext w
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, mem_ofPred_eq]
    change ‖scale • e w - scale • e ref‖ ≤ B ↔ _
    rw [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hscale,
      le_div_iff₀ hscale]
    rw [mul_comm scale ‖e (w - ref)‖]
  have hm := scale_pow_smul_map_haar_scaled_seed_coordinate_sub κ e
    (map_originalSeedHaar_eq_coordinate_volume S κ) hscale (scale • e ref)
  have hv := congrArg (fun μ : Measure (Fin (finrank ℝ S.covector.ker) → ℝ) ↦
    μ (Metric.closedBall 0 B)) hm
  simp only [Measure.smul_apply, smul_eq_mul] at hv
  change ENNReal.ofReal (scale ^ finrank ℝ S.covector.ker) *
    (κ.map f) (Metric.closedBall 0 B) = _ at hv
  rw [Measure.map_apply hf hball, hset] at hv
  exact hv

/-- Every actual shrinking-cell subset has a scale-independent normalized real
native-Haar mass bound, preserving the original finite-basis Jacobian. -/
theorem original_shrinking_seed_ball_haar_volume_real_le
    (S : F.CalibratedLevelSeedPatch u) (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure]
    (ref : S.covector.ker) {scale : ℝ} (hscale : 0 < scale) (B : ℝ)
    {A : Set S.covector.ker}
    (hA : A ⊆ {w | ‖(Module.finBasis ℝ S.covector.ker).equivFunL (w - ref)‖ ≤ B / scale}) :
    scale ^ Module.finrank ℝ S.covector.ker * κ.real A ≤
      (originalSeedCoordinateHaarFactor S κ : ℝ) *
        (volume : Measure (Fin (Module.finrank ℝ S.covector.ker) → ℝ)).real
          (Metric.closedBall 0 B) := by
  have heq := original_shrinking_seed_ball_haar_volume S κ ref hscale B
  dsimp only at heq
  have hle := (mul_le_mul_right (measure_mono hA)
    (ENNReal.ofReal (scale ^ Module.finrank ℝ S.covector.ker))).trans_eq heq
  have hfinite : (originalSeedCoordinateHaarFactor S κ : ℝ≥0∞) *
      (volume : Measure (Fin (Module.finrank ℝ S.covector.ker) → ℝ))
        (Metric.closedBall 0 B) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top measure_closedBall_lt_top.ne
  have hreal := ENNReal.toReal_mono hfinite hle
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hscale.le _),
    ENNReal.coe_toReal, measureReal_def] using hreal

end OTSelector.Reconstruction
