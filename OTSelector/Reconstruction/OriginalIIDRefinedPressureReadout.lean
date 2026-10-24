import OTSelector.Reconstruction.OriginalIIDUniformResidualUpperClosure
import OTSelector.Reconstruction.FinslerOriginalClosedWindowPressureCutoffs
import OTSelector.Reconstruction.FinslerOriginalClosedWindowPhysicalIntensity
import OTSelector.Reconstruction.FinslerOriginalFullClockResamplingData
import OTSelector.Reconstruction.FinslerOriginalClosedWindowClassPressure
import OTSelector.Reconstruction.FinslerOriginalClosedWindowRangePressure

/-!
# Original refined pressure readout on the same empirical upper cores

The original accuracy family is restricted along one deterministic dyadic subsequence.
This makes its actual root losses summable without replacing the original cores, laws,
atlas constants, optimizers or pressure models. Exact coordinate weights are kept.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- One deterministic subsequence of the already produced upper cores. -/
def originalUpperReadoutRefinement (n : ℕ) : ℕ := 2 ^ n

/-- Every later readout still uses one common increasing original refinement index. -/
theorem strictMono_originalUpperReadoutRefinement : StrictMono originalUpperReadoutRefinement :=
  pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)

/-- The same actual root-loss budget becomes summable along this fixed subsequence. -/
theorem summable_originalUpperReadoutAccuracy :
    Summable (fun n ↦ originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)) := by
  apply Summable.of_nonneg_of_le (fun n ↦
    (originalUpperRefinementAccuracy_pos_lt_one _).1.le) _ summable_geometric_two
  intro n
  unfold originalUpperRefinementAccuracy originalUpperReadoutRefinement
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  calc
    1 / ((2 ^ n : ℕ) + 2 : ℝ) ≤ 1 / ((2 : ℝ) ^ n) := by
      push_cast
      exact one_div_le_one_div_of_le hp (by linarith)
    _ = ((1 : ℝ) / 2) ^ n := by rw [div_pow, one_pow]

/-- The empirical upper's original root losses now satisfy the exact finite-sum
hypothesis of the actual closed-window pressure recovery theorem. -/
theorem tsum_originalUpperReadoutLoss_ne_top :
    (∑' n, ENNReal.ofReal
      (originalUpperRefinementAccuracy (originalUpperReadoutRefinement n))) ≠ ⊤ :=
  summable_originalUpperReadoutAccuracy.tsum_ofReal_ne_top

/-- Accuracy still tends to zero on the same original refinement subsequence. -/
theorem tendsto_originalUpperReadoutAccuracy :
    Tendsto (fun n ↦ originalUpperRefinementAccuracy (originalUpperReadoutRefinement n))
      atTop (𝓝 0) :=
  tendsto_originalUpperRefinementAccuracy.comp strictMono_originalUpperReadoutRefinement.tendsto_atTop

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {range : Set ℝ}

/-- Closed-window kernels on the already constructed upper cores recover the
original clock law in mass along the same deterministic subsequence. -/
theorem original_upper_readout_closed_window_mass_recovery
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ} (hgap : 0 ≤ gap)
    (D : ∀ k, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r
      (ENNReal.ofReal (originalUpperRefinementAccuracy k))
      (ENNReal.ofReal (originalUpperRefinementAccuracy k)))
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) :
    let χ := fun n ↦ (D (originalUpperReadoutRefinement n)).originalClosedWindowPairKernel
      hcomplete γ
    (∀ n z, χ n z ≤ γ z) ∧
      ∀ᵐ z ∂μ.map a, Tendsto (fun n ↦ (χ n z).real univ) atTop (𝓝 1) := by
  exact originalClosedWindowPairKernel_ae_mass_recovery γ gap hgap (fun _ ↦ r)
    (fun n ↦ ENNReal.ofReal (originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)))
    (fun n ↦ ENNReal.ofReal (originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)))
    (fun n ↦ D (originalUpperReadoutRefinement n)) hcomplete
    (fun _ ↦ ENNReal.ofReal_ne_top)
    (by simpa only [ENNReal.toReal_ofReal (originalUpperRefinementAccuracy_pos_lt_one _).1.le] using tendsto_originalUpperReadoutAccuracy)
    tsum_originalUpperReadoutLoss_ne_top

/-- The actual clock-law hypotheses are recovered from the same summably retained
cores themselves; they are not an extra conditional-coupling callback. -/
theorem ae_original_upper_readout_clock_pair_good
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) {gap : ℝ}
    (D : ∀ k, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r
      (ENNReal.ofReal (originalUpperRefinementAccuracy k))
      (ENNReal.ofReal (originalUpperRefinementAccuracy k))) :
    ∀ᵐ z ∂μ.map a,
      originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range z := by
  have hsum : (∑' n, (μ.map a)
      ((D (originalUpperReadoutRefinement n)).haar.continuous.population.roots)ᶜ) ≠ ⊤ :=
    ne_top_of_le_ne_top tsum_originalUpperReadoutLoss_ne_top
      (ENNReal.tsum_le_tsum fun n ↦
        (D (originalUpperReadoutRefinement n)).haar.continuous.population.complement_small.le)
  filter_upwards [ae_eventually_notMem hsum] with z hz
  obtain ⟨n, hn⟩ := hz.exists
  have hzin : z ∈ (D (originalUpperReadoutRefinement n)).haar.continuous.population.roots := by
    simpa only [mem_compl_iff, not_not] using hn
  exact ((D (originalUpperReadoutRefinement n)).haar.continuous.population.good z hzin).1

/-- The same upper cores give actual retained pressure integrals bounded by the
canonical original root-pressure integral, after one deterministic root cutoff.
Zero retained masses and the original Haar density factors remain allowed. -/
theorem eventually_original_upper_readout_pressure_integral
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hdim : 6 ≤ finrank ℝ E)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ]
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hb : Measurable b)
    (D : ∀ k, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r
      (ENNReal.ofReal (originalUpperRefinementAccuracy k))
      (ENNReal.ofReal (originalUpperRefinementAccuracy k)))
    (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0)
      (μ.map a)) (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    let χ := fun n ↦ (D (originalUpperReadoutRefinement n)).originalClosedWindowPairKernel
      hcomplete γ
    ∀ᶠ n in atTop, ∃ K : Set (ℚ → M), MeasurableSet K ∧
      K ⊆ (D (originalUpperReadoutRefinement n)).haar.continuous.population.roots ∧
      (μ.map a).real Kᶜ < budget +
        originalUpperRefinementAccuracy (originalUpperReadoutRefinement n) ∧
      IntegrableOn (originalRetainedFinslerRootPressure P a κ (μ.map a) χ
        (fun n _ ↦ originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)) b f n t)
        K (μ.map a) ∧
      (∫ z in K, originalRetainedFinslerRootPressure P a κ (μ.map a) χ
        (fun n _ ↦ originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)) b f n t z
        ∂μ.map a) <
      (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t z ∂μ.map a) +
        tolerance := by
  have hgood := ae_original_upper_readout_clock_pair_good γ D
  have hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z)
      (condDistrib u a μ z) (condDistrib u a ν z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2 :=
    hgood.mono fun _ h ↦ ⟨h.1, h.2.1.mono fun _ hp ↦ sub_nonneg.mp (hgap.le.trans hp)⟩
  simpa only [ENNReal.toReal_ofReal (originalUpperRefinementAccuracy_pos_lt_one _).1.le] using
    eventually_exists_originalClosedWindow_global_pressure_cutoff_on_core hlaw hF hcomplete hu
      ha hinj hdim γ hγ hgap hsep hb (fun _ ↦ r)
      (fun n ↦ ENNReal.ofReal (originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)))
      (fun n ↦ ENNReal.ofReal (originalUpperRefinementAccuracy (originalUpperReadoutRefinement n)))
      (fun n ↦ D (originalUpperReadoutRefinement n))
      (fun _ ↦ ENNReal.ofReal_ne_top)
      (by simpa only [ENNReal.toReal_ofReal (originalUpperRefinementAccuracy_pos_lt_one _).1.le]
        using tendsto_originalUpperReadoutAccuracy)
      tsum_originalUpperReadoutLoss_ne_top
      (fun n ↦ originalUpperRefinementAccuracy (originalUpperReadoutRefinement n))
      tendsto_originalUpperReadoutAccuracy
      (fun _ ↦ ⟨(originalUpperRefinementAccuracy_pos_lt_one _).1.le,
        (originalUpperRefinementAccuracy_pos_lt_one _).2.le⟩)
      f hp0 t budget tolerance hbudget htolerance

/-- Coordinate volume on each actual retained original cell equals its inverse
coordinate-intensity integral against the unchanged original root measure.
The positive lower bound is supplied by this retained core itself. -/
theorem PopulationLocalPressureCore.integral_inverse_coordinate_intensity_eq_volume
    {Good : (ℚ → M) → Prop} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {K : Set (ℚ → M)}
    (hK : MeasurableSet K) (hsub : K ⊆ (D.haar.continuous.coefficient i).roots) :
    (∫ z in K, (originalSeedCoordinateIntensity P a κ (μ.map a)
      (D.haar.continuous.coefficient i).seedIndex z)⁻¹ ∂μ.map a) =
    volume.real ((atlasSeedCoord (P (D.haar.continuous.coefficient i).seedIndex).seed
      (finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL a) '' K) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let rr := populationSeedRootLabelValue S a
  let d := populationSeedPieceHaarDensity P a κ (μ.map a) C.seedIndex
  let e := (finBasis ℝ S.covector.ker).equivFunL
  let c : ℝ := originalSeedCoordinateHaarFactor S (κ C.seedIndex)
  let f : S.labels → (ℚ → M) := fun w ↦ a (S.curve w 0)
  have hf : MeasurableEmbedding f :=
    measurableEmbedding_populationSeedLabel S hF hcomplete hu ha hinj
  have hv := MeasurableEmbedding.subtype_coe S.labels_measurable
  have hr : Measurable rr := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  have hd : Measurable d :=
    measurable_populationSeedPieceHaarDensity P a κ (μ.map a) hF hcomplete hu ha hinj C.seedIndex
  have hpiece : K ⊆ populationSeedRootPiece P a κ (μ.map a) C.seedIndex :=
    fun z hz ↦ C.roots_subset_piece (hsub hz)
  have hinverse (w : S.labels) : rr (f w) = w.val :=
    populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj w
  have himage : rr '' K = ((↑) : S.labels → S.covector.ker) '' (f ⁻¹' K) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      let v := populationSeedPieceLabel P a κ (μ.map a) C.seedIndex ⟨z, hpiece hz⟩
      have hvroot : f v = z :=
        populationSeedPieceLabel_root P a κ (μ.map a) C.seedIndex ⟨z, hpiece hz⟩
      exact ⟨v, by simpa only [mem_preimage, hvroot] using hz,
        (hinverse v).symm.trans (congrArg rr hvroot)⟩
    · rintro ⟨v, hvK, rfl⟩
      exact ⟨f v, hvK, hinverse v⟩
  have hKr : MeasurableSet (rr '' K) := by
    rw [himage]
    exact hv.measurableSet_image.mpr (hf.measurable hK)
  have hpos (w : S.covector.ker) (hw : w ∈ rr '' K) : 0 < (d w).toReal := by
    obtain ⟨z, hz, rfl⟩ := hw
    have hzI : z ∈ (D.haar.intensity i).roots := by
      rw [D.haar.intensity_roots]
      exact hsub hz
    exact (D.haar.intensity i).lower_pos.trans_le
      ((D.haar.intensity i).bounds _ (mem_image_of_mem _ hzI)).1
  have hfinite : ∀ᵐ w ∂(κ C.seedIndex).restrict (rr '' K), d w < ⊤ := by
    filter_upwards [ae_restrict_mem hKr] with w hw
    exact (ENNReal.toReal_pos_iff.mp (hpos w hw)).2
  have hmap := map_populationSeedCore_eq_withDensity P a κ (μ.map a) hF hcomplete hu ha hinj
    C.seedIndex hK hpiece
  have hintegral : (∫ z in K, (d (rr z)).toReal⁻¹ ∂μ.map a) =
      (κ C.seedIndex).real (rr '' K) := by
    calc
      _ = ∫ w, (d w).toReal⁻¹ ∂((μ.map a).restrict K).map rr :=
        (integral_map hr.aemeasurable hd.ennreal_toReal.inv.aestronglyMeasurable).symm
      _ = ∫ w, (d w).toReal⁻¹ ∂((κ C.seedIndex).restrict (rr '' K)).withDensity d := by
        rw [hmap]
      _ = ∫ w in rr '' K, (1 : ℝ) ∂κ C.seedIndex := by
        rw [integral_withDensity_eq_integral_toReal_smul hd hfinite]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hKr] with w hw
        exact mul_inv_cancel₀ (hpos w hw).ne'
      _ = _ := by simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
        Measure.restrict_apply_univ]
  have hcoord : atlasSeedCoord S e a '' K = e '' (rr '' K) := by
    rw [image_image]
    rfl
  have hcoordM : MeasurableSet (atlasSeedCoord S e a '' K) := by
    rw [hcoord]
    exact e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hKr
  have hpre : e ⁻¹' (atlasSeedCoord S e a '' K) = rr '' K := by
    rw [hcoord, e.injective.preimage_image]
  have hHaar := map_originalSeedHaar_eq_coordinate_volume S (κ C.seedIndex)
  have hκ : (κ C.seedIndex).real (rr '' K) = c * volume.real (atlasSeedCoord S e a '' K) := by
    have hh := map_measureReal_apply (μ := κ C.seedIndex) e.continuous.measurable hcoordM
    rw [hpre, hHaar] at hh
    simpa only [measureReal_ennreal_smul_apply, ENNReal.coe_toReal] using hh.symm
  have hcpos : 0 < c := by
    exact_mod_cast originalSeedCoordinateHaarFactor_pos S (κ C.seedIndex)
  have hc : c ≠ 0 := hcpos.ne'
  change (∫ z in K, (c * (d (rr z)).toReal)⁻¹ ∂μ.map a) =
    volume.real (atlasSeedCoord S e a '' K)
  simp_rw [mul_inv_rev, mul_comm _ c⁻¹]
  rw [integral_const_mul, hintegral, hκ]
  exact inv_mul_cancel_left₀ hc _

/-- The actual inverse coordinate intensity is integrable on every measurable
part of a retained original core. No global positive-density condition is used. -/
theorem PopulationLocalPressureCore.integrableOn_inverse_coordinate_intensity
    {Good : (ℚ → M) → Prop} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {K : Set (ℚ → M)}
    (hK : MeasurableSet K) (hsub : K ⊆ (D.haar.continuous.coefficient i).roots) :
    IntegrableOn (fun z ↦ (originalSeedCoordinateIntensity P a κ (μ.map a)
      (D.haar.continuous.coefficient i).seedIndex z)⁻¹) K (μ.map a) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let c : ℝ := originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex)
  let lower := c * (D.haar.intensity i).lower
  have hc : 0 < c := by
    exact_mod_cast originalSeedCoordinateHaarFactor_pos (P C.seedIndex).seed (κ C.seedIndex)
  have hlower : 0 < lower := mul_pos hc (D.haar.intensity i).lower_pos
  have hm : Measurable (fun z ↦ originalSeedCoordinateIntensity P a κ (μ.map a)
      C.seedIndex z) := by
    exact (measurable_actual_populationAtlasTheta hF hcomplete hu ha hinj C.seedIndex).const_mul c
  apply (integrable_const (lower⁻¹ : ℝ)).mono' hm.inv.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hK] with z hz
  have hzI : z ∈ (D.haar.intensity i).roots := by
    rw [D.haar.intensity_roots]
    exact hsub hz
  have hb := ((D.haar.intensity i).bounds _ (mem_image_of_mem _ hzI)).1
  have hbound : lower ≤ originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z :=
    mul_le_mul_of_nonneg_left hb hc.le
  have hθpos := hlower.trans_le hbound
  change ‖(originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z)⁻¹‖ ≤ lower⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθpos)]
  simpa only [one_div] using one_div_le_one_div_of_le hlower hbound

/-- A literal frozen cell contribution is exactly an original-root integral,
with the coordinate intensity in the denominator and both retained density
powers unchanged. -/
theorem PopulationLocalPressureCore.original_frozen_cell_pressure_eq_root_integral
    {Good : (ℚ → M) → Prop} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {K : Set (ℚ → M)}
    (hK : MeasurableSet K) (hsub : K ⊆ (D.haar.continuous.coefficient i).roots)
    (density : ℝ≥0) (p : ℝ → ℝ) (tilt : ℝ) :
    let q := finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker
    let coord := atlasSeedCoord (P (D.haar.continuous.coefficient i).seedIndex).seed
      (finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL a
    volume.real (coord '' K) * (density : ℝ) ^ (1 - 2 / (q : ℝ)) *
      p (tilt * (density : ℝ) ^ (2 / (q : ℝ))) =
    ∫ z in K, (originalSeedCoordinateIntensity P a κ (μ.map a)
      (D.haar.continuous.coefficient i).seedIndex z)⁻¹ *
      (density : ℝ) ^ (1 - 2 / (q : ℝ)) * p (tilt * (density : ℝ) ^ (2 / (q : ℝ)))
      ∂μ.map a := by
  intro q coord
  rw [integral_mul_const, integral_mul_const,
    D.integral_inverse_coordinate_intensity_eq_volume hF hcomplete hu ha hinj i hK hsub]

/-- The actual entire finite-family leading term has its exact original-root
integral representation. In particular, the original Haar factor is never
replaced by one and retained density can be zero. -/
theorem PopulationLocalPressureCore.original_frozen_family_pressure_eq_root_integral
    {Good : (ℚ → M) → Prop} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {Cell : Type*} [Fintype Cell] (coreIndex : Cell → Fin D.haar.continuous.count)
    (cell : Cell → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots)
    (density : Cell → ℝ≥0) (p : Cell → ℝ → ℝ) (tilt : ℝ) :
    let q := fun c ↦ finrank ℝ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker
    let coord := fun c ↦ atlasSeedCoord (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed
      (finBasis ℝ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker).equivFunL a
    (∑ c, volume.real (coord c '' cell c) * (density c : ℝ) ^ (1 - 2 / (q c : ℝ)) *
      p c (tilt * (density c : ℝ) ^ (2 / (q c : ℝ)))) =
    ∫ z, ∑ c, (cell c).indicator (fun w ↦
      (originalSeedCoordinateIntensity P a κ (μ.map a)
        (D.haar.continuous.coefficient (coreIndex c)).seedIndex w)⁻¹ *
      (density c : ℝ) ^ (1 - 2 / (q c : ℝ)) * p c (tilt * (density c : ℝ) ^ (2 / (q c : ℝ)))) z
      ∂μ.map a := by
  intro q coord
  have hI (c : Cell) : Integrable ((cell c).indicator (fun w ↦
      (originalSeedCoordinateIntensity P a κ (μ.map a)
        (D.haar.continuous.coefficient (coreIndex c)).seedIndex w)⁻¹ *
      (density c : ℝ) ^ (1 - 2 / (q c : ℝ)) * p c (tilt * (density c : ℝ) ^ (2 / (q c : ℝ)))))
      (μ.map a) := by
    apply (integrable_indicator_iff (hcell c)).2
    exact ((D.integrableOn_inverse_coordinate_intensity hF hcomplete hu ha hinj
      (coreIndex c) (hcell c) (hsub c)).mul_const _).mul_const _
  rw [integral_finsetSum Finset.univ (fun c _ ↦ hI c)]
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_indicator (hcell c)]
  exact D.original_frozen_cell_pressure_eq_root_integral hF hcomplete hu ha hinj
    (coreIndex c) (hcell c) (hsub c) (density c) (p c) tilt

/-- The SAME original fine bins supply both the genuine physical assignment geometry
and the actual continuous-clock pressure resampling certificate. All are selected
before finite root cells or empirical samples. -/
theorem PopulationLocalPressureCore.exists_original_clockClass_geometry_with_resampling
    {Good : (ℚ → M) → Prop} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε probeError : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hprobeError : 0 < probeError) :
    let C := D.haar.continuous.coefficient i
    ∃ (Q : C.roots → FiniteScalarBins I globalGap) (U : C.roots → Set (ℚ → M)),
      (∀ z₀, Nonempty (OriginalRangeClockResamplingData C (Q z₀)
        z₀.val z₀.property f ε probeError)) ∧
      (∀ z₀ j k, C.clockClassAllowed (Q z₀) j k →
        ∀ s ∈ (Q z₀).cell j, ∀ t ∈ (Q z₀).cell k,
          s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ s < t) ∧
      (∀ z₀, IsOpen (U z₀) ∧ z₀.val ∈ U z₀) ∧
      (∀ z₀ j k, C.clockClassAllowed (Q z₀) j k →
        ∀ s ∈ (Q z₀).cell j, ∀ t ∈ (Q z₀).cell k,
          s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1) ∧
      (∀ z₀, ∀ z ∈ C.roots ∩ U z₀, ∀ z' ∈ C.roots ∩ U z₀,
        ∀ s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
        ∀ t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
          s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
          (s, t) ∈ C.window.region) ∧
      ∀ z₀, ∀ z ∈ C.roots ∩ U z₀, ∀ z' ∈ C.roots ∩ U z₀,
      ∀ j k, C.clockClassAllowed (Q z₀) j k → ∀ s ∈ (Q z₀).cell j,
      ∀ t ∈ (Q z₀).cell k,
      D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        let S := (P C.seedIndex).seed
        let R := populationSeedRootLabelValue S a
        let v := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
        (s, t) ∈ C.window.region ∧
        |populationSeedPairDeficit S (s, t) (R z, R z') -
          C.clockClassKinetic (Q z₀) z₀.val j k v| ≤
            (3 * ε + 2 * ε ^ 2) * C.clockClassKinetic (Q z₀) z₀.val j k v ∧
        |f (D.corePoint i (z, s), D.corePoint i (z', t)) -
          C.clockClassProbe (Q z₀) z₀.val z₀.property f j k| ≤ 2 * probeError := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  obtain ⟨radius, hradius, hregion⟩ := D.exists_original_clock_region_radius hF i hgap hsep hscreen
  obtain ⟨U, hU, hgeometry⟩ := D.exists_original_pair_geometry_neighborhoods hF hcomplete hu ha hinj
    i f f.continuous hε hprobeError hradius
  choose Q hRdata hfull using fun z₀ : C.roots ↦
    C.exists_original_full_clock_resampling_data hF hcomplete hu ha hinj z₀.val z₀.property
      f hI hglobalGap hε hε1 hprobeError
  have hQ (z₀ : C.roots) (j k : Fin (Q z₀).count)
      (hjk : C.clockClassAllowed (Q z₀) j k) (s : ℝ) (hs : s ∈ (Q z₀).cell j)
      (t : ℝ) (ht : t ∈ (Q z₀).cell k) :
      s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
      t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ True ∧ s < t ∧
      (∀ v, |matrixQuadratic (C.matrix z₀.val (s,t)) v -
        C.clockClassKinetic (Q z₀) z₀.val j k v| ≤
          ε * C.clockClassKinetic (Q z₀) z₀.val j k v) ∧
      |originalReferenceClockProbe C z₀.val z₀.property f (s,t) -
        C.clockClassProbe (Q z₀) z₀.val z₀.property f j k| ≤ probeError := by
    let x : I := ⟨s, (Q z₀).subset j hs⟩
    let y : I := ⟨t, (Q z₀).subset k ht⟩
    have hx : (Q z₀).rangeClassify x = j := (Q z₀).rangeClassify_eq_of_mem j hs
    have hy : (Q z₀).rangeClassify y = k := (Q z₀).rangeClassify_eq_of_mem k ht
    have hallowed : C.clockClassAllowed (Q z₀) ((Q z₀).rangeClassify x)
        ((Q z₀).rangeClassify y) := by rw [hx, hy]; exact hjk
    let Rdata := Classical.choice (hRdata z₀)
    have hh := hfull z₀ j k hjk s hs t ht
    refine ⟨hh.1, hh.2.1, trivial, hh.2.2, ?_, ?_⟩
    · intro v
      simpa only [OriginalPopulationCoefficientCore.originalMaskedClockKinetic,
        hallowed, ↓reduceIte, hx, hy, hjk] using Rdata.relative x y hallowed v
    · simpa only [OriginalPopulationCoefficientCore.originalRangeClockProbe, hx, hy] using
        Rdata.probe_error x y hallowed
  refine ⟨Q, fun z₀ ↦ U z₀.val, hRdata, hfull, fun z₀ ↦ hU z₀.val, ?_, ?_, ?_⟩
  · intro z₀ j k hjk s hs t ht
    exact ⟨(hQ z₀ j k hjk s hs t ht).1, (hQ z₀ j k hjk s hs t ht).2.1⟩
  · intro z₀ z hz z' hz' s hs t ht hst hA hB
    exact hregion z hz.1 z' hz'.1 s hs t ht
      (hgeometry z₀.val z₀.property z hz z' hz').1 hst hA hB
  intro z₀ z hz z' hz' j k hjk s hs t ht hA hB
  obtain ⟨hsI, htI, hhalf, hforward, hkin, hprobe⟩ := hQ z₀ j k hjk s hs t ht
  obtain ⟨hdiam, hcost, hphysicalProbe⟩ := hgeometry z₀.val z₀.property z hz z' hz'
  have hp := hregion z hz.1 z' hz'.1 s hsI t htI hdiam hforward hA hB
  refine ⟨hp, ?_, ?_⟩
  · let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let v := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
    let raw := matrixQuadratic (C.matrix z₀.val (s, t)) v
    let frozen := C.clockClassKinetic (Q z₀) z₀.val j k v
    have hraw_le : raw ≤ (1 + ε) * frozen := by
      have h := (abs_le.mp (hkin v)).2
      dsimp only [raw, frozen]
      linarith
    have hcost' := hcost (s, t) hp
    have hscaled := mul_le_mul_of_nonneg_left hraw_le (by positivity : 0 ≤ 2 * ε)
    have htri := abs_sub_le (populationSeedPairDeficit S (s, t) (R z, R z')) raw frozen
    have hbin := hkin v
    change |populationSeedPairDeficit S (s, t) (R z, R z') - frozen| ≤
      (3 * ε + 2 * ε ^ 2) * frozen
    nlinarith only [hcost', hscaled, htri, hbin]
  · have hreference : originalReferenceClockProbe C z₀.val z₀.property f (s, t) =
        f (D.corePoint i (z₀.val, s), D.corePoint i (z₀.val, t)) := by
      dsimp only [originalReferenceClockProbe, corePoint]
      rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
        ⟨z₀.val, C.roots_subset_piece z₀.property⟩]
    have hphysical := hphysicalProbe s hsI t htI
    rw [← hreference] at hphysical
    have htri := abs_sub_le (f (D.corePoint i (z, s), D.corePoint i (z', t)))
      (originalReferenceClockProbe C z₀.val z₀.property f (s, t))
      (C.clockClassProbe (Q z₀) z₀.val z₀.property f j k)
    linarith


/-- For any of the SAME actual fine bins carrying the produced resampling certificate,
the literal class-pressure limit has a quantitative error against the canonical
original retained-root pressure. Neither a pressure-identification nor a class-law
continuity premise is supplied. -/
theorem PopulationLocalPressureCore.ae_original_clockClass_resampling_pressure_bound
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hlabel : ν.map a = μ.map a)
    (hdim : 6 ≤ finrank ℝ E) (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count)
    (hwindowGap : (D.haar.continuous.coefficient i).roots.Nonempty →
      ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap) :
    let C := D.haar.continuous.coefficient i
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ∀ᵐ z ∂(μ.map a).restrict C.roots, ∀ hz : z ∈ C.roots,
      ∀ {width : ℝ} (Q : FiniteScalarBins range width)
        {ε probeError : ℝ}, 0 ≤ ε → ε ≤ 1 → 0 ≤ probeError →
      OriginalRangeClockResamplingData C Q z hz f ε probeError →
      (∀ j k, C.clockClassAllowed Q j k → ∀ x ∈ Q.cell j, ∀ y ∈ Q.cell k,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) →
      ∃ pref : ℝ → ℝ,
        (∀ t, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ⟨z,hz⟩ Q
          hη hgap.le hδ hδ1 f R t) atTop (𝓝 (pref t))) ∧
        ∀ t, |originalSeedRetainedRootPressure (P C.seedIndex).seed a χ b f z t - pref t| ≤
          ε * (pref t + |t| * ‖f‖) + |t| * probeError := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let χkernel := D.originalClosedWindowPairKernel hcomplete γ
  have hsame := D.ae_originalClosedWindow_scalePressure_eq_range γ hF hcomplete hu ha hinj horder
    hb hμreg hνreg hμinv hνinv hlabel hgap.le hδ hδ1 f i
  filter_upwards [hsame, ae_restrict_of_ae hsep] with z hscale hzsep
  intro hz width Q ε probeError hε0 hε1 hprobe Rdata hfull
  let ref : C.roots := ⟨z,hz⟩
  have hzpop : z ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,hz⟩
  have hgoodRoot := (D.haar.continuous.population.good z hzpop).1
  obtain ⟨π,⟨_hπ,hmap⟩,_⟩ := existsUnique_subtype_coupling_lift hrange.measurableSet hrange.measurableSet
    hgoodRoot.2.2.1 hgoodRoot.2.2.2 hgoodRoot.1
  let read : range × range → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  have hread : Measurable read := measurable_subtype_coe.prodMap measurable_subtype_coe
  have : IsProbabilityMeasure (π.map read) := by rw [hmap]; infer_instance
  let : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map read
  let χ := π.restrict (read ⁻¹' C.window.region)
  have hχmap : χ.map read = (γ ref.val).restrict C.window.region := by
    rw [← Measure.restrict_map hread C.window.isCompact_region.measurableSet,hmap]
  have hχmass : χ.real univ = ((γ ref.val).restrict C.window.region).real univ := by
    rw [← hχmap]
    exact (map_measureReal_apply hread MeasurableSet.univ).symm
  have hpos : 0 < χ.real univ := by
    rw [hχmass,← D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i ref.val ref.property]
    exact (sub_pos.mpr hδ1).trans (D.originalClosedWindowPairKernel_mass_lower γ hcomplete hgap.le hδ i ref)
  let : IsProbabilityMeasure (normalizedFiniteLaw χ) := normalizedFiniteLaw_probability χ hpos
  let law : ProbabilityMeasure (range × range) := ⟨normalizedFiniteLaw χ,inferInstance⟩
  let α := law.map measurable_fst.aemeasurable
  let β := law.map measurable_snd.aemeasurable
  have hac : (law : Measure (range × range)) ≪ π :=
    (Measure.absolutelyContinuous_of_le (show χ ≤ π from Measure.restrict_le_self)).smul_left _
  have hregion : ∀ᵐ p ∂(law : Measure (range × range)), read p ∈ C.window.region :=
    ae_normalizedFiniteLaw (ae_restrict_mem (C.window.isCompact_region.measurableSet.preimage hread))
  have hα : ∀ᵐ x ∂(α : Measure range), x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_Icc.preimage measurable_subtype_coe)).mpr
    exact hregion.mono (fun _ h ↦ h.1.1)
  have hβ : ∀ᵐ y ∂(β : Measure range), y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    apply (ae_map_iff measurable_snd.aemeasurable
      (measurableSet_Icc.preimage measurable_subtype_coe)).mpr
    exact hregion.mono (fun _ h ↦ h.1.2)
  have hzRefPop : ref.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,ref.property⟩
  have hgood := (D.haar.continuous.population.good ref.val hzRefPop).1
  have hπgap : ∀ᵐ p ∂π, gap ≤ p.2.val-p.1.val :=
    ae_of_ae_map hread.aemeasurable (by rw [hmap]; exact hgood.2.1)
  have hgapLaw : ∀ᵐ p ∂(law : Measure (range × range)), gap ≤ p.2.val-p.1.val := hac.ae_le hπgap
  have hγS : ∀ᵐ p ∂γ ref.val, p.1 ∈ (condDistrib u a μ ref.val).support :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hgood.1.1]; exact Measure.support_mem_ae)
  have hγT : ∀ᵐ p ∂γ ref.val, p.2 ∈ (condDistrib u a ν ref.val).support :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hgood.1.2]; exact Measure.support_mem_ae)
  have hπS : ∀ᵐ p ∂π, p.1.val ∈ (condDistrib u a μ ref.val).support :=
    ae_of_ae_map hread.aemeasurable (by rw [hmap]; exact hγS)
  have hπT : ∀ᵐ p ∂π, p.2.val ∈ (condDistrib u a ν ref.val).support :=
    ae_of_ae_map hread.aemeasurable (by rw [hmap]; exact hγT)
  have hS : ∀ᵐ x ∂(α : Measure range), x.val ∈ (condDistrib u a μ ref.val).support := by
    apply (ae_map_iff measurable_fst.aemeasurable
      ((condDistrib u a μ ref.val).isClosed_support.measurableSet.preimage measurable_subtype_coe)).mpr
    exact hac.ae_le hπS
  have hT : ∀ᵐ y ∂(β : Measure range), y.val ∈ (condDistrib u a ν ref.val).support := by
    apply (ae_map_iff measurable_snd.aemeasurable
      ((condDistrib u a ν ref.val).isClosed_support.measurableSet.preimage measurable_subtype_coe)).mpr
    exact hac.ae_le hπT
  have hsepLaw : ∀ᵐ p ∂(α : Measure range).prod (β : Measure range), gap ≤ |p.2.val-p.1.val| := by
    filter_upwards [ae_fst_of_ae hS,ae_snd_of_ae hT] with p hs ht
    simpa only [Real.dist_eq,abs_sub_comm] using hzsep.separated p.1.val hs p.2.val ht
  have hlegal : ∀ᵐ p ∂(law : Measure (range × range)),
      C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2) := by
    filter_upwards [hregion] with p hp
    exact ⟨(p.1.val,p.2.val),hp,Q.rangeClassify_mem p.1,Q.rangeClassify_mem p.2⟩
  have hq : 4 < finrank ℝ (P C.seedIndex).seed.covector.ker := by
    have hh := (P C.seedIndex).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at hh
    omega
  obtain ⟨p,pref,hp,hpref,herror⟩ := OriginalRangeClockResamplingData.exists_pressure_limits
    C hF hcomplete hu ha hinj Q ref.val ref.property f hε0 hε1 hprobe Rdata hq
    (α : Measure range) (β : Measure range) (law : Measure (range × range)) ⟨rfl,rfl⟩ hlegal
  have heq (t : ℝ) : originalSeedRetainedRootPressure (P C.seedIndex).seed a χkernel b f z t = p t := by
    have hcanonical := (hp t).congr' (Filter.Eventually.of_forall fun R ↦
      C.fine_clock_scalePressure_eq_canonical_original Q (hwindowGap ⟨z,hz⟩) hfull
        z hz f (α : Measure range) (β : Measure range) hα hβ hsepLaw R t)
    have hlim : Tendsto (fun R ↦ originalSeedRetainedScalePressure
        (P C.seedIndex).seed a χkernel b f R t z) atTop (𝓝 (p t)) :=
      hcanonical.congr' (Filter.Eventually.of_forall fun R ↦ (hscale hz π hmap law rfl R t).symm)
    exact hlim.limUnder_eq
  have hobs := D.originalClosedWindow_class_observation hrange.measurableSet γ i ref π hmap Q
    (hwindowGap ⟨z,hz⟩) hfull hη hgap.le hδ hδ1
  have hαclass : (normalizedClockClassPairMeasure
      (D.originalWindowReferenceWeights γ gap range i ref Q η)).map Prod.fst =
      (α : Measure range).map Q.rangeClassify := by
    change _ = (((law : Measure (range × range)).map Prod.fst).map Q.rangeClassify)
    rw [← hobs.2.2.2.2.1,Measure.map_map measurable_fst
      (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify),
      Measure.map_map Q.measurable_rangeClassify measurable_fst]
    rfl
  have hβclass : (normalizedClockClassPairMeasure
      (D.originalWindowReferenceWeights γ gap range i ref Q η)).map Prod.snd =
      (β : Measure range).map Q.rangeClassify := by
    change _ = (((law : Measure (range × range)).map Prod.snd).map Q.rangeClassify)
    rw [← hobs.2.2.2.2.1,Measure.map_map measurable_snd
      (Q.measurable_rangeClassify.prodMap Q.measurable_rangeClassify),
      Measure.map_map Q.measurable_rangeClassify measurable_snd]
    rfl
  simp only [ref] at hαclass hβclass
  refine ⟨pref,?_,?_⟩
  · intro t
    simpa only [PopulationLocalPressureCore.originalWindowClassScalePressure,hαclass,hβclass,C,
      ref, ProbabilityMeasure.toMeasure_map] using hpref t
  · intro t
    rw [heq]
    exact herror t

/-- Every given sequence of the SAME actual bins carrying the produced accuracy and
endpoint certificates converges to the canonical original retained pressure. The AE
set is chosen before all bin sequences and all real tilts. -/
theorem PopulationLocalPressureCore.ae_original_same_clockClass_pressure_convergence
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hlabel : ν.map a = μ.map a)
    (hdim : 6 ≤ finrank ℝ E) (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count)
    (hwindowGap : (D.haar.continuous.coefficient i).roots.Nonempty →
      ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap) :
    let C := D.haar.continuous.coefficient i
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ∀ᵐ z ∂(μ.map a).restrict C.roots, ∀ hz : z ∈ C.roots,
      ∀ (width : ℕ → ℝ) (Q : ∀ n, FiniteScalarBins range (width n)),
      (∀ n, Nonempty (OriginalRangeClockResamplingData C (Q n) z hz f
        (originalUpperRefinementAccuracy n) (originalUpperRefinementAccuracy n))) →
      (∀ n j k, C.clockClassAllowed (Q n) j k →
        ∀ x ∈ (Q n).cell j, ∀ y ∈ (Q n).cell k,
          x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) →
      ∃ pref : ℕ → ℝ → ℝ,
        (∀ n t, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ⟨z,hz⟩ (Q n)
          hη hgap.le hδ hδ1 f R t) atTop (𝓝 (pref n t))) ∧
        ∀ t, Tendsto (fun n ↦ pref n t) atTop
          (𝓝 (originalSeedRetainedRootPressure (P C.seedIndex).seed a χ b f z t)) := by
  have hactual := D.ae_original_clockClass_resampling_pressure_bound hrange γ hF hcomplete hu
    ha hinj horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hδ hδ1 hη f i hwindowGap
  filter_upwards [hactual] with z hzactual
  intro hz width Q hRdata hfull
  have hstep (n : ℕ) := hzactual hz (Q n)
    (originalUpperRefinementAccuracy_pos_lt_one n).1.le
    (originalUpperRefinementAccuracy_pos_lt_one n).2.le
    (originalUpperRefinementAccuracy_pos_lt_one n).1.le
    (Classical.choice (hRdata n)) (hfull n)
  choose pref hpref herror using hstep
  refine ⟨pref, hpref, ?_⟩
  intro t
  have hD : Tendsto (fun n ↦ |t| * originalUpperRefinementAccuracy n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_originalUpperRefinementAccuracy.const_mul |t|
  apply tendsto_pressure_of_relative_error atTop (fun n ↦ pref n t)
    originalUpperRefinementAccuracy (fun n ↦ |t| * originalUpperRefinementAccuracy n)
    (originalSeedRetainedRootPressure
      (P (D.haar.continuous.coefficient i).seedIndex).seed a
      (D.originalClosedWindowPairKernel hcomplete γ) b f z t)
    (|t| * ‖f‖) tendsto_originalUpperRefinementAccuracy hD
  exact Filter.Eventually.of_forall fun n ↦
    ⟨(originalUpperRefinementAccuracy_pos_lt_one n).1.le,
      (originalUpperRefinementAccuracy_pos_lt_one n).2, herror n t⟩

/-- The exact Haar-weighted pressure readout of any GIVEN accurate class refinement
converges to the same actual retained physical root pressure. The original inverse
intensity, retained mass and rescaled physical tilt are preserved. -/
theorem PopulationLocalPressureCore.ae_original_same_weighted_clockClass_pressure_convergence
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hlabel : ν.map a = μ.map a)
    (hdim : 6 ≤ finrank ℝ E) (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count)
    (hwindowGap : (D.haar.continuous.coefficient i).roots.Nonempty →
      ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap) :
    let C := D.haar.continuous.coefficient i
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ∀ᵐ z ∂(μ.map a).restrict C.roots, ∀ hz : z ∈ C.roots,
      ∀ (width : ℕ → ℝ) (Q : ∀ n, FiniteScalarBins range (width n)),
      (∀ n, Nonempty (OriginalRangeClockResamplingData C (Q n) z hz f
        (originalUpperRefinementAccuracy n) (originalUpperRefinementAccuracy n))) →
      (∀ n j k, C.clockClassAllowed (Q n) j k →
        ∀ x ∈ (Q n).cell j, ∀ y ∈ (Q n).cell k,
          x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
          y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) →
      ∃ pref : ℕ → ℝ → ℝ,
        (∀ n t, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ⟨z,hz⟩ (Q n)
          hη hgap.le hδ hδ1 f R t) atTop (𝓝 (pref n t))) ∧
        let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z
        let density := fun n ↦
          (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
          (clockClassPairMeasure
            (D.originalWindowReferenceWeights γ gap range i ⟨z,hz⟩ (Q n) η)).real univ
        ∀ t, Tendsto (fun n ↦ theta⁻¹ * (density n) ^ (1-2/(q:ℝ)) *
          pref n (t * (density n) ^ (2/(q:ℝ)))) atTop
          (𝓝 (originalRetainedFinslerRootPressure P a κ (μ.map a)
            (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 t z)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  have hactual := D.ae_original_same_clockClass_pressure_convergence hrange γ hF hcomplete hu
    ha hinj horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hδ hδ1 hη f i hwindowGap
  filter_upwards [hactual] with z hclass
  intro hz width Q hRdata hfull
  obtain ⟨pref,hpref,hconv⟩ := hclass hz width Q hRdata hfull
  refine ⟨pref,hpref,?_⟩
  dsimp only
  let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z
  let d := ((1-η) * theta) * (χ z).real univ
  let density := fun n ↦
    (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
      (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ⟨z,hz⟩ (Q n) η)).real univ
  have hd n : density n = d := by
    exact D.originalWindowReferenceWeights_coordinate_intensity hrange.measurableSet γ hcomplete i ⟨z,hz⟩
      (Q n) (hwindowGap ⟨z,hz⟩) (hfull n) hη hgap.le hδ hδ1
  intro t
  have htarget : originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 t z =
      theta⁻¹ * d ^ (1-2/(q:ℝ)) *
        originalSeedRetainedRootPressure (P C.seedIndex).seed a χ b f z (t*d^(2/(q:ℝ))) := by
    rw [originalRetainedFinslerRootPressure_eq_on_piece P a κ (μ.map a)
      (fun _ ↦ χ) (fun _ _ ↦ η) b f 0 C.seedIndex t (C.roots_subset_piece hz)]
    rfl
  rw [htarget]
  have hlim := (hconv (t*d^(2/(q:ℝ)))).const_mul (theta⁻¹*d^(1-2/(q:ℝ)))
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    change theta⁻¹*d^(1-2/(q:ℝ))*pref n (t*d^(2/(q:ℝ))) =
      theta⁻¹*(density n)^(1-2/(q:ℝ))*pref n (t*(density n)^(2/(q:ℝ)))
    rw [hd n]

end OTSelector.Reconstruction
