import OTSelector.Reconstruction.FinslerOriginalClassRetentionPressure
import OTSelector.Reconstruction.FinslerOriginalPhysicalUnitDensitySupportedUpper

/-!
# Actual scalar-retention removal on the same original frozen cells

Fix the original core, cells, references and class windows first. Scalar retention multiplies
the same original raw matrix by 1-eta and leaves its normalized actual class law unchanged.
The actual unit-density pressure producer supplies its limit and Lipschitz continuity, so
the full original Haar-weighted leading contribution converges as eta tends to zero.

The sample/side-length limit is taken at each fixed retention before retention is removed.
No assertion about uniform geometry constants across different refined cores is made.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 20000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}
  {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
  (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
    (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)

/-- The actual retained point density in the original upper's coordinate Haar convention. -/
def PopulationLocalPressureCore.originalWindowRetainedDensity
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins I width) (cHaar : ℝ≥0) (η : ℝ) : ℝ≥0 :=
  cHaar * (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap I i ref Q η) univ).toNNReal

/-- Actual retained Haar density scales by exactly the same scalar as its original matrix. -/
theorem PopulationLocalPressureCore.originalWindowRetainedDensity_eq
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins I width) (cHaar : ℝ≥0)
    {η : ℝ} (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    (D.originalWindowRetainedDensity γ gap i ref Q cHaar η : ℝ) =
      (1 - η) * (D.originalWindowRetainedDensity γ gap i ref Q cHaar 0 : ℝ) := by
  have hzero := D.originalWindowReferenceWeights_mass γ gap I i ref Q (by norm_num : (0 : ℝ) < 1) hgap hδ hδ1
  have hret := D.originalWindowReferenceWeights_mass γ gap I i ref Q hη hgap hδ hδ1
  simp only [originalWindowRetainedDensity, NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
    ← measureReal_def, clockClassPairMeasure_real_univ _ hret.1,
    clockClassPairMeasure_real_univ _ hzero.1]
  simp_rw [D.originalWindowReferenceWeights_retention γ gap i ref Q η, ← Finset.mul_sum]
  ring

/-- One canonical actual pressure works at every scalar retention on a fixed original
window. Its original finite-model limit supplies continuity; no pressure-continuity or
error-convergence callback is used. Both physical density and tilt retain their exact powers. -/
theorem PopulationLocalPressureCore.exists_original_window_retention_pressure_limits
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins I width) (cHaar : ℝ≥0) (hcHaar : 0 < cHaar)
    (f : M × M →ᵇ ℝ) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (hq : 4 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) :
    let C := D.haar.continuous.coefficient i
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let P₀ := D.originalWindowReferenceWeights γ gap I i ref Q 0
    let hw := D.originalWindowReferenceWeights_mass γ gap I i ref Q (by norm_num : (0 : ℝ) < 1) hgap hδ hδ1
    let _instJoint := normalizedClockClassPairMeasure_probability P₀ hw.1 hw.2.2.2
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let density := D.originalWindowRetainedDensity γ gap i ref Q cHaar
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q) α β
        (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) L t)
        atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ‖f‖₊ p ∧
      (∀ η : ℝ, η < 1 → normalizedClockClassPairMeasure
        (D.originalWindowReferenceWeights γ gap I i ref Q η) = normalizedClockClassPairMeasure P₀) ∧
      (∀ η : ℝ, η < 1 → ∀ t,
        Tendsto (fun L : ℝ ↦ finiteClassLegalPressure q (C.clockClassAllowed Q) α β
          (density η * Real.toNNReal (L ^ q))
          (C.densityClockClassKinetic Q ref.val (density η))
          (C.clockClassProbe Q ref.val ref.property f) t / L ^ q) atTop
          (𝓝 ((density η : ℝ) ^ (1 - 2 / (q : ℝ)) * p (t * (density η : ℝ) ^ (2 / (q : ℝ)))))) ∧
      ∀ t, Tendsto (fun η : ℝ ↦ (density η : ℝ) ^ (1 - 2 / (q : ℝ)) *
          p (t * (density η : ℝ) ^ (2 / (q : ℝ)))) (𝓝 0)
        (𝓝 ((density 0 : ℝ) ^ (1 - 2 / (q : ℝ)) * p (t * (density 0 : ℝ) ^ (2 / (q : ℝ))))) := by
  intro C q P₀ hw _instJoint α β _instS _instT density
  obtain ⟨p,hp,hphysical,hconc,hlip⟩ := C.exists_clockClassPressure_unit_density
    Q ref.val ref.property f P₀ hw.1 hw.2.1 hw.2.2.2 hq
  refine ⟨p,hp,hconc,hlip,?_,?_,?_⟩
  · intro η hη
    exact D.normalized_originalWindowReferenceWeights_retention γ gap i ref Q hη hw.1 hw.2.2.2
  · intro η hη t
    have hret := D.originalWindowReferenceWeights_mass γ gap I i ref Q hη hgap hδ hδ1
    have hpositive : 0 < density η := by
      apply mul_pos hcHaar
      apply ENNReal.toNNReal_pos
      · have hm : 0 < (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap I i ref Q η)).real univ := by
          rw [clockClassPairMeasure_real_univ _ hret.1]
          exact hret.2.2.2
        exact ne_of_gt (ENNReal.toReal_pos_iff.mp hm).1
      · exact measure_ne_top _ _
    exact hphysical (density η) hpositive t
  · intro t
    have hqNat : 4 < q := hq
    have hqR : (2 : ℝ) < q := by exact_mod_cast (show 2 < q by omega)
    have hlim := tendsto_density_weighted_pressure_retention (density := (density 0 : ℝ))
      (t := t) hqR hlip.continuous
    apply hlim.congr'
    filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)] with η hη
    rw [D.originalWindowRetainedDensity_eq γ gap i ref Q cHaar hη hgap hδ hδ1]


/-- On one unchanged original finite cell/reference family, scalar retention disappears
from the complete actual Haar-weighted upper leading sum. The same original unit pressure
limits and normalized class laws are retained, with continuity proved by their producer. -/
theorem PopulationLocalPressureCore.exists_original_frozen_family_retention_error_tendsto_zero
    {Cell : Type*} [Fintype Cell]
    (coreIndex : Cell → Fin D.haar.continuous.count)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (cell : Cell → Set (ℚ → M))
    (Q : ∀ i : Fin D.haar.continuous.count, (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
    (cHaar : Cell → ℝ≥0) (hcHaar : ∀ c, 0 < cHaar c)
    (f : M × M →ᵇ ℝ) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (hdim : 6 ≤ finrank ℝ E) :
    let C := fun c ↦ D.haar.continuous.coefficient (coreIndex c)
    let q := fun c ↦ finrank ℝ (P (C c).seedIndex).seed.covector.ker
    let Qlocal := fun c ↦ Q (coreIndex c) (reference c)
    let P₀ := fun c ↦ D.originalWindowReferenceWeights γ gap I (coreIndex c) (reference c) (Qlocal c) 0
    let hw := fun c ↦ D.originalWindowReferenceWeights_mass γ gap I (coreIndex c) (reference c)
      (Qlocal c) (by norm_num : (0 : ℝ) < 1) hgap hδ hδ1
    let density := fun c ↦ D.originalWindowRetainedDensity γ gap (coreIndex c) (reference c) (Qlocal c) (cHaar c)
    let coord := fun c ↦ atlasSeedCoord (P (C c).seedIndex).seed
      (Module.finBasis ℝ (P (C c).seedIndex).seed.covector.ker).equivFunL a
    ∃ p : Cell → ℝ → ℝ,
      (∀ c,
        let _instJoint := normalizedClockClassPairMeasure_probability (P₀ c) (hw c).1 (hw c).2.2.2
        let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
        let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
        let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
        let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
        ∀ t, Tendsto (fun L ↦ finiteClassLegalScalePressure (q c) ((C c).clockClassAllowed (Qlocal c)) α β
          ((C c).clockClassKinetic (Qlocal c) (reference c).val)
          ((C c).clockClassProbe (Qlocal c) (reference c).val (reference c).property f) L t)
          atTop (𝓝 (p c t))) ∧
      (∀ c, LipschitzWith ‖f‖₊ (p c)) ∧
      ∀ t,
        let leading := fun η ↦ ∑ c, volume.real ((coord c) '' cell c) *
          ((density c η : ℝ) ^ (1 - 2 / (q c : ℝ)) * p c (t * (density c η : ℝ) ^ (2 / (q c : ℝ))))
        Tendsto leading (𝓝 0) (𝓝 (leading 0)) ∧
          Tendsto (fun η ↦ |leading η - leading 0|) (𝓝 0) (𝓝 0) := by
  intro C q Qlocal P₀ hw density coord
  have hq (c : Cell) : 4 < q c := by
    have h := D.original_seed_label_finrank (coreIndex c)
    change q c = finrank ℝ E - 1 at h
    omega
  have hmodels (c : Cell) := D.exists_original_window_retention_pressure_limits γ gap
    (coreIndex c) (reference c) (Qlocal c) (cHaar c) (hcHaar c) f hgap hδ hδ1 (hq c)
  choose p hp _hconc hlip _hnorm _hphysical hret using hmodels
  refine ⟨p,hp,hlip,?_⟩
  intro t
  dsimp only
  have hsum : Tendsto (fun η : ℝ ↦ ∑ c, volume.real ((coord c) '' cell c) *
      ((density c η : ℝ) ^ (1 - 2 / (q c : ℝ)) * p c (t * (density c η : ℝ) ^ (2 / (q c : ℝ)))))
      (𝓝 0) (𝓝 (∑ c, volume.real ((coord c) '' cell c) *
        ((density c 0 : ℝ) ^ (1 - 2 / (q c : ℝ)) * p c (t * (density c 0 : ℝ) ^ (2 / (q c : ℝ)))))) :=
    tendsto_finsetSum Finset.univ (fun c _ ↦
      (hret c t).const_mul (volume.real ((coord c) '' cell c)))
  refine ⟨hsum, ?_⟩
  simpa only [sub_self, abs_zero] using (hsum.sub_const
    (∑ c, volume.real ((coord c) '' cell c) *
      ((density c 0 : ℝ) ^ (1 - 2 / (q c : ℝ)) * p c (t * (density c 0 : ℝ) ^ (2 / (q c : ℝ)))))).abs


/-- A concrete positive original core/retention accuracy, chosen before any sample limit. -/
def originalUpperRefinementAccuracy (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

/-- The explicit original refinement accuracy satisfies every positive subunit budget. -/
theorem originalUpperRefinementAccuracy_pos_lt_one (k : ℕ) :
    0 < originalUpperRefinementAccuracy k ∧ originalUpperRefinementAccuracy k < 1 := by
  unfold originalUpperRefinementAccuracy
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · positivity
  · apply (div_lt_one (by positivity : (0 : ℝ) < k + 2)).mpr
    linarith

/-- This actual refinement accuracy tends to zero without a prescribed error-limit input. -/
theorem tendsto_originalUpperRefinementAccuracy :
    Tendsto originalUpperRefinementAccuracy atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [∀ j, SigmaFinite (κ j)] in
/-- The actual supported-upper residual mass is bounded by the primitive original
retention/split/window/core losses. The core complement bound comes from its own data. -/
theorem PopulationLocalPressureCore.original_upper_residual_mass_le
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (retentionError splitError : ℝ) (hret : 0 ≤ retentionError) (hsplit : 0 ≤ splitError)
    (hloss : loss ≠ ⊤) :
    (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
      (μ.map a) D.haar.continuous.population.rootsᶜ).toReal ≤
      retentionError + splitError + δ.toReal + loss.toReal := by
  have hfinite : (μ.map a) D.haar.continuous.population.rootsᶜ ≠ ⊤ := measure_ne_top _ _
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hfinite,
    ENNReal.toReal_ofReal (by positivity)]
  exact add_le_add le_rfl
    (ENNReal.toReal_mono hloss D.haar.continuous.population.complement_small.le)

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [∀ j, SigmaFinite (κ j)] in
/-- Actual local-core producers admit an explicit refinement whose original residual mass
and supported-probe residual contribution vanish. The cores may change with k; at each k
all of its original frozen data are fixed before the empirical sample limit. No bound is
asserted for the potentially changing quadratic repair constant A_k. -/
theorem exists_original_upper_refined_cores_residual_mass_tendsto_zero
    (hcore : PopulationLocalPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (Good : (ℚ → M) → Prop) (hGood : ∀ᵐ z ∂μ.map a, Good z) :
    ∃ D : ∀ k, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r
        (ENNReal.ofReal (originalUpperRefinementAccuracy k))
        (ENNReal.ofReal (originalUpperRefinementAccuracy k)),
      let residual := fun k ↦
        (ENNReal.ofReal (originalUpperRefinementAccuracy k + originalUpperRefinementAccuracy k +
          (ENNReal.ofReal (originalUpperRefinementAccuracy k)).toReal) +
          (μ.map a) (D k).haar.continuous.population.rootsᶜ).toReal
      (∀ k, 0 ≤ residual k ∧ residual k ≤ 4 * originalUpperRefinementAccuracy k) ∧
      Tendsto residual atTop (𝓝 0) ∧
      (∀ t C : ℝ, Tendsto (fun k ↦ 2 * |t| * C * residual k) atTop (𝓝 0)) ∧
      ∀ ξ : ℕ → Measure (M × M),
        (∀ k, ξ k univ ≤ ENNReal.ofReal
          (originalUpperRefinementAccuracy k + originalUpperRefinementAccuracy k +
            (ENNReal.ofReal (originalUpperRefinementAccuracy k)).toReal) +
              (μ.map a) (D k).haar.continuous.population.rootsᶜ) →
        Tendsto (fun k ↦ (ξ k univ).toReal) atTop (𝓝 0) ∧
          ∀ t C : ℝ, Tendsto (fun k ↦ 2 * |t| * C * (ξ k univ).toReal) atTop (𝓝 0) := by
  have hpos (k : ℕ) : 0 < originalUpperRefinementAccuracy k := by
    unfold originalUpperRefinementAccuracy
    positivity
  let D := fun k ↦ Classical.choice
    (hcore Good hGood (ENNReal.ofReal (originalUpperRefinementAccuracy k))
      (ENNReal.ofReal_pos.mpr (hpos k)).ne'
      (ENNReal.ofReal (originalUpperRefinementAccuracy k))
      (ENNReal.ofReal_pos.mpr (hpos k)).ne')
  refine ⟨D, ?_⟩
  dsimp only
  let residual := fun k ↦
    (ENNReal.ofReal (originalUpperRefinementAccuracy k + originalUpperRefinementAccuracy k +
      (ENNReal.ofReal (originalUpperRefinementAccuracy k)).toReal) +
      (μ.map a) (D k).haar.continuous.population.rootsᶜ).toReal
  have hbound (k : ℕ) : 0 ≤ residual k ∧ residual k ≤ 4 * originalUpperRefinementAccuracy k := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hb := (D k).original_upper_residual_mass_le (originalUpperRefinementAccuracy k)
      (originalUpperRefinementAccuracy k) (hpos k).le (hpos k).le
      ENNReal.ofReal_ne_top
    calc
      residual k ≤ _ := hb
      _ = 4 * originalUpperRefinementAccuracy k := by
        rw [ENNReal.toReal_ofReal (hpos k).le]
        ring
  have hlim : Tendsto residual atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ (hbound k).1) (fun k ↦ (hbound k).2)
      (by simpa only [mul_zero] using tendsto_originalUpperRefinementAccuracy.const_mul 4)
  refine ⟨hbound, hlim, ?_, ?_⟩
  · intro t C
    simpa only [mul_zero] using hlim.const_mul (2 * |t| * C)
  · intro ξ hξ
    have hξlim : Tendsto (fun k ↦ (ξ k univ).toReal) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg) (fun k ↦ ?_) hlim
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top, measure_ne_top _ _⟩) (hξ k)
    refine ⟨hξlim, ?_⟩
    intro t C
    simpa only [mul_zero] using hξlim.const_mul (2 * |t| * C)


omit [∀ j, SigmaFinite (κ j)] in
/-- The original Haar population and physical label-recovery producers construct the
refined actual cores themselves. Their residual masses and literal supported-probe error
vanish under the explicit accuracy sequence, with no final convergence hypothesis. -/
theorem exists_original_physical_upper_refined_residual_mass_tendsto_zero
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (Good : (ℚ → M) → Prop) (hGood : ∀ᵐ z ∂μ.map a, Good z) :
    ∃ D : ∀ k, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r
        (ENNReal.ofReal (originalUpperRefinementAccuracy k))
        (ENNReal.ofReal (originalUpperRefinementAccuracy k)),
      let residual := fun k ↦
        (ENNReal.ofReal (originalUpperRefinementAccuracy k + originalUpperRefinementAccuracy k +
          (ENNReal.ofReal (originalUpperRefinementAccuracy k)).toReal) +
          (μ.map a) (D k).haar.continuous.population.rootsᶜ).toReal
      (∀ k, 0 ≤ residual k ∧ residual k ≤ 4 * originalUpperRefinementAccuracy k) ∧
      Tendsto residual atTop (𝓝 0) ∧
      (∀ t C : ℝ, Tendsto (fun k ↦ 2 * |t| * C * residual k) atTop (𝓝 0)) ∧
      ∀ ξ : ℕ → Measure (M × M),
        (∀ k, ξ k univ ≤ ENNReal.ofReal
          (originalUpperRefinementAccuracy k + originalUpperRefinementAccuracy k +
            (ENNReal.ofReal (originalUpperRefinementAccuracy k)).toReal) +
              (μ.map a) (D k).haar.continuous.population.rootsᶜ) →
        Tendsto (fun k ↦ (ξ k univ).toReal) atTop (𝓝 0) ∧
          ∀ t C : ℝ, Tendsto (fun k ↦ 2 * |t| * C * (ξ k univ).toReal) atTop (𝓝 0) := by
  exact exists_original_upper_refined_cores_residual_mass_tendsto_zero
    (hcore.local_core hrecovery hF hcomplete hu ha hinj hκ) Good hGood

end OTSelector.Reconstruction
