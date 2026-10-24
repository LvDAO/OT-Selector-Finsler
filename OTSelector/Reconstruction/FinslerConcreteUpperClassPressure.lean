import OTSelector.Reconstruction.FinslerConcreteUpperClassMask
import OTSelector.Reconstruction.MarkedStationaryValueLegalFiniteClassLimit
import OTSelector.Transport.Coupling.FiniteClockMixture
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation

/-!
The literal fixed Haar pair-class weights are normalized by their own total
mass. Their actual original finite-class coefficient model then has a legal
thermodynamic pressure limit; no unrestricted matching pressure is substituted.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

variable {I J : Type*} [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J] [MeasurableSingletonClass I] [MeasurableSingletonClass J]

/-- The actual raw fixed pair-class weights, retaining their original mass. -/
def clockClassPairMeasure (P : I → J → ℝ) : Measure (I × J) :=
  finiteClassPopulationCoupling P Measure.dirac Measure.dirac

instance clockClassPairMeasure_finite (P : I → J → ℝ) : IsFiniteMeasure (clockClassPairMeasure P) := by
  unfold clockClassPairMeasure finiteClassPopulationCoupling
  constructor
  simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr fun i _ ↦ ENNReal.sum_lt_top.mpr fun j _ ↦ ENNReal.ofReal_lt_top

theorem clockClassPairMeasure_real_univ (P : I → J → ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    (clockClassPairMeasure P).real univ = ∑ i, ∑ j, P i j := by
  rw [measureReal_def, clockClassPairMeasure, finiteClassPopulationCoupling_mass P _ _ hP,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hP i j)]

/-- The normalized class plan uses precisely the original fixed pair weights. -/
def normalizedClockClassPairMeasure (P : I → J → ℝ) : Measure (I × J) :=
  normalizedFiniteLaw (clockClassPairMeasure P)

instance normalizedClockClassPairMeasure_finite (P : I → J → ℝ) :
    IsFiniteMeasure (normalizedClockClassPairMeasure P) := by
  unfold normalizedClockClassPairMeasure
  infer_instance

theorem normalizedClockClassPairMeasure_probability (P : I → J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hmass : 0 < ∑ i, ∑ j, P i j) :
    IsProbabilityMeasure (normalizedClockClassPairMeasure P) := by
  apply normalizedFiniteLaw_probability
  rwa [clockClassPairMeasure_real_univ P hP]

/-- Vanishing off the original main mask gives literal almost-everywhere legal
support after normalization, including zero individual rows and columns. -/
theorem normalizedClockClassPairMeasure_legal (P : I → J → ℝ) (allowed : I → J → Prop)
    (hzero : ∀ i j, ¬allowed i j → P i j = 0) :
    ∀ᵐ p ∂normalizedClockClassPairMeasure P, allowed p.1 p.2 := by
  have hraw : ∀ᵐ p ∂clockClassPairMeasure P, allowed p.1 p.2 := by
    unfold clockClassPairMeasure finiteClassPopulationCoupling
    simp only [ae_finsetSum_measure_iff]
    intro i _ j _
    by_cases hij : allowed i j
    · rw [Measure.dirac_prod_dirac]
      have hh : ∀ᵐ p ∂Measure.dirac (i, j), allowed p.1 p.2 :=
        (ae_dirac_iff (Set.to_countable {p : I × J | allowed p.1 p.2}).measurableSet).mpr hij
      exact Measure.ae_smul_measure hh (ENNReal.ofReal (P i j))
    · rw [hzero i j hij, ENNReal.ofReal_zero, zero_smul]
      simp
  exact Measure.ae_smul_measure hraw ((clockClassPairMeasure P).real univ)⁻¹.toNNReal

/-- Null retained class mass is an actual zero measure and contributes no
cell to the pressure reference. -/
theorem clockClassPairMeasure_eq_zero_of_total_zero (P : I → J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hmass : (∑ i, ∑ j, P i j) = 0) :
    clockClassPairMeasure P = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [clockClassPairMeasure, finiteClassPopulationCoupling_mass P _ _ hP, hmass,
    ENNReal.ofReal_zero]

/-- The normalized joint law has precisely the original pair weight divided
by its own total mass, including individual zero classes. -/
theorem normalizedClockClassPairMeasure_real_singleton (P : I → J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (i : I) (j : J) :
    (normalizedClockClassPairMeasure P).real {(i, j)} = P i j / (∑ i, ∑ j, P i j) := by
  have hraw : clockClassPairMeasure P {(i, j)} = ENNReal.ofReal (P i j) := by
    simp [clockClassPairMeasure, finiteClassPopulationCoupling, Measure.finsetSum_apply,
      Measure.smul_apply, Measure.dirac_prod_dirac, Pi.single_apply, Prod.mk.injEq, ite_and]
  rw [normalizedClockClassPairMeasure, normalizedFiniteLaw, measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ (inv_nonneg.mpr measureReal_nonneg), clockClassPairMeasure_real_univ P hP]
  have hrawReal : (clockClassPairMeasure P).real {(i, j)} = P i j := by
    simp only [measureReal_def, hraw, ENNReal.toReal_ofReal (hP i j)]
  rw [hrawReal]
  ring

/-- The same normalized fixed class plan packaged as a probability measure. -/
def clockClassJointProbability (P : I → J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hmass : 0 < ∑ i, ∑ j, P i j) : ProbabilityMeasure (I × J) :=
  ⟨normalizedClockClassPairMeasure P, normalizedClockClassPairMeasure_probability P hP hmass⟩

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The actual original finite clock-class coefficient and physical probe have
an original-mask pressure limit for every nonzero fixed pair-class weight
matrix. Only that literal matrix is normalized; its lost mass stays in the
physical cell intensity. -/
theorem OriginalPopulationCoefficientCore.exists_clockClassPressure_limit
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hzero : ∀ j k, ¬C.clockClassAllowed Q j k → P₀ j k = 0)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 4 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure
        (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨‖f‖, norm_nonneg f⟩ p := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  have hnested : ∀ j j', (∀ k, C.clockClassAllowed Q j k → C.clockClassAllowed Q j' k) ∨
      (∀ k, C.clockClassAllowed Q j' k → C.clockClassAllowed Q j k) := by
    intro j j'
    exact C.clockClassAllowed_rows_nested Q j j'
  have hk : Measurable (Function.uncurry (fun p : Fin Q.count × Fin Q.count ↦
      C.clockClassKinetic Q z₀ p.1 p.2)) := C.measurable_clockClassKinetic Q z₀
  have hπ : Vlasov.IsCoupling (π : Measure (Fin Q.count × Fin Q.count))
      (α : Measure (Fin Q.count)) (β : Measure (Fin Q.count)) := by
    constructor <;> rfl
  have hlegal : ∀ᵐ p ∂(π : Measure (Fin Q.count × Fin Q.count)), C.clockClassAllowed Q p.1 p.2 :=
    normalizedClockClassPairMeasure_legal P₀ _ hzero
  have result := exists_finiteClassLegalScalePressure_limit_of_nested
    (A := Fin Q.count) (B := Fin Q.count) (C.clockClassAllowed Q) hnested
    (α : Measure _) (β : Measure _) (π : Measure _) hπ hlegal
    (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) hq hK (norm_nonneg f)
    (kin := C.clockClassKinetic Q z₀) hk (C.clockClassKinetic_nonneg Q z₀ hz₀) hbound
    (fun j k c _ v ↦ C.clockClassKinetic_homogeneous Q z₀ j k c v)
    (C.clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f)
  exact result


/-- Count intensity includes the original Haar density and retained class mass.
This kinetic factor keeps the original physical N^(2/q) cost scale unchanged. -/
def OriginalPopulationCoefficientCore.densityClockClassKinetic
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width) (z₀ : Z)
    (density : ℝ) (j k : Fin Q.count)
    (v : Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) : ℝ :=
  density ^ (-2 / (Module.finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ)) *
    C.clockClassKinetic Q z₀ j k v

/-- The actual density-scaled original finite-class model has a pressure limit,
with the same limit under intensity normalization and uniform convergence on
compact tilt sets. The mark law stays P0 divided by its own total mass. -/
theorem OriginalPopulationCoefficientCore.exists_density_clockClassPressure_limit
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hzero : ∀ j k, ¬C.clockClassAllowed Q j k → P₀ j k = 0)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (density : ℝ) (hdensity : 0 < density)
    (hq : 4 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let kin := C.densityClockClassKinetic Q z₀ density
    let probe := C.clockClassProbe Q z₀ hz₀ f
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) kin probe R t) atTop (𝓝 (p t))) ∧
      (∀ t, Tendsto (fun r : ℝ ↦ finiteClassLegalPressure q (C.clockClassAllowed Q)
        (α : Measure _) (β : Measure _) (Real.toNNReal r) kin probe t / r) atTop (𝓝 (p t))) ∧
      (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
        (fun R ↦ finiteClassLegalScalePressure q (C.clockClassAllowed Q)
          (α : Measure _) (β : Measure _) kin probe R) p atTop K) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨‖f‖, norm_nonneg f⟩ p := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let factor := density ^ (-2 / (q : ℝ))
  let kin := C.densityClockClassKinetic Q z₀ density
  let probe := C.clockClassProbe Q z₀ hz₀ f
  have hfactor : 0 ≤ factor := Real.rpow_nonneg hdensity.le _
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  have hnested : ∀ j j', (∀ k, C.clockClassAllowed Q j k → C.clockClassAllowed Q j' k) ∨
      (∀ k, C.clockClassAllowed Q j' k → C.clockClassAllowed Q j k) := by
    intro j j'
    exact C.clockClassAllowed_rows_nested Q j j'
  have hk : Measurable (Function.uncurry (fun p : Fin Q.count × Fin Q.count ↦ kin p.1 p.2)) :=
    (C.measurable_clockClassKinetic Q z₀).const_mul factor
  have hkn : ∀ j k v, 0 ≤ kin j k v := fun j k v ↦
    mul_nonneg hfactor (C.clockClassKinetic_nonneg Q z₀ hz₀ j k v)
  have hkb : ∀ j k v, |kin j k v| ≤ (factor * K) * ∑ l, v l ^ 2 := by
    intro j k v
    change |factor * C.clockClassKinetic Q z₀ j k v| ≤ _
    rw [abs_mul, abs_of_nonneg hfactor]
    exact (mul_le_mul_of_nonneg_left (hbound j k v) hfactor).trans_eq (by ring)
  have hhom : ∀ j k (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin j k (fun l ↦ c * v l) = c ^ 2 * kin j k v := by
    intro j k c _ v
    change factor * C.clockClassKinetic Q z₀ j k (c • v) =
      c ^ 2 * (factor * C.clockClassKinetic Q z₀ j k v)
    rw [C.clockClassKinetic_homogeneous Q z₀ j k c v]
    ring
  have hπ : Vlasov.IsCoupling (π : Measure (Fin Q.count × Fin Q.count))
      (α : Measure (Fin Q.count)) (β : Measure (Fin Q.count)) := by constructor <;> rfl
  have hlegal : ∀ᵐ p ∂(π : Measure (Fin Q.count × Fin Q.count)), C.clockClassAllowed Q p.1 p.2 :=
    normalizedClockClassPairMeasure_legal P₀ _ hzero
  obtain ⟨p, hpt, hconc, hlip⟩ := exists_finiteClassLegalScalePressure_limit_of_nested
    (A := Fin Q.count) (B := Fin Q.count) (C.clockClassAllowed Q) hnested
    (α : Measure _) (β : Measure _) (π : Measure _) hπ hlegal q hq
    (mul_nonneg hfactor hK) (norm_nonneg f) hk hkn hkb hhom probe
    (C.clockClassProbe_abs_le Q z₀ hz₀ f)
  refine ⟨p, hpt, ?_, ?_, hconc, hlip⟩
  · exact tendsto_finiteClassLegalPressure_div_of_nested (C.clockClassAllowed Q) hnested
      q (by omega) (α : Measure _) (β : Measure _) kin probe p hpt
  · intro T hT
    exact tendstoUniformlyOn_finiteClassLegalScalePressure_of_nested (C.clockClassAllowed Q)
      hnested q (α : Measure _) (β : Measure _) (mul_nonneg hfactor hK) (norm_nonneg f)
      hk hkb probe (C.clockClassProbe_abs_le Q z₀ hz₀ f) hpt hT

end OTSelector.Reconstruction
