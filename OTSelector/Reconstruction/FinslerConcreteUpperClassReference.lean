import OTSelector.Probability.FiniteClassThinning
import OTSelector.Reconstruction.FinslerConcreteUpperClassMass
import OTSelector.Probability.WeightedMarkNormalization

/-!
Exact finite frozen-cell references retain original measurable spatial cells.
Positive retained classes use their actual in-bin clock kernels; zero classes
need no in-bin fallback. Both raw and normalized label/class laws are exact
products. No claim of a uniform full-cube spatial law is used here.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {Z X I : Type*} [MeasurableSpace Z] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Class observation is exact even with arbitrary fallbacks in zero classes;
only classes with positive retained weights need positive actual bin mass. -/
theorem frozenClassRetainedKernel_map_class_ae
    (μ : Measure Z) (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)]
    (B : I → Set X) (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X)
    (classify : X → I) (hm : Measurable classify)
    (hclass : ∀ i x, x ∈ B i → classify x = i) (p : I → ℝ≥0∞)
    (hpositive : ∀ᵐ z ∂μ, ∀ i, p i ≠ 0 → κ z (B i) ≠ 0) :
    (frozenClassRetainedKernel κ B hB fallback p).map classify =ᵐ[μ]
      Kernel.const Z (∑ i, p i • Measure.dirac i) := by
  classical
  filter_upwards [hpositive] with z hz
  rw [Kernel.map_apply _ hm]
  simp only [frozenClassRetainedKernel, sum_apply, Kernel.coe_mk, Kernel.const_apply]
  rw [Measure.map_finset_sum' hm.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.map_smul]
  by_cases hp : p i = 0
  · simp only [hp, zero_smul]
  · congr 1
    have heq : classify =ᵐ[normalizedActualBinKernel κ (B i) (hB i) (fallback i) z]
        (fun _ ↦ i) :=
      (normalizedActualBinKernel_supported_of_mass_ne_zero κ (B i) (hB i)
        (fallback i) z (hz i hp)).mono (fun x hx ↦ hclass i x hx)
    rw [Measure.map_congr heq, Measure.map_const, measure_univ, one_smul]

/-- The actual retained raw population has an exact product class observation
on its original spatial cell, with no positivity requirement on zero classes. -/
theorem frozenClassRetainedKernel_original_cell_law
    (μ : Measure Z) [SFinite μ] (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)]
    (B : I → Set X) (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X)
    (classify : X → I) (hm : Measurable classify)
    (hclass : ∀ i x, x ∈ B i → classify x = i) (p : I → ℝ≥0∞) (hp : ∀ i, p i ≠ ∞)
    (hpositive : ∀ᵐ z ∂μ, ∀ i, p i ≠ 0 → κ z (B i) ≠ 0) :
    (μ ⊗ₘ frozenClassRetainedKernel κ B hB fallback p).map (Prod.map id classify) =
      μ.prod (∑ i, p i • Measure.dirac i) := by
  haveI := frozenClassRetainedKernel_isFinite κ B hB fallback p hp
  haveI : ∀ i, IsFiniteMeasure (p i • Measure.dirac i) := fun i ↦
    ⟨by simpa [Measure.smul_apply] using (hp i).lt_top⟩
  rw [← Measure.compProd_map hm,
    Measure.compProd_congr (frozenClassRetainedKernel_map_class_ae μ κ B hB fallback
      classify hm hclass p hpositive), Measure.compProd_const]

/-- Pointwise class domination gives domination of the actual original
label-clock population before any observation or normalization. -/
theorem frozenClassRetainedKernel_original_cell_le
    (μ : Measure Z) [SFinite μ] (κ : Kernel Z X) [IsSFiniteKernel κ]
    [∀ z, IsFiniteMeasure (κ z)]
    (B : I → Set X) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (fallback : I → X)
    (p : I → ℝ≥0∞) (hp : ∀ i, p i ≠ ∞)
    (d : Z → ℝ) (hd : Measurable d)
    (hdom : ∀ᵐ z ∂μ, ∀ i, p i ≤ ENNReal.ofReal (d z) * κ z (B i)) :
    μ ⊗ₘ frozenClassRetainedKernel κ B hB fallback p ≤ μ ⊗ₘ classWeightedKernel d κ := by
  haveI := frozenClassRetainedKernel_isFinite κ B hB fallback p hp
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.compProd_apply hA, Measure.compProd_apply hA]
  apply lintegral_mono_ae
  filter_upwards [hdom] with z hz
  rw [classWeightedKernel_apply d hd κ z]
  exact frozenClassRetainedKernel_le κ B hB hdisj fallback p z hz _

/-- Normalizing an original finite product normalizes its two factors. -/
theorem normalizedFiniteLaw_prod_eq {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Z) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν] :
    normalizedFiniteLaw (μ.prod ν) = (normalizedFiniteLaw μ).prod (normalizedFiniteLaw ν) := by
  have hmass : (μ.prod ν).real univ = μ.real univ * ν.real univ := by
    rw [measureReal_def, ← univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
    rfl
  simp only [normalizedFiniteLaw, hmass, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr measureReal_nonneg),
    Real.coe_toNNReal _ (inv_nonneg.mpr (mul_nonneg measureReal_nonneg measureReal_nonneg))]
  rw [mul_inv]
  ring

/-- The normalized retained class law is exactly the normalized original
spatial-cell law times the frozen finite class law. -/
theorem frozenClassRetainedKernel_normalized_original_cell_law
    (μ : Measure Z) [IsFiniteMeasure μ] (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)]
    (B : I → Set X) (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X)
    (classify : X → I) (hm : Measurable classify)
    (hclass : ∀ i x, x ∈ B i → classify x = i) (p : I → ℝ≥0∞) (hp : ∀ i, p i ≠ ∞)
    (hpositive : ∀ᵐ z ∂μ, ∀ i, p i ≠ 0 → κ z (B i) ≠ 0) :
    (normalizedFiniteLaw (μ ⊗ₘ frozenClassRetainedKernel κ B hB fallback p)).map
        (Prod.map id classify) =
      (normalizedFiniteLaw μ).prod (normalizedFiniteLaw (∑ i, p i • Measure.dirac i)) := by
  haveI := frozenClassRetainedKernel_isFinite κ B hB fallback p hp
  haveI : ∀ i, IsFiniteMeasure (p i • Measure.dirac i) := fun i ↦
    ⟨by simpa [Measure.smul_apply] using (hp i).lt_top⟩
  let raw := μ ⊗ₘ frozenClassRetainedKernel κ B hB fallback p
  let observe : Z × X → Z × I := Prod.map id classify
  have hmeas : Measurable observe := measurable_id.prodMap hm
  have hmass : (raw.map observe).real univ = raw.real univ := by
    simp only [measureReal_def, Measure.map_apply hmeas MeasurableSet.univ, preimage_univ]
  have hnormalize : (normalizedFiniteLaw raw).map observe = normalizedFiniteLaw (raw.map observe) := by
    simp only [normalizedFiniteLaw, hmass, Measure.map_smul]
  rw [hnormalize, frozenClassRetainedKernel_original_cell_law μ κ B hB fallback
    classify hm hclass p hp hpositive, normalizedFiniteLaw_prod_eq]


end OTSelector.Reconstruction

open Manifold OTSelector.Geometry
open scoped Topology ContDiff
namespace OTSelector.Reconstruction

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

/-- The same actual finite cover controls reference-dependent class tolerances
and relative original Haar intensity. The whole-line test is an extra finite
observable, so no pointwise continuity of raw clock densities is needed. -/
theorem PopulationLocalPressureCore.exists_finite_clockClass_mass_intensity_cover
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {I : Type*} [Fintype I]
    (B : I → Set ℝ) (hB : ∀ c, MeasurableSet (B c))
    (tolerance : (ℚ → M) → ℝ)
    (htolerance : ∀ z ∈ (D.haar.continuous.coefficient i).roots, 0 < tolerance z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (centers : Set (ℚ → M)) (U : (ℚ → M) → Set (ℚ → M)),
      centers.Finite ∧ centers ⊆ (D.haar.continuous.coefficient i).roots ∧
      (D.haar.continuous.coefficient i).roots ⊆ ⋃ z ∈ centers, U z ∧
      ∀ z₀ ∈ centers, IsOpen (U z₀) ∧ z₀ ∈ U z₀ ∧
        ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U z₀,
          |D.rootIntensity i z - D.rootIntensity i z₀| < ε * D.rootIntensity i z₀ ∧
          ∀ color c, |D.rootWeightedClockBinMass i color (B c) z -
            D.rootWeightedClockBinMass i color (B c) z₀| < tolerance z₀ := by
  classical
  let C := D.haar.continuous.coefficient i
  have hdpos : ∀ z ∈ C.roots, 0 < D.rootIntensity i z := by
    intro z hz
    have hzI : z ∈ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
    exact (D.haar.intensity i).lower_pos.trans_le
      ((D.haar.intensity i).bounds _ (mem_image_of_mem _ hzI)).1
  let tests : Option I → Set ℝ := fun c ↦ match c with
    | none => univ
    | some j => B j
  have hm : ∀ c, MeasurableSet (tests c) := by
    intro c
    cases c with
    | none => exact MeasurableSet.univ
    | some j => exact hB j
  obtain ⟨centers, U, hfinite, hsub, hcover, hclose⟩ :=
    D.exists_finite_clockClass_mass_cover i tests hm
      (fun z ↦ min (tolerance z) (ε * D.rootIntensity i z))
      (fun z hz ↦ lt_min (htolerance z hz) (mul_pos hε (hdpos z hz)))
  have hwhole (z : ℚ → M) : D.rootWeightedClockBinMass i 0 univ z = D.rootIntensity i z := by
    simp only [rootWeightedClockBinMass, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]
  refine ⟨centers, U, hfinite, hsub, hcover, fun z₀ hz₀ ↦
    ⟨(hclose z₀ hz₀).1, (hclose z₀ hz₀).2.1, fun z hz ↦ ?_⟩⟩
  constructor
  · have h := (hclose z₀ hz₀).2.2 z hz 0 none
    change |D.rootWeightedClockBinMass i 0 univ z -
      D.rootWeightedClockBinMass i 0 univ z₀| < _ at h
    rw [hwhole, hwhole] at h
    exact h.trans_le (min_le_right _ _)
  · intro color c
    exact ((hclose z₀ hz₀).2.2 z hz color (some c)).trans_le (min_le_left _ _)




/-- Original class accuracy, original relative intensity and arbitrary actual
geometry neighborhoods coexist before finite reference selection. No uniform
positive reference Hall tolerance is required on the compact root set. -/
theorem PopulationLocalPressureCore.exists_finite_clockClass_cover_subordinate
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {I : Type*} [Fintype I]
    (B : I → Set ℝ) (hB : ∀ c, MeasurableSet (B c))
    (tolerance : (ℚ → M) → ℝ)
    (htolerance : ∀ z ∈ (D.haar.continuous.coefficient i).roots, 0 < tolerance z)
    {ε : ℝ} (hε : 0 < ε)
    (V : (ℚ → M) → Set (ℚ → M))
    (hVopen : ∀ z ∈ (D.haar.continuous.coefficient i).roots, IsOpen (V z))
    (hVself : ∀ z ∈ (D.haar.continuous.coefficient i).roots, z ∈ V z) :
    ∃ (centers : Set (ℚ → M)) (U : (ℚ → M) → Set (ℚ → M)),
      centers.Finite ∧ centers ⊆ (D.haar.continuous.coefficient i).roots ∧
      (D.haar.continuous.coefficient i).roots ⊆ ⋃ z ∈ centers, U z ∧
      ∀ z₀ ∈ centers, IsOpen (U z₀) ∧ z₀ ∈ U z₀ ∧ U z₀ ⊆ V z₀ ∧
        ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U z₀,
          |D.rootIntensity i z - D.rootIntensity i z₀| < ε * D.rootIntensity i z₀ ∧
          ∀ color c, |D.rootWeightedClockBinMass i color (B c) z -
            D.rootWeightedClockBinMass i color (B c) z₀| < tolerance z₀ := by
  classical
  let _instActualRefMetric : MetricSpace M := F.metricSpace
  let _instActualRefRootMetric : MetricSpace (ℚ → M) :=
    TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  let C := D.haar.continuous.coefficient i
  have hdpos : ∀ z ∈ C.roots, 0 < D.rootIntensity i z := by
    intro z hz
    have hzI : z ∈ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
    exact (D.haar.intensity i).lower_pos.trans_le
      ((D.haar.intensity i).bounds _ (mem_image_of_mem _ hzI)).1
  let tests : Option I → Set ℝ := fun c ↦ match c with
    | none => univ
    | some j => B j
  have hm : ∀ c, MeasurableSet (tests c) := by
    intro c
    cases c with
    | none => exact MeasurableSet.univ
    | some j => exact hB j
  let profile := fun z (c : Fin 2 × Option I) ↦
    D.rootWeightedClockBinMass i c.1 (tests c.2) z
  have hc : ContinuousOn profile C.roots := continuousOn_pi.mpr fun c ↦
    D.continuousOn_rootWeightedClockBinMass i c.1 (hm c.2)
  let tol := fun z ↦ min (tolerance z) (ε * D.rootIntensity i z)
  have htol : ∀ z ∈ C.roots, 0 < tol z := fun z hz ↦
    lt_min (htolerance z hz) (mul_pos hε (hdpos z hz))
  have hlocal (z₀ : C.roots) : ∃ radius > 0, ∀ z ∈ C.roots,
      dist z z₀.val < radius → ‖profile z - profile z₀.val‖ < tol z₀.val := by
    obtain ⟨radius, hradius, hnear⟩ := Metric.continuousWithinAt_iff.mp
      (hc z₀.val z₀.property) (tol z₀.val) (htol z₀.val z₀.property)
    exact ⟨radius, hradius, fun z hz hdist ↦ by simpa only [dist_eq_norm] using hnear hz hdist⟩
  choose radius hradius hnear using hlocal
  let U := fun z : ℚ → M ↦ if hz : z ∈ C.roots then
    V z ∩ Metric.ball z (radius ⟨z, hz⟩) else ∅
  have hopen : ∀ z ∈ C.roots, IsOpen (U z) := fun z hz ↦ by
    simp only [U, dite_eq_left hz]
    exact (hVopen z hz).inter Metric.isOpen_ball
  have hmem : ∀ z ∈ C.roots, z ∈ U z := fun z hz ↦ by
    simp only [U, dite_eq_left hz]
    exact ⟨hVself z hz, Metric.mem_ball_self (hradius ⟨z, hz⟩)⟩
  obtain ⟨centers, hsub, hfinite, hcover⟩ := C.roots_compact.elim_finite_subcover_image hopen
    (show C.roots ⊆ ⋃ z ∈ C.roots, U z from fun z hz ↦ mem_iUnion₂.mpr ⟨z, hz, hmem z hz⟩)
  refine ⟨centers, U, hfinite, hsub, hcover, fun z₀ hz₀ ↦
    ⟨hopen z₀ (hsub hz₀), hmem z₀ (hsub hz₀), ?_, ?_⟩⟩
  · intro z hz
    have hz' : z ∈ V z₀ ∩ Metric.ball z₀ (radius ⟨z₀, hsub hz₀⟩) := by
      simpa only [U, dite_eq_left (hsub hz₀)] using hz
    exact hz'.1
  · intro z hz
    have hz' : z ∈ V z₀ ∩ Metric.ball z₀ (radius ⟨z₀, hsub hz₀⟩) := by
      simpa only [U, dite_eq_left (hsub hz₀)] using hz.2
    have hnorm := hnear ⟨z₀, hsub hz₀⟩ z hz.1 hz'.2
    have hcomponent (color : Fin 2) (c : Option I) :
        |D.rootWeightedClockBinMass i color (tests c) z -
          D.rootWeightedClockBinMass i color (tests c) z₀| < tol z₀ :=
      (show |D.rootWeightedClockBinMass i color (tests c) z -
          D.rootWeightedClockBinMass i color (tests c) z₀| ≤ ‖profile z - profile z₀‖ by
        simpa only [profile, Pi.sub_apply, Real.norm_eq_abs] using
          (norm_le_pi_norm (profile z - profile z₀) (color, c))).trans_lt hnorm
    constructor
    · have h := hcomponent 0 none
      change |D.rootWeightedClockBinMass i 0 univ z -
        D.rootWeightedClockBinMass i 0 univ z₀| < _ at h
      simp only [rootWeightedClockBinMass, measureReal_def, measure_univ,
        ENNReal.toReal_one, mul_one] at h
      exact h.trans_le (min_le_right _ _)
    · intro color c
      exact (hcomponent color (some c)).trans_le (min_le_left _ _)


/-- Each actual reference may choose its own finite clock bins and tolerance
before neighborhoods and finite selection. The final finite physical cells can
therefore retain different class types without refining their Hall tests. -/
theorem PopulationLocalPressureCore.exists_finite_dependent_clockClass_cover
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count)
    (I : (D.haar.continuous.coefficient i).roots → Type*) [∀ ref, Fintype (I ref)]
    (B : ∀ ref, I ref → Set ℝ) (hB : ∀ ref c, MeasurableSet (B ref c))
    (tolerance : (D.haar.continuous.coefficient i).roots → ℝ)
    (htolerance : ∀ ref, 0 < tolerance ref) {ε : ℝ} (hε : 0 < ε)
    (V : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hVopen : ∀ ref, IsOpen (V ref)) (hVself : ∀ ref, ref.val ∈ V ref) :
    ∃ (centers : Finset (D.haar.continuous.coefficient i).roots)
      (U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M)),
      (D.haar.continuous.coefficient i).roots ⊆ ⋃ ref ∈ centers, U ref ∧
      ∀ ref ∈ centers, IsOpen (U ref) ∧ ref.val ∈ U ref ∧ U ref ⊆ V ref ∧
        ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
          |D.rootIntensity i z - D.rootIntensity i ref.val| < ε * D.rootIntensity i ref.val ∧
          ∀ color c, |D.rootWeightedClockBinMass i color (B ref c) z -
            D.rootWeightedClockBinMass i color (B ref c) ref.val| < tolerance ref := by
  classical
  let _instDependentRefMetric : MetricSpace M := F.metricSpace
  let _instDependentRootMetric : MetricSpace (ℚ → M) :=
    TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  let C := D.haar.continuous.coefficient i
  have hdpos (ref : C.roots) : 0 < D.rootIntensity i ref.val := by
    have hzI : ref.val ∈ (D.haar.intensity i).roots := by
      rw [D.haar.intensity_roots]
      exact ref.property
    exact (D.haar.intensity i).lower_pos.trans_le
      ((D.haar.intensity i).bounds _ (mem_image_of_mem _ hzI)).1
  let tests := fun ref : C.roots ↦ fun c : Option (I ref) ↦ match c with
    | none => univ
    | some j => B ref j
  have hm : ∀ ref c, MeasurableSet (tests ref c) := by
    intro ref c
    cases c with
    | none => exact MeasurableSet.univ
    | some j => exact hB ref j
  let profile := fun ref : C.roots ↦ fun z (c : Fin 2 × Option (I ref)) ↦
    D.rootWeightedClockBinMass i c.1 (tests ref c.2) z
  have hc (ref : C.roots) : ContinuousOn (profile ref) C.roots :=
    continuousOn_pi.mpr fun c ↦ D.continuousOn_rootWeightedClockBinMass i c.1 (hm ref c.2)
  let tol := fun ref : C.roots ↦ min (tolerance ref) (ε * D.rootIntensity i ref.val)
  have htol (ref : C.roots) : 0 < tol ref :=
    lt_min (htolerance ref) (mul_pos hε (hdpos ref))
  have hlocal (ref : C.roots) : ∃ radius > 0, ∀ z ∈ C.roots,
      dist z ref.val < radius → ‖profile ref z - profile ref ref.val‖ < tol ref := by
    obtain ⟨radius, hradius, hnear⟩ := Metric.continuousWithinAt_iff.mp
      (hc ref ref.val ref.property) (tol ref) (htol ref)
    exact ⟨radius, hradius, fun z hz hdist ↦ by simpa only [dist_eq_norm] using hnear hz hdist⟩
  choose radius hradius hnear using hlocal
  let U := fun ref : C.roots ↦ V ref ∩ Metric.ball ref.val (radius ref)
  have hopen (ref : C.roots) : IsOpen (U ref) := (hVopen ref).inter Metric.isOpen_ball
  have hmem (ref : C.roots) : ref.val ∈ U ref :=
    ⟨hVself ref, Metric.mem_ball_self (hradius ref)⟩
  obtain ⟨centers, hcover⟩ := C.roots_compact.elim_finite_subcover U hopen
    (show C.roots ⊆ ⋃ ref, U ref from fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, hmem ⟨z, hz⟩⟩)
  refine ⟨centers, U, hcover, fun ref _ ↦ ⟨hopen ref, hmem ref, inter_subset_left, ?_⟩⟩
  intro z hz
  have hnorm := hnear ref z hz.1 hz.2.2
  have hcomponent (color : Fin 2) (c : Option (I ref)) :
      |D.rootWeightedClockBinMass i color (tests ref c) z -
        D.rootWeightedClockBinMass i color (tests ref c) ref.val| < tol ref :=
    (show |D.rootWeightedClockBinMass i color (tests ref c) z -
        D.rootWeightedClockBinMass i color (tests ref c) ref.val| ≤
          ‖profile ref z - profile ref ref.val‖ by
      simpa only [profile, Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm (profile ref z - profile ref ref.val) (color, c))).trans_lt hnorm
  constructor
  · have h := hcomponent 0 none
    change |D.rootWeightedClockBinMass i 0 univ z -
      D.rootWeightedClockBinMass i 0 univ ref.val| < _ at h
    simp only [rootWeightedClockBinMass, measureReal_def, measure_univ,
      ENNReal.toReal_one, mul_one] at h
    exact h.trans_le (min_le_right _ _)
  · intro color c
    exact (hcomponent color (some c)).trans_le (min_le_left _ _)


/-- Actual finite disjoint measurable root cells retain their own reference
clock classes and geometry neighborhoods. Their union is exactly the original
coefficient core, so no original root mass is lost by finite selection. -/
theorem PopulationLocalPressureCore.exists_finite_dependent_clockClass_cells
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count)
    (I : (D.haar.continuous.coefficient i).roots → Type*) [∀ ref, Fintype (I ref)]
    (B : ∀ ref, I ref → Set ℝ) (hB : ∀ ref c, MeasurableSet (B ref c))
    (tolerance : (D.haar.continuous.coefficient i).roots → ℝ)
    (htolerance : ∀ ref, 0 < tolerance ref) {ε : ℝ} (hε : 0 < ε)
    (V : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hVopen : ∀ ref, IsOpen (V ref)) (hVself : ∀ ref, ref.val ∈ V ref) :
    ∃ (N : ℕ) (reference : Fin N → (D.haar.continuous.coefficient i).roots)
      (cell : Fin N → Set (ℚ → M)),
      (∀ j, MeasurableSet (cell j)) ∧ Pairwise (fun j k ↦ Disjoint (cell j) (cell k)) ∧
      (⋃ j, cell j) = (D.haar.continuous.coefficient i).roots ∧
      ∀ j, cell j ⊆ (D.haar.continuous.coefficient i).roots ∩ V (reference j) ∧
        ∀ z ∈ cell j,
          |D.rootIntensity i z - D.rootIntensity i (reference j).val| <
            ε * D.rootIntensity i (reference j).val ∧
          ∀ color c, |D.rootWeightedClockBinMass i color (B (reference j) c) z -
            D.rootWeightedClockBinMass i color (B (reference j) c) (reference j).val| <
              tolerance (reference j) := by
  classical
  let _instClassCellMetric : MetricSpace M := F.metricSpace
  let _instClassCellProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instClassCellPolish : PolishSpace M := inferInstance
  let _instClassCellBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨centers, U, hcover, hlocal⟩ :=
    D.exists_finite_dependent_clockClass_cover i I B hB tolerance htolerance hε V hVopen hVself
  let C := D.haar.continuous.coefficient i
  let Ref := {ref : C.roots // ref ∈ centers}
  let e : Fin (Fintype.card Ref) ≃ Ref := (Fintype.equivFin Ref).symm
  let reference := fun j : Fin (Fintype.card Ref) ↦ (e j).val
  let s := fun j : Fin (Fintype.card Ref) ↦ C.roots ∩ U (reference j)
  have hs : ∀ j, MeasurableSet (s j) := fun j ↦ C.roots_compact.measurableSet.inter
    ((hlocal (reference j) (e j).property).1.measurableSet)
  have hunion : (⋃ j, s j) = C.roots := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact hj.1
    · intro z hz
      obtain ⟨ref, href, hzU⟩ := mem_iUnion₂.mp (hcover hz)
      refine mem_iUnion.mpr ⟨e.symm ⟨ref, href⟩, hz, ?_⟩
      simpa only [reference, Equiv.apply_symm_apply] using hzU
  refine ⟨Fintype.card Ref, reference, disjointed s, ?_, disjoint_disjointed s,
    iUnion_disjointed.trans hunion, ?_⟩
  · intro j
    rw [disjointed_eq_inter_compl]
    exact (hs j).inter (MeasurableSet.iInter fun k ↦
      MeasurableSet.iInter fun _ ↦ (hs k).compl)
  · intro j
    have hsub : disjointed s j ⊆ s j := disjointed_subset s j
    refine ⟨fun z hz ↦ ⟨(hsub hz).1, ?_⟩, fun z hz ↦ ?_⟩
    · exact (hlocal (reference j) (e j).property).2.2.1 (hsub hz).2
    · exact (hlocal (reference j) (e j).property).2.2.2 z (hsub hz)

end OTSelector.Reconstruction
