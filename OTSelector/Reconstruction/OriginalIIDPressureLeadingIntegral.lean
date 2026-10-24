import OTSelector.Reconstruction.OriginalIIDPressureReferenceRefinement

/-!
# Actual original finite leading pressures and their original root integral

Pressure-accurate original clock partitions are kept while physical neighborhoods
are attached. Finite reference cells use the same original Haar weights and retained
conditional laws; their leading sum is compared with the actual retained pressure.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞} {Good : (ℚ → M) → Prop}

/-- Exact physical compatibility of given original clock partitions and root
neighborhoods. All comparisons use the original seed coefficient and physical probe. -/
def PopulationLocalPressureCore.originalClockClassGeometryOn
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {width : ℝ}
    (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I width)
    (U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (A B : Set M) (f : M × M →ᵇ ℝ) (ε probeError : ℝ) : Prop :=
  let C := D.haar.continuous.coefficient i
  (∀ ref, IsOpen (U ref) ∧ ref.val ∈ U ref) ∧
  (∀ ref, ∀ z ∈ C.roots ∩ U ref, ∀ z' ∈ C.roots ∩ U ref,
    ∀ s ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
    ∀ t ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1,
      s < t → D.corePoint i (z,s) ∈ A → D.corePoint i (z',t) ∈ B →
      (s,t) ∈ C.window.region) ∧
  ∀ ref, ∀ z ∈ C.roots ∩ U ref, ∀ z' ∈ C.roots ∩ U ref,
  ∀ j k, C.clockClassAllowed (Q ref) j k → ∀ s ∈ (Q ref).cell j,
  ∀ t ∈ (Q ref).cell k,
  D.corePoint i (z,s) ∈ A → D.corePoint i (z',t) ∈ B →
    let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let v := (finBasis ℝ S.covector.ker).equivFun (R z' - R z)
    (s,t) ∈ C.window.region ∧
    |populationSeedPairDeficit S (s,t) (R z,R z') -
      C.clockClassKinetic (Q ref) ref.val j k v| ≤
      (3 * ε + 2 * ε ^ 2) * C.clockClassKinetic (Q ref) ref.val j k v ∧
    |f (D.corePoint i (z,s),D.corePoint i (z',t)) -
      C.clockClassProbe (Q ref) ref.val ref.property f j k| ≤ 2 * probeError

/-- The real original physical neighborhoods can be attached to ANY already
chosen fine partitions carrying their original resampling and strict endpoint data.
In particular, no second clock partition replaces a pressure-accurate one. -/
theorem PopulationLocalPressureCore.exists_given_clockClass_geometry
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    {I : Set ℝ} {width : ℝ} {ε probeError : ℝ}
    (hε : 0 < ε) (hprobe : 0 < probeError)
    (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I width)
    (hRdata : ∀ ref, Nonempty (OriginalRangeClockResamplingData
      (D.haar.continuous.coefficient i) (Q ref) ref.val ref.property f ε probeError))
    (hfull : ∀ ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k →
      ∀ s ∈ (Q ref).cell j, ∀ t ∈ (Q ref).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧ s < t) :
    ∃ U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M),
      D.originalClockClassGeometryOn i Q U A B f ε probeError := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  obtain ⟨radius, hradius, hregion⟩ := D.exists_original_clock_region_radius hF i hgap hsep hscreen
  obtain ⟨U, hU, hgeometry⟩ := D.exists_original_pair_geometry_neighborhoods hF hcomplete hu
    ha hinj i f f.continuous hε hprobe hradius
  refine ⟨fun ref ↦ U ref.val, fun ref ↦ hU ref.val, ?_, ?_⟩
  · intro ref z hz z' hz' s hs t ht hst hA hB
    exact hregion z hz.1 z' hz'.1 s hs t ht
      (hgeometry ref.val ref.property z hz z' hz').1 hst hA hB
  intro ref z hz z' hz' j k hjk s hs t ht hA hB
  have hR := Classical.choice (hRdata ref)
  let x : I := ⟨s,(Q ref).subset j hs⟩
  let y : I := ⟨t,(Q ref).subset k ht⟩
  have hx : (Q ref).rangeClassify x = j := (Q ref).rangeClassify_eq_of_mem j hs
  have hy : (Q ref).rangeClassify y = k := (Q ref).rangeClassify_eq_of_mem k ht
  have hallowed : C.clockClassAllowed (Q ref)
      ((Q ref).rangeClassify x) ((Q ref).rangeClassify y) := by rw [hx,hy]; exact hjk
  have hkin (v) : |matrixQuadratic (C.matrix ref.val (s,t)) v -
      C.clockClassKinetic (Q ref) ref.val j k v| ≤
      ε * C.clockClassKinetic (Q ref) ref.val j k v := by
    simpa only [OriginalPopulationCoefficientCore.originalMaskedClockKinetic,
      hallowed, ↓reduceIte, hx, hy, hjk] using hR.relative x y hallowed v
  have hprobe' : |originalReferenceClockProbe C ref.val ref.property f (s,t) -
      C.clockClassProbe (Q ref) ref.val ref.property f j k| ≤ probeError := by
    simpa only [OriginalPopulationCoefficientCore.originalRangeClockProbe,hx,hy] using
      hR.probe_error x y hallowed
  obtain ⟨hsI,htI,hst⟩ := hfull ref j k hjk s hs t ht
  obtain ⟨hdiam,hcost,hphysicalProbe⟩ := hgeometry ref.val ref.property z hz z' hz'
  have hp := hregion z hz.1 z' hz'.1 s hsI t htI hdiam hst hA hB
  refine ⟨hp, ?_, ?_⟩
  · let S := (P C.seedIndex).seed
    let R := populationSeedRootLabelValue S a
    let v := (finBasis ℝ S.covector.ker).equivFun (R z' - R z)
    let raw := matrixQuadratic (C.matrix ref.val (s,t)) v
    let frozen := C.clockClassKinetic (Q ref) ref.val j k v
    have hraw : raw ≤ (1 + ε) * frozen := by
      have hh := (abs_le.mp (hkin v)).2
      dsimp only [raw,frozen]
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ 2 * ε)
    have hcost' := hcost (s,t) hp
    have htri := abs_sub_le (populationSeedPairDeficit S (s,t) (R z,R z')) raw frozen
    have hbin := hkin v
    change |populationSeedPairDeficit S (s,t) (R z,R z') - frozen| ≤
      (3 * ε + 2 * ε ^ 2) * frozen
    nlinarith only [hscaled,hcost',htri,hbin]
  · have href : originalReferenceClockProbe C ref.val ref.property f (s,t) =
        f (D.corePoint i (ref.val,s),D.corePoint i (ref.val,t)) := by
      dsimp only [originalReferenceClockProbe,PopulationLocalPressureCore.corePoint]
      rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
        ⟨ref.val,C.roots_subset_piece ref.property⟩]
    have hphysical := hphysicalProbe s hsI t htI
    rw [← href] at hphysical
    have htri := abs_sub_le (f (D.corePoint i (z,s),D.corePoint i (z',t)))
      (originalReferenceClockProbe C ref.val ref.property f (s,t))
      (C.clockClassProbe (Q ref) ref.val ref.property f j k)
    linarith

/-- Enlarging the requested approximation errors keeps the SAME actual
resampling certificate and clock partition. -/
def OriginalRangeClockResamplingData.monoAccuracy
    {C : OriginalPopulationCoefficientCore P a κ (μ.map a) μ ν δ}
    {I : Set ℝ} {width : ℝ} {Q : FiniteScalarBins I width}
    {z : ℚ → M} {hz : z ∈ C.roots} {f : M × M →ᵇ ℝ}
    {ε probeError ε' probeError' : ℝ}
    (Rdata : OriginalRangeClockResamplingData C Q z hz f ε probeError)
    (hε : ε ≤ ε') (hprobe : probeError ≤ probeError') :
    OriginalRangeClockResamplingData C Q z hz f ε' probeError' where
  kineticConstant := Rdata.kineticConstant
  kineticConstant_nonneg := Rdata.kineticConstant_nonneg
  kinetic_nonneg := Rdata.kinetic_nonneg
  kinetic_bound := Rdata.kinetic_bound
  relative := fun x y hxy v ↦ (Rdata.relative x y hxy v).trans
    (mul_le_mul_of_nonneg_right hε
      (C.clockClassKinetic_nonneg Q z hz (Q.rangeClassify x) (Q.rangeClassify y) v))
  probe_error := fun x y hxy ↦ (Rdata.probe_error x y hxy).trans hprobe

/-- The actual original coordinate intensity is continuous with positive finite
bounds on every stored coefficient piece, including an empty piece. -/
theorem PopulationLocalPressureCore.coordinate_intensity_continuous_bounds
    [∀ j, (κ j).IsAddHaarMeasure]
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) :
    let theta := originalSeedCoordinateIntensity P a κ (μ.map a)
      (D.haar.continuous.coefficient i).seedIndex
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
      ContinuousOn theta (D.haar.continuous.coefficient i).roots ∧
      ∀ z ∈ (D.haar.continuous.coefficient i).roots, L ≤ theta z ∧ theta z ≤ U := by
  let C := D.haar.continuous.coefficient i
  let I := D.haar.intensity i
  let c : ℝ := originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex)
  have hc : 0 < c := by
    exact_mod_cast (originalSeedCoordinateHaarFactor_pos (P C.seedIndex).seed (κ C.seedIndex))
  have hroots : I.roots = C.roots := D.haar.intensity_roots i
  have hdensity : ContinuousOn (D.rootIntensity i) C.roots := by
    apply I.continuous_density.comp (hroots ▸ I.continuous_label)
    intro z hz
    exact mem_image_of_mem _ (hroots.symm ▸ hz)
  have hU : 0 < I.upper := I.lower_pos.trans_le I.lower_le_upper
  refine ⟨c * I.lower, c * I.upper, mul_pos hc I.lower_pos, mul_pos hc hU,
    hdensity.const_mul c, ?_⟩
  intro z hz
  have hb := I.bounds _ (mem_image_of_mem _ (hroots.symm ▸ hz))
  exact ⟨mul_le_mul_of_nonneg_left hb.1 hc.le,
    mul_le_mul_of_nonneg_left hb.2 hc.le⟩

/-- A reference pressure error and oscillation of theta*p control the SAME
frozen leading readout at neighboring roots. No sign assumption on p is needed. -/
theorem weighted_reference_le_of_error_and_oscillation
    {L U thetaRef theta pRef p raw tolerance : ℝ}
    (hL : 0 < L) (hU : 0 < U) (hRef : L ≤ thetaRef) (hRefU : thetaRef ≤ U)
    (hTheta : L ≤ theta) (htolerance : 0 < tolerance)
    (herror : thetaRef⁻¹ * raw ≤ pRef + L * tolerance / (2 * U))
    (hosc : |theta * p - thetaRef * pRef| < L * tolerance / 2) :
    theta⁻¹ * raw ≤ p + tolerance := by
  have href0 : 0 < thetaRef := hL.trans_le hRef
  have htheta0 : 0 < theta := hL.trans_le hTheta
  have herror' : raw / thetaRef ≤ pRef + L * tolerance / (2 * U) := by
    simpa only [div_eq_mul_inv, mul_comm] using herror
  have hraw := (div_le_iff₀ href0).mp herror'
  have hα : 0 ≤ L * tolerance / (2 * U) := by positivity
  have hscale := mul_le_mul_of_nonneg_right hRefU hα
  have hcancel : U * (L * tolerance / (2 * U)) = L * tolerance / 2 := by
    field_simp
  have hosc' := (abs_lt.mp hosc).1
  have htol := mul_le_mul_of_nonneg_right hTheta htolerance.le
  have htarget : raw ≤ (p + tolerance) * theta := by nlinarith
  have hh := (div_le_iff₀ htheta0).mpr htarget
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Shrinking only root neighborhoods preserves the actual physical geometry of
exactly the same chosen fine-clock partitions. -/
theorem PopulationLocalPressureCore.originalClockClassGeometryOn_mono
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {width : ℝ}
    {Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I width}
    {U V : (D.haar.continuous.coefficient i).roots → Set (ℚ → M)}
    {A B : Set M} {f : M × M →ᵇ ℝ} {ε probeError : ℝ}
    (h : D.originalClockClassGeometryOn i Q U A B f ε probeError)
    (hV : ∀ ref, IsOpen (V ref) ∧ ref.val ∈ V ref)
    (hsub : ∀ ref, V ref ⊆ U ref) :
    D.originalClockClassGeometryOn i Q V A B f ε probeError := by
  refine ⟨hV, ?_, ?_⟩
  · intro ref z hz z' hz' s hs t ht hst hA hB
    exact h.2.1 ref z ⟨hz.1,hsub ref hz.2⟩ z' ⟨hz'.1,hsub ref hz'.2⟩
      s hs t ht hst hA hB
  intro ref z hz z' hz' j k hjk s hs t ht hA hB
  exact h.2.2 ref z ⟨hz.1,hsub ref hz.2⟩ z' ⟨hz'.1,hsub ref hz'.2⟩
    j k hjk s hs t ht hA hB

variable [∀ j, (κ j).IsAddHaarMeasure]

/-- The frozen reference value read per unit original root mass at a possibly
different retained root. Only the original inverse intensity varies within a cell. -/
def PopulationLocalPressureCore.originalFrozenReferenceReadout
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    (Q : FiniteScalarBins I gap) (η : ℝ) (pref : ℝ → ℝ) (t : ℝ) (z : ℚ → M) : ℝ :=
  let C := D.haar.continuous.coefficient i
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex z
  let density :=
    (originalSeedCoordinateHaarFactor (P C.seedIndex).seed (κ C.seedIndex) : ℝ) *
      (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap I i ref Q η)).real univ
  theta⁻¹ * density ^ (1-2/(q:ℝ)) * pref (t * density ^ (2/(q:ℝ)))

/-- Pressure-accurate original partitions acquire physical neighborhoods for the
SAME Q. On these neighborhoods their frozen Haar readout is bounded by the actual
retained pressure plus the prescribed tolerance, pointwise at every kept root. -/
theorem PopulationLocalPressureCore.exists_pressure_accurate_geometry_readout
    {I : Set ℝ} (hI : IsCompact I)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {A B : Set M} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (i : Fin D.haar.continuous.count)
    (hscreen : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    (hgood : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      OriginalClockClassPressureReferenceGood γ D hcomplete hδ hδ1 hgap hη f i z)
    (t ε probeError tolerance : ℝ) (hε : 0 < ε) (hprobe : 0 < probeError)
    (htolerance : 0 < tolerance)
    (hp : ContinuousOn (originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t)
      (D.haar.continuous.coefficient i).roots) :
    ∃ (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
      (U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
      (pref : (D.haar.continuous.coefficient i).roots → ℝ → ℝ),
      D.originalClockClassGeometryOn i Q U A B f ε probeError ∧
      (∀ ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k →
        ∀ x ∈ (Q ref).cell j, ∀ y ∈ (Q ref).cell k,
          x ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
            (D.haar.continuous.coefficient i).window.val.2.1 ∧
          y ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
            (D.haar.continuous.coefficient i).window.val.2.1 ∧ x < y) ∧
      (∀ ref s, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ref (Q ref)
        hη hgap.le hδ hδ1 f R s) atTop (𝓝 (pref ref s))) ∧
      ∀ ref, ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
        D.originalFrozenReferenceReadout γ i ref (Q ref) η (pref ref) t z ≤
          originalRetainedFinslerRootPressure P a κ (μ.map a)
            (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ)
            (fun _ _ ↦ η) b f 0 t z + tolerance := by
  let C := D.haar.continuous.coefficient i
  let p := originalRetainedFinslerRootPressure P a κ (μ.map a)
    (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t
  let theta := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex
  obtain ⟨L,U,hL,hU,htheta,hbounds⟩ := D.coordinate_intensity_continuous_bounds i
  have hα : 0 < L * tolerance / (2 * U) := by positivity
  obtain ⟨Q, select, pref, hmodel⟩ := D.exists_pressure_accurate_reference_models hI γ hF
    hcomplete hu ha hinj hδ hδ1 hgap hη f i hgood t ε probeError
      (L * tolerance / (2 * U)) hε hprobe hα
  have hRdata ref : Nonempty (OriginalRangeClockResamplingData C (Q ref)
      ref.val ref.property f ε probeError) :=
    ⟨(Classical.choice (hmodel ref).2.2.1).monoAccuracy
      (hmodel ref).1.le (hmodel ref).2.1.le⟩
  have hfull ref := (hmodel ref).2.2.2.1
  obtain ⟨W,hW⟩ := D.exists_given_clockClass_geometry hF hcomplete hu ha hinj i f hgap hsep
    hscreen hε hprobe Q hRdata hfull
  obtain ⟨V,hV,hosc⟩ := exists_open_pressure_reference_neighborhoods (htheta.mul hp)
    (show 0 < L * tolerance / 2 by positivity)
  let W' := fun ref ↦ W ref ∩ V ref
  have hW' : D.originalClockClassGeometryOn i Q W' A B f ε probeError :=
    D.originalClockClassGeometryOn_mono i hW
      (fun ref ↦ ⟨(hW.1 ref).1.inter (hV ref).1,⟨(hW.1 ref).2,(hV ref).2⟩⟩)
      (fun _ ↦ inter_subset_left)
  refine ⟨Q,W',pref,hW',hfull,fun ref ↦ (hmodel ref).2.2.2.2.1,?_⟩
  intro ref z hz
  have hRef := hbounds ref.val ref.property
  have hTheta := hbounds z hz.1
  have herror := (hmodel ref).2.2.2.2.2.le
  have hosc' := hosc ref z ⟨hz.1,hz.2.2⟩
  simp only [PopulationLocalPressureCore.originalFrozenReferenceReadout, mul_assoc]
  apply weighted_reference_le_of_error_and_oscillation hL hU hRef.1 hRef.2 hTheta.1
    htolerance _ (by simpa only [Pi.mul_apply] using hosc')
  simpa only [PopulationLocalPressureCore.originalWeightedReferencePressure,mul_assoc] using herror

/-- The exact retained reference intensity in the standard original seed basis. -/
def PopulationLocalPressureCore.originalReferenceCoordinateDensity
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    (Q : FiniteScalarBins I gap) (η : ℝ) : ℝ≥0 :=
  originalSeedCoordinateHaarFactor (P (D.haar.continuous.coefficient i).seedIndex).seed
    (κ (D.haar.continuous.coefficient i).seedIndex) *
      (clockClassPairMeasure (D.originalWindowReferenceWeights γ gap I i ref Q η) univ).toNNReal

/-- The actual finite-family leading term, retaining each original coordinate
volume, its genuine Haar factor, retained intensity and rescaled physical tilt. -/
def PopulationLocalPressureCore.originalReferenceFamilyLeadingPressure
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    {Cell : Type*} [Fintype Cell] (index : Cell → Fin D.haar.continuous.count)
    (ref : ∀ c, (D.haar.continuous.coefficient (index c)).roots)
    (cell : Cell → Set (ℚ → M))
    (Q : ∀ i, (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
    (pref : ∀ i, (D.haar.continuous.coefficient i).roots → ℝ → ℝ) (η t : ℝ) : ℝ :=
  ∑ c,
    let C := D.haar.continuous.coefficient (index c)
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let coord := atlasSeedCoord (P C.seedIndex).seed
      (finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL a
    let density := D.originalReferenceCoordinateDensity γ (index c) (ref c)
      (Q (index c) (ref c)) η
    volume.real (coord '' cell c) * (density : ℝ) ^ (1-2/(q:ℝ)) *
      pref (index c) (ref c) (t * (density : ℝ) ^ (2/(q:ℝ)))

private theorem finite_reference_leading_le_integral
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {Cell : Type*} [Fintype Cell] (index : Cell → Fin D.haar.continuous.count)
    (ref : ∀ c, (D.haar.continuous.coefficient (index c)).roots)
    (cell : Cell → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (index c)).roots)
    (hdisj : Pairwise (Disjoint on cell))
    (hcover : (⋃ c, cell c) = D.haar.continuous.population.roots)
    (Q : ∀ i, (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
    (pref : ∀ i, (D.haar.continuous.coefficient i).roots → ℝ → ℝ) (η t tolerance : ℝ)
    {p : (ℚ → M) → ℝ} (hp : IntegrableOn p D.haar.continuous.population.roots (μ.map a))
    (hread : ∀ c, ∀ z ∈ cell c,
      D.originalFrozenReferenceReadout γ (index c) (ref c) (Q (index c) (ref c)) η
        (pref (index c) (ref c)) t z ≤ p z + tolerance) :
    D.originalReferenceFamilyLeadingPressure γ index ref cell Q pref η t ≤
      (∫ z in D.haar.continuous.population.roots, p z ∂μ.map a) +
        tolerance * (μ.map a).real D.haar.continuous.population.roots := by
  let density := fun c ↦ D.originalReferenceCoordinateDensity γ (index c) (ref c)
    (Q (index c) (ref c)) η
  have hsubpop c : cell c ⊆ D.haar.continuous.population.roots := by
    rw [← hcover]
    exact subset_iUnion cell c
  have hI c : IntegrableOn
      (D.originalFrozenReferenceReadout γ (index c) (ref c) (Q (index c) (ref c)) η
        (pref (index c) (ref c)) t) (cell c) (μ.map a) := by
    unfold PopulationLocalPressureCore.originalFrozenReferenceReadout
    exact ((D.integrableOn_inverse_coordinate_intensity hF hcomplete hu ha hinj
      (index c) (hcell c) (hsub c)).mul_const _).mul_const _
  have hIright c : IntegrableOn (fun z ↦ p z + tolerance) (cell c) (μ.map a) :=
    (hp.mono_set (hsubpop c)).add (integrable_const tolerance)
  have hcellEq c :
      let C := D.haar.continuous.coefficient (index c)
      let q := finrank ℝ (P C.seedIndex).seed.covector.ker
      let coord := atlasSeedCoord (P C.seedIndex).seed
        (finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL a
      volume.real (coord '' cell c) * (density c : ℝ) ^ (1-2/(q:ℝ)) *
        pref (index c) (ref c) (t * (density c : ℝ) ^ (2/(q:ℝ))) =
        ∫ z in cell c, D.originalFrozenReferenceReadout γ (index c) (ref c)
          (Q (index c) (ref c)) η (pref (index c) (ref c)) t z ∂μ.map a := by
    have hh := D.original_frozen_cell_pressure_eq_root_integral hF hcomplete hu ha hinj
      (index c) (hcell c) (hsub c) (density c) (pref (index c) (ref c)) t
    simpa only [density, PopulationLocalPressureCore.originalReferenceCoordinateDensity,
      PopulationLocalPressureCore.originalFrozenReferenceReadout, NNReal.coe_mul,
      ENNReal.toReal, measureReal_def] using hh
  have hle c :
      (∫ z in cell c, D.originalFrozenReferenceReadout γ (index c) (ref c)
        (Q (index c) (ref c)) η (pref (index c) (ref c)) t z ∂μ.map a) ≤
      ∫ z in cell c, p z + tolerance ∂μ.map a :=
    integral_mono_ae (hI c) (hIright c)
      ((ae_restrict_mem (hcell c)).mono (fun z hz ↦ hread c z hz))
  have hsum := integral_iUnion_fintype hcell hdisj hIright
  rw [hcover] at hsum
  have hIR : IntegrableOn (fun z ↦ p z + tolerance)
      D.haar.continuous.population.roots (μ.map a) := hp.add (integrable_const tolerance)
  unfold PopulationLocalPressureCore.originalReferenceFamilyLeadingPressure
  calc
    _ = ∑ c, ∫ z in cell c, D.originalFrozenReferenceReadout γ (index c) (ref c)
        (Q (index c) (ref c)) η (pref (index c) (ref c)) t z ∂μ.map a :=
      Finset.sum_congr rfl (fun c _ ↦ hcellEq c)
    _ ≤ ∑ c, ∫ z in cell c, p z + tolerance ∂μ.map a :=
      Finset.sum_le_sum (fun c _ ↦ hle c)
    _ = _ := by
      rw [← hsum, integral_add hp (integrable_const tolerance), setIntegral_const]
      simp only [smul_eq_mul, mul_comm]

/-- The same pressure-accurate Q/U family controls EVERY actual finite reference
cover sampled afterwards. Its true finite leading sum is at most the retained
original-root pressure integral plus tolerance times unchanged retained root mass.
No finite-cell pressure-identification bound is assumed. -/
theorem PopulationLocalPressureCore.exists_actual_finite_leading_integral_upper
    {I : Set ℝ} (hI : IsCompact I)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {A B : Set M} (hgap : 0 < gap)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    {η : ℝ} (hη : η < 1) (f : M × M →ᵇ ℝ)
    (hscreen : ∀ i, ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    (hgood : ∀ i, ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      OriginalClockClassPressureReferenceGood γ D hcomplete hδ hδ1 hgap hη f i z)
    (t ε probeError tolerance : ℝ) (hε : 0 < ε) (hprobe : 0 < probeError)
    (htolerance : 0 < tolerance)
    (hp : ContinuousOn (originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t)
      D.haar.continuous.population.roots)
    (hpI : IntegrableOn (originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t)
      D.haar.continuous.population.roots (μ.map a)) :
    ∃ (Q : ∀ i, (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
      (U : ∀ i, (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
      (pref : ∀ i, (D.haar.continuous.coefficient i).roots → ℝ → ℝ),
      (∀ i, D.originalClockClassGeometryOn i (Q i) (U i) A B f ε probeError) ∧
      (∀ i ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q i ref) j k →
        ∀ x ∈ (Q i ref).cell j, ∀ y ∈ (Q i ref).cell k,
          x ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
            (D.haar.continuous.coefficient i).window.val.2.1 ∧
          y ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
            (D.haar.continuous.coefficient i).window.val.2.1 ∧ x < y) ∧
      (∀ i ref s, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ref (Q i ref)
        hη hgap.le hδ hδ1 f R s) atTop (𝓝 (pref i ref s))) ∧
      ∀ {Cell : Type*} [Fintype Cell] (index : Cell → Fin D.haar.continuous.count)
      (ref : ∀ c, (D.haar.continuous.coefficient (index c)).roots)
      (cell : Cell → Set (ℚ → M)) (_hcell : ∀ c, MeasurableSet (cell c))
      (_hsub : ∀ c, cell c ⊆
        (D.haar.continuous.coefficient (index c)).roots ∩ U (index c) (ref c))
      (_hdisj : Pairwise (Disjoint on cell))
      (_hcover : (⋃ c, cell c) = D.haar.continuous.population.roots),
      D.originalReferenceFamilyLeadingPressure γ index ref cell Q pref η t ≤
        (∫ z in D.haar.continuous.population.roots,
          originalRetainedFinslerRootPressure P a κ (μ.map a)
            (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η) b f 0 t z
          ∂μ.map a) + tolerance * (μ.map a).real D.haar.continuous.population.roots := by
  have hpiece i := D.exists_pressure_accurate_geometry_readout hI γ hF hcomplete hu ha hinj
    hgap hsep hδ hδ1 hη f i (hscreen i) (hgood i) t ε probeError tolerance
    hε hprobe htolerance (hp.mono (fun z hz ↦
      D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,hz⟩))
  choose Q U pref hgeometry hfull hlimit hread using hpiece
  refine ⟨Q,U,pref,hgeometry,hfull,hlimit,?_⟩
  intro Cell _ index ref cell hcell hsub hdisj hcover
  exact finite_reference_leading_le_integral γ D hF hcomplete hu ha hinj
    index ref cell hcell (fun c z hz ↦ (hsub c hz).1) hdisj hcover Q pref η t tolerance hpI
    (fun c z hz ↦ hread (index c) (ref c) z (hsub c hz))

private theorem sharp_population_pressure_integral_upper
    [∀ j, SigmaFinite (κ j)]
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ)
    (ha : Measurable a) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hbalance : ν.map a = μ.map a)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hdim : 6 ≤ Module.finrank ℝ E)
    {T : Type (max u₁ u₂)} [Fintype T] (quadC Bnd forwardGap : ℝ)
    (hdata : D.originalFixedAtlasSharpPopulationData γ originalGap Q U retentionError splitError
      f ε probeError ha T quadC Bnd forwardGap)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) (hgap : 0 ≤ originalGap)
    (hη : retentionError < 1)
    (pref : ∀ i, (D.haar.continuous.coefficient i).roots → ℝ → ℝ)
    (hpref : ∀ i ref s, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ originalGap
      i ref (Q i ref) hη hgap hδ hδ1 f R s) atTop (𝓝 (pref i ref s)))
    (t bound : ℝ)
    (hfinite : ∀ {Cell : Type} [Fintype Cell]
      (index : Cell → Fin D.haar.continuous.count)
      (ref : ∀ c, (D.haar.continuous.coefficient (index c)).roots)
      (cell : Cell → Set (ℚ → M)) (_hcell : ∀ c, MeasurableSet (cell c))
      (_hsub : ∀ c, cell c ⊆
        (D.haar.continuous.coefficient (index c)).roots ∩ U (index c) (ref c))
      (_hdisj : Pairwise (Disjoint on cell))
      (_hcover : (⋃ c, cell c) = D.haar.continuous.population.roots),
      D.originalReferenceFamilyLeadingPressure γ index ref cell Q pref retentionError t ≤ bound) :
    let q := finrank ℝ E - 1
    let A := quadC * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2/(q:ℝ))
    let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
      (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
    let iid := fun N ↦ (Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))
    let assignment := fun N (sample : (Fin N → M) × (Fin N → M)) ↦ perturbedAssignmentValue
      (fun i j ↦ (N:ℝ) ^ (2/(q:ℝ)) *
        ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
        t * f (sample.1 i,sample.2 j)) 0 0
    (∀ N, 0 < N → Integrable (assignment N) (iid N)) ∧
    ∀ ζ > 0, ∀ᶠ N in atTop, (∫ sample, assignment N sample ∂iid N) / N ≤
      bound + originalUniformUpperError q A t ‖f‖ ε probeError residual + ζ := by
  classical
  rcases hdata with ⟨N,refs,cells,Pf,Qf,hcells,
    hsub,hPfM,hQfM,hfields,hweights,hdensity,hdisj,hcover,Qglobal,hQglobal,hwhole,
    ξ,hχfinite,hξfinite,hπ,hcal,hξmass,Cst,hquadEq,hBEq,hfgood,classify,hclassM,hclass,hsharp⟩
  let Cell := Sigma (fun i ↦ Fin (N i))
  let coreIndex := fun c : Cell ↦ c.1
  let reference := fun c : Cell ↦ refs c.1 c.2
  let cell := fun c : Cell ↦ cells c.1 c.2
  let hcell := fun c : Cell ↦ hcells c.1 c.2
  let Qlocal := fun c : Cell ↦ Q c.1 (reference c)
  let P₀ := fun c : Cell ↦ D.originalWindowReferenceWeights γ originalGap I c.1
    (reference c) (Qlocal c) retentionError
  let : MeasurableSpace (Option (Bool × T)) := ⊤
  let : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  let α := fun (c : Cell) j ↦ normalizedActualBinKernel (condDistrib u a μ)
    ((Qlocal c).cell j) ((Qlocal c).measurable_cell j) 0
  let β := fun (c : Cell) k ↦ normalizedActualBinKernel (condDistrib u a ν)
    ((Qlocal c).cell k) ((Qlocal c).measurable_cell k) 0
  let KP := fun c : Cell ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
  let χ := (((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell KP).map
    sameLabelPopulationPair).map (Prod.map b b)
  let : IsFiniteMeasure χ := hχfinite
  let : IsFiniteMeasure ξ := hξfinite
  let : IsSFiniteKernel Qglobal := hQglobal
  let (c : Cell) :
      (κ (D.haar.continuous.coefficient (coreIndex c)).seedIndex).IsAddHaarMeasure := hκ _
  have hP₀ : ∀ c j k, 0 ≤ P₀ c j k := fun c ↦ (hweights c.1 c.2).1
  have hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k := fun c ↦ (hweights c.1 c.2).2.2.2
  have hres (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j k, 0 ≤ Qf c.1 c.2 z j k := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.1
  have hrow (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j,
      (∑ k, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k)) =
        (condDistrib u a μ z).real ((Qlocal c).cell j) := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.1
  have hcol (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ k,
      (∑ j, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k)) =
        (condDistrib u a ν z).real ((Qlocal c).cell k) := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.2.1
  obtain ⟨cHaar,hcHaar,hmap,limit,hlimit,hupper⟩ :=
    D.exists_original_sharp_family_assignment_pressure_upper
    hF hcomplete hu ha hinj coreIndex cell hcell (fun c z hz ↦ (hsub c.1 c.2 hz).1)
    hdisj Qlocal reference classify hclassM hclass (fun _ _ ↦ 0) (fun _ _ ↦ 0)
    P₀ hP₀ hmass (fun c ↦ (hweights c.1 c.2).2.1)
    (fun c ↦ Pf c.1 c.2) (fun c ↦ Qf c.1 c.2) (fun c ↦ hPfM c.1 c.2)
    (fun c ↦ hdensity c.1 c.2) hres hrow hcol KP (fun _ ↦ rfl) Qglobal hwhole
    hb hμinv hνinv hbalance χ ξ rfl hπ Cst f hdim ε probeError hsharp
  let Seed := fun c : Cell ↦ (P (D.haar.continuous.coefficient c.1).seedIndex).seed
  let q := fun c : Cell ↦ Module.finrank ℝ (Seed c).covector.ker
  let density := fun c : Cell ↦ cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
  have hq (c : Cell) : 4 < q c := by
    have h := D.original_seed_label_finrank c.1
    change q c = Module.finrank ℝ E - 1 at h
    omega
  have hzero (c : Cell) : ∀ j k,
      ¬(D.haar.continuous.coefficient c.1).clockClassAllowed (Qlocal c) j k →
        P₀ c j k = 0 := by
    intro j k hnot
    simp only [P₀, PopulationLocalPressureCore.originalWindowReferenceWeights, maskedClockFlow,
      hnot, ↓reduceIte]
  have hpressure (c : Cell) :=
    (D.haar.continuous.coefficient c.1).exists_clockClassPressure_unit_density
      (Qlocal c) (reference c).val (reference c).property f (P₀ c) (hP₀ c)
      (hzero c) (hmass c) (hq c)
  choose unitPressure hunit hphysical hconc hlip using hpressure
  have hunitEq (c : Cell) (s : ℝ) : unitPressure c s = pref c.1 (reference c) s := by
    apply tendsto_nhds_unique (hunit c s)
    simpa only [PopulationLocalPressureCore.originalWindowClassScalePressure,
      ProbabilityMeasure.toMeasure_map, clockClassJointProbability, ProbabilityMeasure.coe_mk,
      P₀, Seed, q, Qlocal, reference] using hpref c.1 (reference c) s
  have hdensity (c : Cell) : 0 < density c := by
    apply mul_pos (hcHaar c)
    apply ENNReal.toNNReal_pos
    · have hr : 0 < (clockClassPairMeasure (P₀ c)).real univ := by
        rw [clockClassPairMeasure_real_univ (P₀ c) (hP₀ c)]
        exact hmass c
      exact ne_of_gt ((ENNReal.toReal_pos_iff.mp hr).1)
    · exact measure_ne_top _ _
  have hident (c : Cell) (tilt : ℝ) :
      limit c tilt = (density c : ℝ) ^ (1 - 2 / (q c : ℝ)) *
        unitPressure c (tilt * (density c : ℝ) ^ (2 / (q c : ℝ))) := by
    apply tendsto_nhds_unique (hlimit c tilt)
    simpa only [ProbabilityMeasure.toMeasure_map, clockClassJointProbability,
      ProbabilityMeasure.coe_mk, density, P₀, Seed, q, Qlocal, reference] using
      hphysical c (density c) (hdensity c) tilt
  have hcEq (c : Cell) : cHaar c =
      originalSeedCoordinateHaarFactor (Seed c) (κ (D.haar.continuous.coefficient c.1).seedIndex) :=
    (originalSeedCoordinateHaarFactor_eq_of_map (Seed c)
      (κ (D.haar.continuous.coefficient c.1).seedIndex) (cHaar c) (hmap c)).symm
  have hleading : (∑ c, volume.real
      ((atlasSeedCoord (Seed c) (finBasis ℝ (Seed c).covector.ker).equivFunL a) '' cell c) *
      limit c t) ≤ bound := by
    have hh := hfinite coreIndex reference cell hcell (fun c ↦ hsub c.1 c.2) hdisj hcover
    simpa only [hident, hunitEq, hcEq, density,
      PopulationLocalPressureCore.originalReferenceFamilyLeadingPressure,
      PopulationLocalPressureCore.originalReferenceCoordinateDensity,
      coreIndex, reference, cell, Qlocal, P₀, Seed, q, mul_assoc] using hh
  let qGlobal := finrank ℝ E - 1
  let A := quadC * dyadicMatchingConstant qGlobal * (Fintype.card T : ℝ) ^ (2/(qGlobal:ℝ))
  let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
    (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
  have hqGlobal : 4 < qGlobal := by dsimp only [qGlobal]; omega
  have hquad : 0 ≤ quadC := hquadEq ▸ Cst.quadratic_nonneg
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hquad (dyadicMatchingConstant_pos hqGlobal).le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨(hupper t).1, ?_⟩
  intro ζ hζ
  filter_upwards [(hupper t).2 ζ hζ] with N hN
  have hξreal : (ξ univ).toReal ≤ residual := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, measure_ne_top _ _⟩) hξmass
  have hexp : 0 ≤ 1 - 2/(qGlobal:ℝ) := by
    have hqR : (2:ℝ) ≤ qGlobal := by exact_mod_cast (by omega : 2 ≤ qGlobal)
    have hqpos : (0:ℝ) < qGlobal := by exact_mod_cast (by omega : 0 < qGlobal)
    exact sub_nonneg.mpr ((div_le_one hqpos).mpr hqR)
  have hrepair : A * (ξ univ).toReal ^ (1-2/(qGlobal:ℝ)) +
      2 * |t| * ‖f‖ * (ξ univ).toReal ≤
      A * residual ^ (1-2/(qGlobal:ℝ)) + 2 * |t| * ‖f‖ * residual :=
    add_le_add (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ENNReal.toReal_nonneg hξreal hexp) hA)
      (mul_le_mul_of_nonneg_left hξreal (by positivity))
  simp only [hquadEq] at hN
  have hh := hN.trans (add_le_add (add_le_add (le_refl _) hrepair) (le_refl ζ))
  have hfinal := hh.trans
    (add_le_add (add_le_add (add_le_add hleading (le_refl _)) (le_refl _)) (le_refl ζ))
  simpa only [originalUniformUpperError, A, qGlobal, residual, add_assoc] using hfinal

/-- One actual original atlas precedes all pressure screens and references. The
pressure-accurate Q/U choices are fed to its universally quantified real full-iid
factory, and limit uniqueness identifies its literal finite pressures. Hence the
original full-iid minimum has the SAME retained-pressure integral upper and the
existing deterministic geometry/probe/residual errors. -/
theorem exists_uniform_original_pressure_integral_upper
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (originalGap : ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x)
    (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (hI : IsCompact I) (hgapOriginal : 0 < originalGap)
    (hq : 4 < Module.finrank ℝ E - 1)
    (hlabel : ν.map a = μ.map a)
    (hsep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, originalGap ≤ dist x y) :
    ∃ (T : Type (max u₁ u₂)) (hT : Fintype T) (quadC Bnd forwardGap : ℝ),
      let _inst : Fintype T := hT
      0 ≤ quadC ∧ 0 ≤ Bnd ∧ 0 < forwardGap ∧
      ∀ (δ loss : ℝ≥0∞)
      (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
        (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
      (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
      (retention splitError : ℝ) (_hret : 0 < retention)
      (hret1 : retention < 1) (_hsplit : 0 < splitError)
      (f : M × M →ᵇ ℝ)
      (_hscreen : ∀ i,
        ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ originalGap / 2)
      (_hgood : ∀ i, ∀ z ∈ (D.haar.continuous.coefficient i).roots,
        OriginalClockClassPressureReferenceGood γ D hcomplete hδ hδ1 hgapOriginal hret1 f i z)
      (t ε probeError tolerance : ℝ) (_hε : 0 < ε) (_hprobe : 0 < probeError)
      (_htolerance : 0 < tolerance) (_hsmall : 3 * ε + 2 * ε ^ 2 < 1)
      (_hp : ContinuousOn (originalRetainedFinslerRootPressure P a κ (μ.map a)
        (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ)
        (fun _ _ ↦ retention) b f 0 t) D.haar.continuous.population.roots)
      (_hpI : IntegrableOn (originalRetainedFinslerRootPressure P a κ (μ.map a)
        (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ)
        (fun _ _ ↦ retention) b f 0 t) D.haar.continuous.population.roots (μ.map a)),
      ∃ (Q : ∀ i, (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
        (U : ∀ i, (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
        (pref : ∀ i, (D.haar.continuous.coefficient i).roots → ℝ → ℝ),
        D.originalFixedAtlasSharpPopulationData γ originalGap Q U retention splitError
          f ε probeError ha T quadC Bnd forwardGap ∧
        (∀ i ref s, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ originalGap
          i ref (Q i ref) hret1 hgapOriginal.le hδ hδ1 f R s) atTop (𝓝 (pref i ref s))) ∧
        let q := finrank ℝ E - 1
        let A := quadC * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2/(q:ℝ))
        let residual := (ENNReal.ofReal (retention + splitError + δ.toReal) +
          (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
        let iid := fun N ↦ (Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))
        let assignment := fun N (sample : (Fin N → M) × (Fin N → M)) ↦ perturbedAssignmentValue
          (fun i j ↦ (N:ℝ) ^ (2/(q:ℝ)) *
            ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
            t * f (sample.1 i,sample.2 j)) 0 0
        (∀ N, 0 < N → Integrable (assignment N) (iid N)) ∧
        ∀ ζ > 0, ∀ᶠ N in atTop, (∫ sample, assignment N sample ∂iid N) / N ≤
          (∫ z in D.haar.continuous.population.roots,
            originalRetainedFinslerRootPressure P a κ (μ.map a)
              (fun _ ↦ D.originalClosedWindowPairKernel hcomplete γ)
              (fun _ _ ↦ retention) b f 0 t z ∂μ.map a) +
            tolerance * (μ.map a).real D.haar.continuous.population.roots +
            originalUniformUpperError q A t ‖f‖ ε probeError residual + ζ := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨T,hT,quadC,Bnd,forwardGap,hquad,hBnd,hfgap,hfactory⟩ :=
    exists_uniform_original_sharp_population_factory (P := P) (κ := κ)
      (ρ₀ := ρ₀) (ρ₁ := ρ₁) (v := v) (r := r) γ originalGap hF hcomplete hu ha hinj horder
      hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB πOriginal hπOriginal hcalOriginal
      hI hgapOriginal hq
  let _instT : Fintype T := hT
  refine ⟨T,hT,quadC,Bnd,forwardGap,hquad,hBnd,hfgap,?_⟩
  intro δ loss D hδ hδ1 retention splitError hret hret1 hsplit f hscreen hgood
    t ε probeError tolerance hε hprobe htolerance hsmall hp hpI
  obtain ⟨Q,U,pref,hgeometry,hfull,hlimit,hfinite⟩ := D.exists_actual_finite_leading_integral_upper
    hI γ hF hcomplete hu ha hinj hgapOriginal hsep hδ hδ1 hret1 f hscreen hgood
    t ε probeError tolerance hε hprobe htolerance hp hpI
  have hsharp := hfactory δ loss D Q U
    (fun i ref ↦ ((hgeometry i).1 ref).1) (fun i ref ↦ ((hgeometry i).1 ref).2)
    (fun i ref j k hjk s hs t ht ↦
      ⟨(hfull i ref j k hjk s hs t ht).1,(hfull i ref j k hjk s hs t ht).2.1⟩)
    (fun i ↦ (hgeometry i).2.1) hδ hδ1 retention splitError hret hret1 hsplit f
    (by positivity : 0 ≤ 3 * ε + 2 * ε ^ 2) hprobe.le (fun i ↦ (hgeometry i).2.2) hsmall
  refine ⟨Q,U,pref,hsharp,hlimit,?_⟩
  have hupper := sharp_population_pressure_integral_upper γ originalGap D Q U
    retention splitError f ε probeError ha hF hcomplete hu hinj hb hμinv hνinv hlabel
    (fun j ↦ inferInstance) (by omega) quadC Bnd forwardGap hsharp hδ hδ1 hgapOriginal.le
    hret1 pref hlimit t _ hfinite
  simpa only [add_assoc] using hupper

/-- Actual original full-iid assignment pressure is eventually below the true
original global pressure integral at every positive accuracy. The SAME core family
is pressure-screened along one increasing subsequence, real pressure-accurate
partitions feed one fixed original atlas, and all deterministic errors vanish
by the already proved diagonal residual bound. The low-level zero-tilt analytic
integrability input remains explicit and is not added to a final D-main contract. -/
theorem original_full_iid_pressure_le_global_integral
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
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
    (hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z)
      (condDistrib u a μ z) (condDistrib u a ν z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      r (δn n) (lossn n))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0))
    (hη : ∀ n, 0 < η n ∧ η n < 1)
    (hscreen : ∀ n i, (((D n).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap / 2)
    (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0)
      (μ.map a))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hphysicalSep : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (t : ℝ) :
    let q := finrank ℝ E - 1
    let iid := fun N ↦ (Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))
    let assignment := fun N (sample : (Fin N → M) × (Fin N → M)) ↦ perturbedAssignmentValue
      (fun i j ↦ (N:ℝ) ^ (2/(q:ℝ)) *
        ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
        t * f (sample.1 i,sample.2 j)) 0 0
    (∀ N, 0 < N → Integrable (assignment N) (iid N)) ∧
    ∀ accuracy > 0, ∀ᶠ N in atTop, (∫ sample, assignment N sample ∂iid N) / N ≤
      (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t z ∂μ.map a) +
        accuracy := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let _instRootProbability : IsProbabilityMeasure (μ.map a) :=
    Measure.isProbabilityMeasure_map ha.aemeasurable
  let q := finrank ℝ E - 1
  let iid := fun N ↦ (Measure.pi (fun _ : Fin N ↦ μ)).prod (Measure.pi (fun _ : Fin N ↦ ν))
  let assignment := fun N (sample : (Fin N → M) × (Fin N → M)) ↦ perturbedAssignmentValue
    (fun i j ↦ (N:ℝ) ^ (2/(q:ℝ)) *
      ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
      t * f (sample.1 i,sample.2 j)) 0 0
  let full := ∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t z ∂μ.map a
  obtain ⟨T,hT,quadC,Bnd,forwardGap,hquad,hBnd,hfgap,hfactory⟩ :=
    exists_uniform_original_pressure_integral_upper (P := P) (κ := κ)
      (ρ₀ := ρ₀) (ρ₁ := ρ₁) (v := v) (r := r) γ gap hF hcomplete hu ha hinj horder
      hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB πOriginal hπOriginal hcalOriginal
      hrange hgap (by omega) hlabel hphysicalSep
  let _instT : Fintype T := hT
  let A := quadC * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2/(q:ℝ))
  obtain ⟨φ,hφ,K,hKdata,hmasslim,hRbounds,herrors⟩ :=
    exists_original_diagonal_pressure_reference_screens hrange γ hlaw hF hcomplete hu ha hinj
      horder hb hμreg hνreg hμinv hνinv hlabel hdim hgap hsep hγ
      (fun _ ↦ r) δn lossn D hδ hδ1 hδlim hloss η hηlim
      (fun n ↦ ⟨(hη n).1.le,(hη n).2⟩)
      (fun n i _ ↦ (hscreen n i).trans (by linarith)) f hp0 t
  let residual := fun m ↦ (ENNReal.ofReal
    (η (φ m) + originalUpperRefinementAccuracy m + (δn (φ m)).toReal) +
      (μ.map a) (K m)ᶜ).toReal
  let error := fun m ↦ originalUniformUpperError q A t ‖f‖
    (originalUpperRefinementAccuracy m / 10) (originalUpperRefinementAccuracy m) (residual m)
  have herrorlim : Tendsto error atTop (𝓝 0) := herrors A t
  have hrecovery := populationLabelCoreRecoveryLaw_of_inverse μ ν ha hu.continuous.measurable
    hb (lambda := μ.map a) rfl hlabel hμinv hνinv
  have hstep m : (∀ N, 0 < N → Integrable (assignment N) (iid N)) ∧
      ∀ ζ > 0, ∀ᶠ N in atTop, (∫ sample, assignment N sample ∂iid N) / N ≤
        full + 2 * originalUpperRefinementAccuracy m + error m + ζ := by
    rcases hKdata m with ⟨hK,hsub,hmass,hδτ,hητ,hcont,hcontFull,hbounded,hI,hint,hgood⟩
    obtain ⟨hτ,hτ1⟩ := originalUpperRefinementAccuracy_pos_lt_one m
    have hsmall : (μ.map a) (K m)ᶜ < ENNReal.ofReal (originalUpperRefinementAccuracy m) :=
      (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
        (by simpa only [measureReal_def, ENNReal.toReal_ofReal hτ.le] using hmass)
    let Ecore := (D (φ m)).restrictToPressureScreen hrecovery hcomplete ha
      hu.continuous.measurable hK hsub hsmall
    have hroots : Ecore.haar.continuous.population.roots = K m :=
      (D (φ m)).restrictToPressureScreen_roots hrecovery hcomplete ha
        hu.continuous.measurable hK hsub hsmall
    let oldp := originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ) (fun n _ ↦ η n) b f (φ m) t
    let newp := originalRetainedFinslerRootPressure P a κ (μ.map a)
      (fun _ ↦ Ecore.originalClosedWindowPairKernel hcomplete γ) (fun _ _ ↦ η (φ m)) b f 0 t
    have hpeq z (hz : z ∈ K m) : newp z = oldp z := by
      have hzold := hsub hz
      rw [← (D (φ m)).haar.continuous.union_eq] at hzold
      obtain ⟨i,hi⟩ := mem_iUnion.mp hzold
      exact (D (φ m)).pressureScreen_retained_pressure_eq hrecovery hcomplete ha
        hu.continuous.measurable hK hsub hsmall γ f (η (φ m)) t i z ⟨hz,hi⟩
    have hp : ContinuousOn newp Ecore.haar.continuous.population.roots := by
      rw [hroots]
      exact hcont.congr hpeq
    have hpI : IntegrableOn newp Ecore.haar.continuous.population.roots (μ.map a) := by
      rw [hroots]
      exact hI.congr ((ae_restrict_mem hK.measurableSet).mono (fun z hz ↦ (hpeq z hz).symm))
    have hgood' := (D (φ m)).pressureScreen_reference_good γ hrecovery hcomplete ha
      hu.continuous.measurable hK hsub hsmall (hδ (φ m)) (hδ1 (φ m)) hgap
      (hη (φ m)).2 f hgood
    obtain ⟨hε,hρ,hsmallGeometry⟩ := originalUpperRefinementGeometry_small m
    obtain ⟨Q,U,pref,hsharp,hlimit,hupper⟩ := hfactory (δn (φ m))
      (ENNReal.ofReal (originalUpperRefinementAccuracy m)) Ecore (hδ (φ m)) (hδ1 (φ m))
      (η (φ m)) (originalUpperRefinementAccuracy m) (hη (φ m)).1 (hη (φ m)).2 hτ f
      (hscreen (φ m)) hgood' t (originalUpperRefinementAccuracy m / 10)
      (originalUpperRefinementAccuracy m) (originalUpperRefinementAccuracy m)
      hε hτ hτ hsmallGeometry hp hpI
    have hintEq : (∫ z in Ecore.haar.continuous.population.roots, newp z ∂μ.map a) =
        ∫ z in K m, oldp z ∂μ.map a := by
      rw [hroots]
      exact integral_congr_ae ((ae_restrict_mem hK.measurableSet).mono hpeq)
    have hmassScale : originalUpperRefinementAccuracy m *
        (μ.map a).real Ecore.haar.continuous.population.roots ≤
        originalUpperRefinementAccuracy m := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (measureReal_le_one (μ := μ.map a) (s := Ecore.haar.continuous.population.roots)) hτ.le
    refine ⟨hupper.1, ?_⟩
    intro ζ hζ
    filter_upwards [hupper.2 ζ hζ] with N hN
    have hN' : (∫ sample, assignment N sample ∂iid N) / N ≤
        (∫ z in Ecore.haar.continuous.population.roots, newp z ∂μ.map a) +
        originalUpperRefinementAccuracy m *
          (μ.map a).real Ecore.haar.continuous.population.roots + error m + ζ := by
      simpa only [hroots] using hN
    rw [hintEq] at hN'
    change (∫ sample, assignment N sample ∂iid N) / N ≤ full +
      2 * originalUpperRefinementAccuracy m + error m + ζ
    change (∫ z in K m, oldp z ∂μ.map a) < full + originalUpperRefinementAccuracy m at hint
    linarith only [hN',hint,hmassScale]
  refine ⟨(hstep 0).1, ?_⟩
  intro accuracy haccuracy
  have htotal : Tendsto (fun m ↦ 2 * originalUpperRefinementAccuracy m + error m)
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_originalUpperRefinementAccuracy.const_mul 2).add herrorlim
  obtain ⟨m,hm⟩ := (htotal.eventually_lt_const (half_pos haccuracy)).exists
  filter_upwards [(hstep m).2 (accuracy / 2) (half_pos haccuracy)] with N hN
  linarith only [hm,hN]

end OTSelector.Reconstruction
