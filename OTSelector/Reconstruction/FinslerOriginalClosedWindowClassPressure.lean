import OTSelector.Reconstruction.FinslerOriginalClosedWindowClassObservation
import OTSelector.Reconstruction.FinslerOriginalFineClassPressureWithEndpoints

/-! Actual physical reference class pressures converge to the canonical
continuous closed-window pressure, on one fixed original joint clock law. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Literal unit-density physical class pressure at its original reference
weights. Its nonzero original mass is produced by the stored window loss. -/
def PopulationLocalPressureCore.originalWindowClassScalePressure
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width) {η : ℝ}
    (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (f : M × M →ᵇ ℝ) (R t : ℝ) : ℝ := by
  let C := D.haar.continuous.coefficient i
  let P₀ := D.originalWindowReferenceWeights γ gap range i ref Q η
  have hweights := D.originalWindowReferenceWeights_mass γ gap range i ref Q hη hgap hδ hδ1
  letI : IsProbabilityMeasure (normalizedClockClassPairMeasure P₀) :=
    normalizedClockClassPairMeasure_probability P₀ hweights.1 hweights.2.2.2
  let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
  let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
  letI : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact finiteClassLegalScalePressure (finrank ℝ (P C.seedIndex).seed.covector.ker)
    (C.clockClassAllowed Q) α β (C.clockClassKinetic Q ref.val)
    (C.clockClassProbe Q ref.val ref.property f) R t

/-- The actual original separated conditional laws internally supply one fixed
positive window law, all full endpoint fine bins, their actual physical class
pressure limits, and convergence to the SAME continuous original coefficient
pressure. No class-law or pressure-limit callback is supplied. -/
theorem PopulationLocalPressureCore.exists_originalClosedWindow_class_pressure_convergence
    {range : Set ℝ} (hrange : IsCompact range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap diameter : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    (π : Measure (range × range))
    (hmap : π.map (Prod.map Subtype.val Subtype.val) = γ ref.val)
    (hwindowGap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (hsep : ConditionalClockSupportBounds (condDistrib u a μ ref.val) (condDistrib u a ν ref.val) gap diameter)
    (hq : 4 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    {η : ℝ} (hη : η < 1) (hgap : 0 < gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (f : M × M →ᵇ ℝ) :
    let C := D.haar.continuous.coefficient i
    let χ := π.restrict ((Prod.map Subtype.val Subtype.val) ⁻¹' C.window.region)
    ∃ law : ProbabilityMeasure (range × range), (law : Measure (range × range)) = normalizedFiniteLaw χ ∧
    ∃ Q : ∀ n : ℕ, FiniteScalarBins range (1 / ((n:ℝ)+2)),
      (∀ n, Nonempty (OriginalRangeClockResamplingData C (Q n) ref.val ref.property f
        (1 / ((n:ℝ)+2)) (1 / ((n:ℝ)+2)))) ∧
      (∀ n j k, C.clockClassAllowed (Q n) j k → ∀ x ∈ (Q n).cell j, ∀ y ∈ (Q n).cell k,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y) ∧
    ∃ p : ℝ → ℝ, ∃ pref : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ legalMarkedScalePressure
        (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val
        (law.map measurable_fst.aemeasurable : Measure range)
        (law.map measurable_snd.aemeasurable : Measure range)
        (fun x y w ↦ matrixQuadratic (C.matrix ref.val (x.val,y.val)) w)
        (C.originalRangeClockProbe ref.val ref.property f) R t) atTop (𝓝 (p t))) ∧
      (∀ n t, Tendsto (fun R ↦ D.originalWindowClassScalePressure γ gap i ref (Q n)
        hη hgap.le hδ hδ1 f R t) atTop (𝓝 (pref n t))) ∧
      ∀ t, Tendsto (fun n ↦ pref n t) atTop (𝓝 (p t)) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let read : range × range → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  have hread : Measurable read := measurable_subtype_coe.prodMap measurable_subtype_coe
  haveI : IsProbabilityMeasure (π.map read) := by rw [hmap]; infer_instance
  letI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map read
  let χ := π.restrict (read ⁻¹' C.window.region)
  have hχmap : χ.map read = (γ ref.val).restrict C.window.region := by
    rw [← Measure.restrict_map hread C.window.isCompact_region.measurableSet,hmap]
  have hχmass : χ.real univ = ((γ ref.val).restrict C.window.region).real univ := by
    rw [← hχmap]
    exact (map_measureReal_apply hread MeasurableSet.univ).symm
  have hpos : 0 < χ.real univ := by
    rw [hχmass,← D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i ref.val ref.property]
    exact (sub_pos.mpr hδ1).trans (D.originalClosedWindowPairKernel_mass_lower γ hcomplete hgap.le hδ i ref)
  letI : IsProbabilityMeasure (normalizedFiniteLaw χ) := normalizedFiniteLaw_probability χ hpos
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
  have hz : ref.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,ref.property⟩
  have hgood := (D.haar.continuous.population.good ref.val hz).1
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
    simpa only [Real.dist_eq,abs_sub_comm] using hsep.separated p.1.val hs p.2.val ht
  obtain ⟨Q,hRdata,hfull,p,pref,hp,hpref,hconv⟩ := C.exists_original_fine_class_pressure_convergence_with_endpoints
    hF hcomplete hu ha hinj ref.val ref.property f hrange hwindowGap
    (α : Measure range) (β : Measure range) hα hβ (law : Measure (range × range)) ⟨rfl,rfl⟩ hgapLaw hsepLaw hq
  refine ⟨law,rfl,Q,hRdata,hfull,p,pref,hp,?_,hconv⟩
  intro n t
  have hobs := D.originalClosedWindow_class_observation hrange.measurableSet γ i ref π hmap (Q n)
    hwindowGap (hfull n) hη hgap.le hδ hδ1
  have hαclass : (normalizedClockClassPairMeasure
      (D.originalWindowReferenceWeights γ gap range i ref (Q n) η)).map Prod.fst =
      (α : Measure range).map (Q n).rangeClassify := by
    change _ = (((law : Measure (range × range)).map Prod.fst).map (Q n).rangeClassify)
    rw [← hobs.2.2.2.2.1,Measure.map_map measurable_fst
      ((Q n).measurable_rangeClassify.prodMap (Q n).measurable_rangeClassify),
      Measure.map_map (Q n).measurable_rangeClassify measurable_fst]
    rfl
  have hβclass : (normalizedClockClassPairMeasure
      (D.originalWindowReferenceWeights γ gap range i ref (Q n) η)).map Prod.snd =
      (β : Measure range).map (Q n).rangeClassify := by
    change _ = (((law : Measure (range × range)).map Prod.snd).map (Q n).rangeClassify)
    rw [← hobs.2.2.2.2.1,Measure.map_map measurable_snd
      ((Q n).measurable_rangeClassify.prodMap (Q n).measurable_rangeClassify),
      Measure.map_map (Q n).measurable_rangeClassify measurable_snd]
    rfl
  simpa only [PopulationLocalPressureCore.originalWindowClassScalePressure,hαclass,hβclass,C,
    ProbabilityMeasure.toMeasure_map] using hpref n t

end OTSelector.Reconstruction
