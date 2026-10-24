import OTSelector.Reconstruction.FinslerOriginalWindowKernelConvergence
import OTSelector.Reconstruction.OriginalJointLawGeometryPressureUpper
import OTSelector.MeasureTheory.VariationNullSet

/-! Actual conditional-law variation on the original Finsler continuity cores
passes exactly through scalar-range lifts and arbitrary retained pairings. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- Actual original L1 and geometric cores produce upper continuity of the
canonical retained-window pressures. The original conditional pairings may vary
arbitrarily. Their actual retained masses, source laws and target laws remain
unchanged; no pressure-limit or conditional-law continuity callback is required. -/
theorem PopulationLocalPressureCore.exists_original_window_pressure_upper
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count)
    (z : ℕ → (D.haar.continuous.coefficient i).roots)
    (ref : (D.haar.continuous.coefficient i).roots) (hz : Tendsto z atTop (𝓝 ref))
    (f : M × M →ᵇ ℝ) {range : Set ℝ} (hrange : MeasurableSet range)
    {gap : ℝ} (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (hwindowGap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (hq : 4 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (π : ℕ → ProbabilityMeasure (range × range)) (πref : ProbabilityMeasure (range × range))
    (hmapSn : ∀ n, ((π n : Measure (range × range)).map Prod.fst).map Subtype.val =
      populationTwoColorClockKernel u a μ ν 0 (z n).val)
    (hmapTn : ∀ n, ((π n : Measure (range × range)).map Prod.snd).map Subtype.val =
      populationTwoColorClockKernel u a μ ν 1 (z n).val)
    (hmapS : ((πref : Measure (range × range)).map Prod.fst).map Subtype.val =
      populationTwoColorClockKernel u a μ ν 0 ref.val)
    (hmapT : ((πref : Measure (range × range)).map Prod.snd).map Subtype.val =
      populationTwoColorClockKernel u a μ ν 1 ref.val)
    (hgapLaw : ∀ n, ∀ᵐ p ∂(π n : Measure (range × range)), gap ≤ p.2.val - p.1.val)
    (hgapRef : ∀ᵐ p ∂(πref : Measure (range × range)), gap ≤ p.2.val - p.1.val)
    (hsep : ∀ n, ∀ᵐ p ∂((π n : Measure (range × range)).map Prod.fst).prod
      ((π n : Measure (range × range)).map Prod.snd), gap ≤ |p.2.val - p.1.val|)
    (hsepRef : ∀ᵐ p ∂((πref : Measure (range × range)).map Prod.fst).prod
      ((πref : Measure (range × range)).map Prod.snd), gap ≤ |p.2.val - p.1.val|)
    (χ : ℕ → Measure (range × range)) (hχ : ∀ n, χ n ≤ (π n : Measure (range × range)))
    (χouter : ∀ n, ∀ᵐ p ∂χ n,
      p.1.val ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1 ∧
      p.2.val ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1)
    (δn : ℕ → ℝ) (hδ : Tendsto δn atTop (𝓝 0))
    (hδ0 : ∀ n, 0 ≤ δn n) (hδ1 : ∀ n, δn n < 1)
    (hmass : ∀ n, 1 - δn n ≤ (χ n).real univ) :
    let C := D.haar.continuous.coefficient i
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ πret : ℕ → ProbabilityMeasure (range × range),
      (∀ n, (πret n : Measure (range × range)) = normalizedFiniteLaw (χ n)) ∧
    ∃ pref : ℝ → ℝ, ∃ p : ℕ → ℝ → ℝ,
      (∀ t, Tendsto (fun L ↦ legalMarkedScalePressure q Subtype.val Subtype.val
        (πref.map measurable_fst.aemeasurable : Measure range)
        (πref.map measurable_snd.aemeasurable : Measure range)
        (fun x y w ↦ matrixQuadratic (C.matrix ref.val (x.val,y.val)) w)
        (C.originalRangeClockProbe ref.val ref.property f) L t) atTop (𝓝 (pref t))) ∧
      (∀ n t, Tendsto (fun L ↦ legalMarkedScalePressure q Subtype.val Subtype.val
        ((πret n).map measurable_fst.aemeasurable : Measure range)
        ((πret n).map measurable_snd.aemeasurable : Measure range)
        (fun x y w ↦ matrixQuadratic (C.matrix (z n).val (x.val,y.val)) w)
        (C.originalRangeClockProbe (z n).val (z n).property f) L t) atTop (𝓝 (p n t))) ∧
      (∀ n, LipschitzWith ⟨‖f‖,norm_nonneg f⟩ (p n)) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop, p n t < pref t + ε := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := finrank ℝ (P C.seedIndex).seed.covector.ker
  let α := πref.map measurable_fst.aemeasurable
  let β := πref.map measurable_snd.aemeasurable
  letI : ∀ n, IsFiniteMeasure (χ n) := fun n ↦ isFiniteMeasure_of_le (π n : Measure _) (hχ n)
  have hpos n : 0 < (χ n).real univ := (sub_pos.mpr (hδ1 n)).trans_le (hmass n)
  letI : ∀ n, IsProbabilityMeasure (normalizedFiniteLaw (χ n)) :=
    fun n ↦ normalizedFiniteLaw_probability (χ n) (hpos n)
  let πret : ℕ → ProbabilityMeasure (range × range) := fun n ↦ ⟨normalizedFiniteLaw (χ n),inferInstance⟩
  let αret := fun n ↦ (πret n).map measurable_fst.aemeasurable
  let βret := fun n ↦ (πret n).map measurable_snd.aemeasurable
  have hfullS : Tendsto (fun n ↦
      (((π n : Measure (range × range)).map Prod.fst).toSignedMeasure -
        (α : Measure range).toSignedMeasure).totalVariation.real univ) atTop (𝓝 0) := by
    have hactual := D.original_piece_clock_variation_tendsto i z ref hz 0
    apply hactual.congr'
    apply Filter.Eventually.of_forall
    intro n
    simpa only [α,ProbabilityMeasure.toMeasure_map,hmapSn n,hmapS] using original_totalVariation_real_map_eq
      ((π n : Measure (range × range)).map Prod.fst) (α : Measure range) Subtype.val
      (MeasurableEmbedding.subtype_coe hrange)
  have hfullT : Tendsto (fun n ↦
      (((π n : Measure (range × range)).map Prod.snd).toSignedMeasure -
        (β : Measure range).toSignedMeasure).totalVariation.real univ) atTop (𝓝 0) := by
    have hactual := D.original_piece_clock_variation_tendsto i z ref hz 1
    apply hactual.congr'
    apply Filter.Eventually.of_forall
    intro n
    simpa only [β,ProbabilityMeasure.toMeasure_map,hmapTn n,hmapT] using original_totalVariation_real_map_eq
      ((π n : Measure (range × range)).map Prod.snd) (β : Measure range) Subtype.val
      (MeasurableEmbedding.subtype_coe hrange)
  have hdata : ∀ᶠ n in atTop, χ n ≤ (π n : Measure (range × range)) ∧
      0 ≤ δn n ∧ δn n < 1 ∧ 1 - δn n ≤ (χ n).real univ :=
    Filter.Eventually.of_forall fun n ↦ ⟨hχ n,hδ0 n,hδ1 n,hmass n⟩
  have hvarS : Tendsto (fun n ↦
      ((αret n : Measure range).toSignedMeasure - (α : Measure range).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
    exact tendsto_totalVariation_normalized_retained_observation
      (fun n ↦ (π n : Measure (range × range))) χ Prod.fst measurable_fst
      (α : Measure range) atTop δn hδ hfullS hdata
  have hvarT : Tendsto (fun n ↦
      ((βret n : Measure range).toSignedMeasure - (β : Measure range).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
    exact tendsto_totalVariation_normalized_retained_observation
      (fun n ↦ (π n : Measure (range × range))) χ Prod.snd measurable_snd
      (β : Measure range) atTop δn hδ hfullT hdata
  let outer : Set range := {x | x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1}
  have houter : MeasurableSet outer := measurable_subtype_coe measurableSet_Icc
  have hretI n : ∀ᵐ p ∂(πret n : Measure (range × range)), p.1 ∈ outer ∧ p.2 ∈ outer :=
    Measure.ae_smul_measure (χouter n) _
  have hαret n : ∀ᵐ x ∂(αret n : Measure range), x ∈ outer :=
    (ae_map_iff measurable_fst.aemeasurable houter).mpr ((hretI n).mono fun _ h ↦ h.1)
  have hβret n : ∀ᵐ y ∂(βret n : Measure range), y ∈ outer :=
    (ae_map_iff measurable_snd.aemeasurable houter).mpr ((hretI n).mono fun _ h ↦ h.2)
  have hα : ∀ᵐ x ∂(α : Measure range), x ∈ outer := by
    have hz n : (αret n : Measure range) outerᶜ = 0 :=
      (measure_eq_zero_iff_ae_notMem).mpr (by simpa only [mem_compl_iff,not_not] using hαret n)
    have hn := original_null_set_of_variation_tendsto (fun n ↦ (αret n : Measure range))
      (α : Measure range) hvarS houter.compl hz
    simpa only [mem_compl_iff,not_not] using (measure_eq_zero_iff_ae_notMem).mp hn
  have hβ : ∀ᵐ y ∂(β : Measure range), y ∈ outer := by
    have hz n : (βret n : Measure range) outerᶜ = 0 :=
      (measure_eq_zero_iff_ae_notMem).mpr (by simpa only [mem_compl_iff,not_not] using hβret n)
    have hn := original_null_set_of_variation_tendsto (fun n ↦ (βret n : Measure range))
      (β : Measure range) hvarT houter.compl hz
    simpa only [mem_compl_iff,not_not] using (measure_eq_zero_iff_ae_notMem).mp hn
  have hac n : normalizedFiniteLaw (χ n) ≪ (π n : Measure (range × range)) :=
    (Measure.absolutelyContinuous_of_le (hχ n)).smul_left _
  have hgapRet n : ∀ᵐ p ∂(πret n : Measure (range × range)), gap ≤ p.2.val - p.1.val :=
    (hac n).ae_le (hgapLaw n)
  have hsepRet n : ∀ᵐ p ∂(αret n : Measure range).prod (βret n : Measure range),
      gap ≤ |p.2.val - p.1.val| :=
    (((hac n).map measurable_fst).prod ((hac n).map measurable_snd)).ae_le (hsep n)
  have hI n : ∀ᵐ p ∂(πret n : Measure (range × range)), p.1.val ∈ range ∧ p.2.val ∈ range :=
    Filter.Eventually.of_forall fun p ↦ ⟨p.1.property,p.2.property⟩
  have hIref : ∀ᵐ p ∂(πref : Measure (range × range)), p.1.val ∈ range ∧ p.2.val ∈ range :=
    Filter.Eventually.of_forall fun p ↦ ⟨p.1.property,p.2.property⟩
  obtain ⟨K,hK,hbound⟩ := C.exists_originalWindowClockKinetic_bound (range := range)
  have hhom (w : ℚ → M) (x y : range) (c : ℝ) (_hc : 0 ≤ c) (v : Fin q → ℝ) :
      C.originalWindowClockKinetic w x y (fun l ↦ c * v l) =
        c ^ 2 * C.originalWindowClockKinetic w x y v := by
    change C.originalWindowClockKinetic w x y (c • v) = _
    exact C.originalWindowClockKinetic_homogeneous w x y c v
  have hgeometry : ∀ ε > 0, ε ≤ 1 → ∀ η > 0, ∀ᶠ n in atTop,
      ∀ x y : range, x.val < y.val →
        (∀ w, |C.originalWindowClockKinetic (z n).val x y w - C.originalWindowClockKinetic ref.val x y w| ≤
          ε * C.originalWindowClockKinetic ref.val x y w) ∧
        |C.originalWindowClockProbe (z n).val (z n).property f x y -
          C.originalWindowClockProbe ref.val ref.property f x y| ≤ η := by
    intro ε hε _hε1 η hη
    exact (D.original_window_kernels_eventually hF hcomplete hu ha hinj i z ref hz f ε hε η hη).mono
      fun n hn x y _ ↦ hn x y
  obtain ⟨pref,p,href,hpt,hLip,hupper⟩ := exists_legalMarkedPressure_upper_of_original_law_and_geometry
    q hq hrange coarse hgap Subtype.val Subtype.val measurable_subtype_coe measurable_subtype_coe
    αret βret α β hvarS hvarT πref ⟨rfl,rfl⟩ hIref hgapRef hsepRef
    πret (fun _ ↦ ⟨rfl,rfl⟩) hI hgapRet hsepRet hK (norm_nonneg f)
    (C.originalWindowClockKinetic ref.val)
    (C.measurable_originalWindowClockKinetic hF hcomplete hu ha hinj ref.val)
    (C.originalWindowClockKinetic_nonneg ref.val ref.property)
    (hbound ref.val ref.property) (hhom ref.val)
    (C.originalWindowClockProbe ref.val ref.property f)
    (C.measurable_originalWindowClockProbe hF ref.val ref.property f)
    (C.originalWindowClockProbe_abs_le ref.val ref.property f)
    (fun n ↦ C.originalWindowClockKinetic (z n).val)
    (fun n ↦ C.originalWindowClockProbe (z n).val (z n).property f)
    (fun _ ↦ K) (fun _ ↦ hK)
    (fun n ↦ C.measurable_originalWindowClockKinetic hF hcomplete hu ha hinj (z n).val)
    (fun n ↦ C.originalWindowClockKinetic_nonneg (z n).val (z n).property)
    (fun n ↦ hbound (z n).val (z n).property) (fun n ↦ hhom (z n).val)
    (fun n ↦ C.measurable_originalWindowClockProbe hF (z n).val (z n).property f)
    (fun n ↦ C.originalWindowClockProbe_abs_le (z n).val (z n).property f) hgeometry
  refine ⟨πret,fun _ ↦ rfl,pref,p,?_,?_,hLip,hupper⟩
  · intro t
    exact (href t).congr' (Filter.Eventually.of_forall fun L ↦
      C.window_clock_scalePressure_eq_canonical_original hwindowGap ref.val ref.property f
        (α : Measure range) (β : Measure range) hα hβ hsepRef L t)
  · intro n t
    exact (hpt n t).congr' (Filter.Eventually.of_forall fun L ↦
      C.window_clock_scalePressure_eq_canonical_original hwindowGap (z n).val (z n).property f
        (αret n : Measure range) (βret n : Measure range) (hαret n) (hβret n) (hsepRet n) L t)

end OTSelector.Reconstruction
