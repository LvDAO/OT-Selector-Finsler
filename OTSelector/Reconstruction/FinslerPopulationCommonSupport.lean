import OTSelector.Reconstruction.FinslerPopulationConditionalSupport

/-!
# A common actual support span for both physical conditional laws

The two original compact populations determine one attained finite support span on
every complete seed representing their common geometric label. The full closed
span is calibrated, and both atomless conditional laws give its interior full mass.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- An original scalar probability with compact atomless support in one physical clock. -/
structure CompactAtomlessClockSupport (μ : Measure ℝ) (offset lo hi : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  atomless : NullSingletonClass μ
  compact : IsCompact μ.support
  support_bounds : ∀ x ∈ μ.support, x - offset ∈ Icc lo hi
  ae_open : ∀ᵐ x ∂μ, x - offset ∈ Ioo lo hi

/-- A fixed clock translation preserves the actual support span and its full interior mass. -/
theorem CompactAtomlessClockSupport.clockShift {μ : Measure ℝ} {offset lo hi : ℝ}
    (h : CompactAtomlessClockSupport μ offset lo hi) (u₀ : ℝ) :
    CompactAtomlessClockSupport (μ.map (fun s : ℝ ↦ s - u₀)) (offset - u₀) lo hi := by
  have := h.probability
  have := h.atomless
  obtain ⟨hp, hn, hc, hs⟩ := compact_atomless_probability_clockShift μ h.compact u₀
  refine ⟨hp, hn, hc, ?_, ?_⟩
  · intro q hq
    obtain ⟨s, hs, rfl⟩ := hs hq
    simpa only [sub_sub_sub_cancel_right] using h.support_bounds s hs
  · apply (ae_map_iff (measurable_id.sub_const u₀).aemeasurable
      (measurableSet_Ioo.preimage (measurable_id.sub_const (offset - u₀)))).mpr
    simpa only [id_eq, sub_sub_sub_cancel_right] using h.ae_open

/-- The seed clock is obtained from the original scalar law by its actual level shift. -/
theorem CompactAtomlessClockSupport.seedClock {μ : Measure ℝ} {offset lo hi : ℝ}
    (h : CompactAtomlessClockSupport μ offset lo hi) :
    CompactAtomlessClockSupport (μ.map (fun s : ℝ ↦ s - offset)) 0 lo hi := by
  simpa only [sub_self] using h.clockShift offset

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M]
  [MeasurableSpace Z] [MeasurableEq Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Both original colors share attained support endpoints on the same complete seed. -/
structure CommonSeedSupportSpan (S : F.CalibratedLevelSeedPatch u) (w : S.covector.ker)
    (μ ν : Measure ℝ) (lo hi : ℝ) : Prop where
  lt : lo < hi
  left_mem_support : (S.level : ℝ) + lo ∈ μ.support ∪ ν.support
  right_mem_support : (S.level : ℝ) + hi ∈ μ.support ∪ ν.support
  source : CompactAtomlessClockSupport μ S.level lo hi
  target : CompactAtomlessClockSupport ν S.level lo hi
  calibrated : Icc lo hi ⊆ S.calibrationTimes w
  curve_continuous : Continuous (S.curve w)

/-- The support conclusion is simultaneous for every actual seed on a retained label. -/
def PopulationConditionalSupportLaw (a : M → Z) (lambda : Measure Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] : Prop :=
  ∀ᵐ z ∂lambda, ∀ (S : F.CalibratedLevelSeedPatch u) (w : S.covector.ker),
    w ∈ S.labels → a (S.curve w 0) = z → ∃ lo hi : ℝ,
      CommonSeedSupportSpan S w (condDistrib u a η₀ z) (condDistrib u a η₁ z) lo hi

omit [BorelSpace E] in
/-- Original physical densities, compact carriers and the actual geometric labels produce
the common calibrated support span; no conditional compactness or clock oracle is supplied. -/
theorem populationConditionalSupportLaw_of_physical_laws
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
    (hsource : PopulationConditionalWindowLaw P a κ lambda η₀ ρ₀ v)
    (htarget : PopulationConditionalWindowLaw P a κ lambda η₁ ρ₁ v)
    (ha : Measurable a) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instCommonSupportMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (horder : let _instCommonSupportOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hη₀ : ∀ᵐ x ∂η₀, x ∈ A) (hη₁ : ∀ᵐ x ∂η₁, x ∈ B)
    (hi₀ : let _instCommonInteriorMetric : MetricSpace M := F.metricSpace
      ∀ᵐ x ∂η₀, x ∈ calibratedInterior u)
    (hi₁ : let _instCommonInteriorMetric : MetricSpace M := F.metricSpace
      ∀ᵐ x ∂η₁, x ∈ calibratedInterior u) :
    PopulationConditionalSupportLaw (F := F) (u := u) a lambda η₀ η₁ := by
  let _instCommonSupportMetric : MetricSpace M := F.metricSpace
  have hs := hsource.ae_compact_atomless_clock ha hu hA hη₀
  have ht := htarget.ae_compact_atomless_clock ha hu hB hη₁
  have hcs := ae_conditional_clock_calibrated_same_seed η₀ ha hF hcomplete hu horder hi₀
  have hct := ae_conditional_clock_calibrated_same_seed η₁ ha hF hcomplete hu horder hi₁
  rw [hsource.label_law] at hcs
  rw [htarget.label_law] at hct
  filter_upwards [hs, ht, hcs, hct] with z hs ht hcs hct
  intro S w hw hwz
  have := hs.1
  have := ht.1
  let μ := condDistrib u a η₀ z
  let ν := condDistrib u a η₁ z
  have hsumNull : NullSingletonClass (μ + ν) := by
    constructor
    intro x
    simp only [Measure.add_apply, measure_singleton, add_zero]
  have hsumne : μ + ν ≠ 0 := by
    intro hzero
    have huniv := congrArg (fun m : Measure ℝ ↦ m univ) hzero
    simp at huniv
  have hcompact : IsCompact (μ + ν).support := by
    rw [Measure.support_add]
    exact hs.2.1.union ht.2.1
  have hclock : ∀ᵐ s : ℝ ∂μ + ν, s - S.level ∈ S.calibrationTimes w :=
    ae_add_measure_iff.mpr ⟨(hcs S w hw hwz).1, (hct S w hw hwz).1⟩
  obtain ⟨lo, hi, hlt, hl, hr, hbounds, hopen, hcal, _, hcurve⟩ :=
    S.exists_compact_support_calibrated_span hF hu hw (μ + ν) hsumne hcompact S.level hclock
  rw [Measure.support_add] at hl hr hbounds
  obtain ⟨hopen₀, hopen₁⟩ := ae_add_measure_iff.mp hopen
  refine ⟨lo, hi, hlt, hl, hr, ?_, ?_, hcal, hcurve⟩
  · exact ⟨inferInstance, hs.1, hs.2.1,
      fun s hmem ↦ hbounds s (Or.inl hmem), hopen₀⟩
  · exact ⟨inferInstance, ht.1, ht.2.1,
      fun s hmem ↦ hbounds s (Or.inr hmem), hopen₁⟩

end OTSelector.Reconstruction
