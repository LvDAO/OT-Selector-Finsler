import OTSelector.Geometry.Finsler.Calibration.RootCoefficient
import OTSelector.Reconstruction.OriginalSeedPairCoefficientContinuity
import OTSelector.MeasureTheory.MeasurableContinuousSections

/-!
# Uniform compact cores for the actual population coefficient

Original conditional moment data supply continuity and positivity on every compact
ordered interior scalar region. The jointly Borel original coefficient then has a
compact root core on which the entire scalar section is continuous. The original
conditional data and any other almost-everywhere property are retained pointwise.
-/

open Set Function MeasureTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- A fixed scalar interval lies inside the actual common conditional support span
of this original seed at the given population root. No comparison is measurably selected. -/
def HasOriginalSeedPairWindow (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (μ ν : Z → Measure ℝ) (l r : ℝ) (z : Z) : Prop :=
  ∃ w : S.labels, a (S.curve w 0) = z ∧
    ∃ D : OriginalSeedConditionalMoments S w (μ z) (ν z),
      l - S.level ∈ Ioo D.lo D.hi ∧ r - S.level ∈ Ioo D.lo D.hi

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instRootCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- Continuity of an actual scalar pair section follows from the original conditional data. -/
theorem HasOriginalSeedPairWindow.continuousOn_rootCoefficient
    {μ ν : Z → Measure ℝ} {l r : ℝ} (hlr : l ≤ r) {z : Z}
    (hz : HasOriginalSeedPairWindow S a μ ν l r z) :
    ContinuousOn (fun p : ℝ × ℝ ↦ populationSeedRootCoefficient S a
      (Module.finBasis ℝ S.covector.ker) (z, p))
      {p | p.1 ∈ Icc l r ∧ p.2 ∈ Icc l r ∧ p.1 < p.2} := by
  obtain ⟨w, hwz, D, hl, hr⟩ := hz
  apply (D.continuousOn_pair_coefficient hF w.property hlr hl hr).congr
  intro p hp
  rw [← hwz]
  exact populationSeedRootCoefficient_at_label S hF hcomplete hu ha hinj
    (Module.finBasis ℝ S.covector.ker) w p.1 p.2

/-- Positivity of the root coefficient uses the same actual interval and original basis. -/
theorem HasOriginalSeedPairWindow.posDef_rootCoefficient
    {μ ν : Z → Measure ℝ} {l r : ℝ} {z : Z}
    (hz : HasOriginalSeedPairWindow S a μ ν l r z)
    {p : ℝ × ℝ} (hp : p.1 ∈ Icc l r ∧ p.2 ∈ Icc l r ∧ p.1 < p.2) :
    (populationSeedRootCoefficient S a (Module.finBasis ℝ S.covector.ker) (z, p)).PosDef := by
  obtain ⟨w, hwz, D, hl, hr⟩ := hz
  rw [← hwz, populationSeedRootCoefficient_at_label S hF hcomplete hu ha hinj]
  have hx : p.1 - S.level ∈ Ioo D.lo D.hi :=
    ⟨hl.1.trans_le (sub_le_sub_right hp.1.1 _),
      (sub_le_sub_right hp.1.2 _).trans_lt hr.2⟩
  have hy : p.2 - S.level ∈ Ioo D.lo D.hi :=
    ⟨hl.1.trans_le (sub_le_sub_right hp.2.1.1 _),
      (sub_le_sub_right hp.2.1.2 _).trans_lt hr.2⟩
  exact (D.pair_compliance_posDef hF w.property hx hy hp.2.2).2

/-- The actual coefficient has joint continuity on a compact root core times the
entire chosen compact ordered scalar region, retaining the original moment witness. -/
theorem exists_populationSeedRootCoefficient_compact_core
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    {lambda : Measure Z} {s : Set Z} (hs : MeasurableSet s) (hfinite : lambda s ≠ (∞ : ℝ≥0∞))
    {μ ν : Z → Measure ℝ} {l r : ℝ} (hlr : l ≤ r)
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (hTsub : T ⊆ {p | p.1 ∈ Icc l r ∧ p.2 ∈ Icc l r ∧ p.1 < p.2})
    {Good : Z → Prop}
    (hgood : ∀ᵐ z ∂lambda.restrict s, HasOriginalSeedPairWindow S a μ ν l r z ∧ Good z)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ lambda (s \ K) < ε ∧
      ContinuousOn (populationSeedRootCoefficient S a (Module.finBasis ℝ S.covector.ker))
        (K ×ˢ T) ∧
      ∀ z ∈ K, HasOriginalSeedPairWindow S a μ ν l r z ∧ Good z := by
  let coeff := populationSeedRootCoefficient S a (Module.finBasis ℝ S.covector.ker)
  have hm : Measurable coeff :=
    measurable_populationSeedRootCoefficient S hF hcomplete hu ha hinj _
  have heval : ∀ p : ℝ × ℝ, Measurable (fun z ↦ coeff (z, p)) :=
    fun p ↦ hm.comp (measurable_id.prodMk measurable_const)
  have hsections : ∀ᵐ z ∂lambda.restrict s,
      ContinuousOn (fun p ↦ coeff (z, p)) T ∧
        (HasOriginalSeedPairWindow S a μ ν l r z ∧ Good z) := by
    filter_upwards [hgood] with z hz
    exact ⟨(hz.1.continuousOn_rootCoefficient S hF hcomplete hu ha hinj hlr).mono hTsub, hz⟩
  exact exists_lusin_compact_continuous_sections_on hs hfinite hT
    (fun z p ↦ coeff (z, p)) heval hsections hε

end OTSelector.Reconstruction
