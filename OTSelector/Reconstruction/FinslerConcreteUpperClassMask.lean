import OTSelector.Reconstruction.FinslerConcreteUpperClassModel
import OTSelector.Finite.NestedRelationClock

/-!
The literal retained-window finite class mask has nested row neighborhoods.
The proof uses actual original pair witnesses and the scalar gap, including
endpoint ties and empty bins. No topological shape of a clock bin is required.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The actual retained-window class mask is a finite Ferrers relation. Its
rows are nested for arbitrary measurable bins, including all endpoint ties. -/
theorem OriginalPopulationCoefficientCore.clockClassAllowed_rows_nested
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (i i' : Fin Q.count) :
    {j | C.clockClassAllowed Q i j} ⊆ {j | C.clockClassAllowed Q i' j} ∨
      {j | C.clockClassAllowed Q i' j} ⊆ {j | C.clockClassAllowed Q i j} := by
  classical
  by_cases hsub : ∀ j, C.clockClassAllowed Q i j → C.clockClassAllowed Q i' j
  · exact Or.inl hsub
  · right
    push Not at hsub
    obtain ⟨j, hij, hi'j⟩ := hsub
    obtain ⟨p, hp, hpi, hpj⟩ := hij
    intro k hi'k
    obtain ⟨r, hr, hri', hrk⟩ := hi'k
    have hpgap : (C.window.val.2.2 : ℝ) ≤ p.2 - p.1 := hp.2
    have hrgap : (C.window.val.2.2 : ℝ) ≤ r.2 - r.1 := hr.2
    by_cases hsource : p.1 ≤ r.1
    · refine ⟨(p.1, r.2), ⟨⟨hp.1.1, hr.1.2⟩, ?_⟩, hpi, hrk⟩
      change (C.window.val.2.2 : ℝ) ≤ r.2 - p.1
      linarith
    · have hother : C.clockClassAllowed Q i' j := by
        refine ⟨(r.1, p.2), ⟨⟨hr.1.1, hp.1.2⟩, ?_⟩, hri', hpj⟩
        change (C.window.val.2.2 : ℝ) ≤ p.2 - r.1
        have hlt : r.1 < p.1 := lt_of_not_ge hsource
        linarith
      exact False.elim (hi'j hother)


/-- The exact original finite mask has strict scalar rank clocks. These encode
only the allowed graph; the raw physical clocks and original costs stay in the
model data. Every class pair has a uniform half-integer gap. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_strict_clocks
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width) :
    ∃ (sourceClock targetClock : Fin Q.count → ℝ),
      (∀ i j, C.clockClassAllowed Q i j ↔ sourceClock i < targetClock j) ∧
      (∀ i j, (1 / 2 : ℝ) ≤ |targetClock j - sourceClock i|) ∧
      (∀ i, -((Q.count : ℝ) + 1) ≤ sourceClock i ∧ sourceClock i ≤ 1) ∧
      (∀ j, -((Q.count : ℝ) + 1) ≤ targetClock j ∧ targetClock j ≤ 1) := by
  have hnested : ∀ i i', (∀ j, C.clockClassAllowed Q i j → C.clockClassAllowed Q i' j) ∨
      (∀ j, C.clockClassAllowed Q i' j → C.clockClassAllowed Q i j) := by
    intro i i'
    rcases C.clockClassAllowed_rows_nested Q i i' with h | h
    · exact Or.inl (fun j hj ↦ h hj)
    · exact Or.inr (fun j hj ↦ h hj)
  simpa only [Fintype.card_fin] using
    OTSelector.FiniteRelation.exists_strict_clocks_of_nested_relation (C.clockClassAllowed Q) hnested


variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]

/-- The full clock model also keeps both raw endpoints inside the original
outer scalar window. Overflow bins never enter its retained main mask. -/
theorem OriginalPopulationCoefficientCore.exists_full_clockClass_model_with_endpoints
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFullModelEndpointMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ) (hf : Continuous f)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ Q : FiniteScalarBins I globalGap,
      ∀ i j, C.clockClassAllowed Q i j → ∀ x ∈ Q.cell i, ∀ y ∈ Q.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        (C.window.val.2.2 : ℝ) / 2 ≤ y - x ∧ x < y ∧
        (∀ v, |matrixQuadratic (C.matrix z₀ (x, y)) v - C.clockClassKinetic Q z₀ i j v| ≤
          ε * C.clockClassKinetic Q z₀ i j v) ∧
        |originalReferenceClockProbe C z₀ hz₀ f (x, y) -
          C.clockClassProbe Q z₀ hz₀ f i j| ≤ B := by
  classical
  obtain ⟨width, hwidth, localBins, hlocal⟩ :=
    C.exists_legal_clock_resampling_bins hF hcomplete hu ha hinj z₀ hz₀ f hf hε hB
  obtain ⟨full, tag, htag⟩ :=
    exists_finiteScalarBins_refining_with_overflow hI measurableSet_Icc localBins hglobalGap
  refine ⟨full, fun i j hij x hx y hy ↦ ?_⟩
  have hp := C.clockClassReference_mem full hij
  let p₀ := C.clockClassReference full i j
  have hi : ∃ k, tag i = some k := by
    cases heq : tag i with
    | none =>
      have hn := htag i hp.2.1
      rw [heq] at hn
      exact False.elim (hn hp.1.1.1)
    | some k => exact ⟨k, rfl⟩
  have hj : ∃ k, tag j = some k := by
    cases heq : tag j with
    | none =>
      have hn := htag j hp.2.2
      rw [heq] at hn
      exact False.elim (hn hp.1.1.2)
    | some k => exact ⟨k, rfl⟩
  obtain ⟨ki, hki⟩ := hi
  obtain ⟨kj, hkj⟩ := hj
  have hisub : full.cell i ⊆ localBins.cell ki := by
    simpa only [hki, FiniteScalarBins.overflowCell] using htag i
  have hjsub : full.cell j ⊆ localBins.cell kj := by
    simpa only [hkj, FiniteScalarBins.overflowCell] using htag j
  refine ⟨localBins.subset ki (hisub hx), localBins.subset kj (hjsub hy), ?_⟩
  have h := hlocal ki kj p₀ hp.1 (hisub hp.2.1) (hjsub hp.2.2) x (hisub hx) y (hjsub hy)
  simpa only [clockClassKinetic, clockClassMatrix, clockClassProbe, ite_eq_left hij] using h

end OTSelector.Reconstruction
