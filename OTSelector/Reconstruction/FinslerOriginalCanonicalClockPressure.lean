import OTSelector.Reconstruction.FinslerOriginalClockPressureScreen

/-! Fine resampling changes neither the original retained continuous clock
law nor its true scalar-legal pressure with the actual original coefficient. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- Changes of kernel or probe off actual original legal mark pairs do not
change the true original Poisson pressure. -/
theorem legalMarkedPressure_congr_of_ae_on_legal
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin kin' : A → B → (Fin q → ℝ) → ℝ) (probe probe' : A → B → ℝ)
    (hcost : ∀ᵐ p ∂α.prod β, source p.1 < target p.2 →
      (∀ v, kin p.1 p.2 v = kin' p.1 p.2 v) ∧ probe p.1 p.2 = probe' p.1 p.2)
    (r : ℝ≥0) (t : ℝ) :
    legalMarkedPressure q source target α β r kin probe t =
      legalMarkedPressure q source target α β r kin' probe' t := by
  apply integral_congr_ae
  filter_upwards [ae_all_crossMarks q α β r (fun p ↦ source p.1 < target p.2 →
    (∀ v, kin p.1 p.2 v = kin' p.1 p.2 v) ∧ probe p.1 p.2 = probe' p.1 p.2) hcost]
    with sample hs
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j hij
  have hfwd : source (mSourceMark sample i) < target (mTargetMark sample j) := by
    simpa only [legalMarkedGraph,Finset.mem_filter,Finset.mem_univ,true_and] using hij
  have h := hs i.val j.val hfwd
  simp only [mKineticCost,mProbe,h.1,h.2]

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}


/-- On the actual original forward clock-pair law, the fine retained mask is
exactly the outer-window screen, independently of all coefficient bins. -/
theorem OriginalPopulationCoefficientCore.original_retained_clock_law_eq_outer_screen
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width gap : ℝ} (fine : FiniteScalarBins range width) (hgap : 0 < gap)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ i j, C.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
    (π : Measure (range × range)) (hforward : ∀ᵐ p ∂π, gap ≤ p.2.val - p.1.val) :
    π.restrict {p | C.clockClassAllowed fine (fine.rangeClassify p.1) (fine.rangeClassify p.2)} =
      π.restrict {p | p.1.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        p.2.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1} := by
  apply Measure.restrict_congr_set
  filter_upwards [hforward] with p hp
  apply propext
  change C.clockClassAllowed fine (fine.rangeClassify p.1) (fine.rangeClassify p.2) ↔
    p.1.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
      p.2.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1
  rw [C.fine_clock_mask_iff_screened_order fine hwindowGap hfull _ _
    (hp.trans (le_abs_self _))]
  have hfwd : p.1.val < p.2.val := sub_pos.mp (hgap.trans_le hp)
  simp only [hfwd,and_true]

/-- The actual original continuous coefficient, with true scalar legality,
has exactly the produced fine model's original pressure. No fine representative
coefficient or auxiliary rank clock remains on the right hand side. -/
theorem OriginalPopulationCoefficientCore.fine_clock_pressure_eq_canonical_original
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width gap : ℝ} (fine : FiniteScalarBins range width)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ i j, C.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|) (r : ℝ≥0) (t : ℝ) :
    finiteClassLegalPressure (finrank ℝ (P C.seedIndex).seed.covector.ker)
      (fun x y ↦ C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y)) α β r
      (C.originalMaskedClockKinetic fine z₀) (C.originalRangeClockProbe z₀ hz₀ f) t =
    legalMarkedPressure (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β r
      (fun x y v ↦ matrixQuadratic (C.matrix z₀ (x.val,y.val)) v)
      (C.originalRangeClockProbe z₀ hz₀ f) t := by
  rw [C.fine_clock_pressure_eq_original_scalar fine hwindowGap hfull α β hα hβ hsep]
  apply legalMarkedPressure_congr_of_ae_on_legal
  filter_upwards [ae_fst_of_ae hα,ae_snd_of_ae hβ,hsep] with p hp₁ hp₂ hpSep
  intro hforward
  have hallowed := (C.fine_clock_mask_iff_screened_order fine hwindowGap hfull _ _ hpSep).mpr
    ⟨hp₁,hp₂,hforward⟩
  refine ⟨?_,rfl⟩
  intro v
  simp only [OriginalPopulationCoefficientCore.originalMaskedClockKinetic,hallowed,↓reduceIte]

/-- The exact canonical original pressure identification holds at every real
spatial scale, before taking any thermodynamic or fine-bin limit. -/
theorem OriginalPopulationCoefficientCore.fine_clock_scalePressure_eq_canonical_original
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width gap : ℝ} (fine : FiniteScalarBins range width)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ i j, C.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|) (L t : ℝ) :
    finiteClassLegalScalePressure (finrank ℝ (P C.seedIndex).seed.covector.ker)
      (fun x y ↦ C.clockClassAllowed fine (fine.rangeClassify x) (fine.rangeClassify y)) α β
      (C.originalMaskedClockKinetic fine z₀) (C.originalRangeClockProbe z₀ hz₀ f) L t =
    legalMarkedScalePressure (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val α β
      (fun x y v ↦ matrixQuadratic (C.matrix z₀ (x.val,y.val)) v)
      (C.originalRangeClockProbe z₀ hz₀ f) L t := by
  by_cases hL : 0 < L
  · simp only [finiteClassLegalScalePressure,legalMarkedScalePressure,hL,↓reduceIte]
    rw [C.fine_clock_pressure_eq_canonical_original fine hwindowGap hfull z₀ hz₀ f α β hα hβ hsep]
  · simp only [finiteClassLegalScalePressure,legalMarkedScalePressure,hL,↓reduceIte]

end OTSelector.Reconstruction
