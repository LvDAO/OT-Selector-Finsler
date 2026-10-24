import OTSelector.Reconstruction.FinslerConcreteUpperClassCost
import OTSelector.Reconstruction.FiniteScalarBins

/-!
Small original scalar bins touched by a retained legal pair have legal full
rectangles. The actual reference coefficient remains continuous and elliptic
on a half-gap enlargement by its original conditional moment witness, so raw
within-bin clocks need not stay in the narrower original pair window.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
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

/-- The actual reference probe is continuous in both original clock variables. -/
theorem continuous_originalReferenceClockProbe
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex) (z₀ : Z) (hz₀ : z₀ ∈ C.roots)
    (f : M × M → ℝ) (hf : Continuous f) :
    Continuous (originalReferenceClockProbe C z₀ hz₀ f) := by
  let S := (P C.seedIndex).seed
  let w := populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z₀, C.roots_subset_piece hz₀⟩
  have hc : Continuous (S.curve w.val) := continuous_iff_continuousAt.mpr fun t ↦
    (hF.contMDiffAt_of_isEulerLagrangeAt (S.complete w.val w.property t (mem_univ _))).continuousAt
  exact hf.comp ((hc.comp (continuous_fst.sub continuous_const)).prodMk
    (hc.comp (continuous_snd.sub continuous_const)))

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]

/-- The original data produce finite bins with legal raw rectangles and relative
coefficient/probe comparison against every retained pair in the same two bins. -/
theorem OriginalPopulationCoefficientCore.exists_legal_clock_resampling_bins
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instLegalBinsMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ) (hf : Continuous f)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ width : ℝ, 0 < width ∧
      ∃ Q : FiniteScalarBins (Icc (C.window.val.1 : ℝ) C.window.val.2.1) width,
        ∀ i j (p₀ : ℝ × ℝ), p₀ ∈ C.window.region →
          p₀.1 ∈ Q.cell i → p₀.2 ∈ Q.cell j →
          ∀ x ∈ Q.cell i, ∀ y ∈ Q.cell j,
            (C.window.val.2.2 : ℝ) / 2 ≤ y - x ∧ x < y ∧
            (∀ v, |matrixQuadratic (C.matrix z₀ (x, y)) v -
                matrixQuadratic (C.matrix z₀ p₀) v| ≤
              ε * matrixQuadratic (C.matrix z₀ p₀) v) ∧
            |originalReferenceClockProbe C z₀ hz₀ f (x, y) -
              originalReferenceClockProbe C z₀ hz₀ f p₀| ≤ B := by
  let l : ℝ := C.window.val.1
  let r : ℝ := C.window.val.2.1
  let gap : ℝ := C.window.val.2.2
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact_mod_cast C.window.property.2
  have hlr : l ≤ r := by
    dsimp only [l, r]
    exact_mod_cast C.window.property.1.le
  let H : Set (ℝ × ℝ) := (Icc l r ×ˢ Icc l r) ∩ {p | gap / 2 ≤ p.2 - p.1}
  have hH : IsCompact H := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_fst))
  have hHsub : H ⊆ {p | p.1 ∈ Icc l r ∧ p.2 ∈ Icc l r ∧ p.1 < p.2} := by
    intro p hp
    exact ⟨hp.1.1, hp.1.2, sub_pos.mp ((half_pos hgap).trans_le hp.2)⟩
  have hwindow := C.original_window z₀ hz₀
  have hA : ContinuousOn (C.matrix z₀) H :=
    (hwindow.continuousOn_rootCoefficient (P C.seedIndex).seed hF hcomplete hu ha hinj hlr).mono hHsub
  have hpos : ∀ p ∈ H, (C.matrix z₀ p).PosDef := fun p hp ↦
    hwindow.posDef_rootCoefficient (P C.seedIndex).seed hF hcomplete hu ha hinj (hHsub hp)
  obtain ⟨meshA, hmeshA, hrelative⟩ := exists_uniform_relative_matrixQuadratic hH hA hpos hε
  obtain ⟨meshP, hmeshP, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hH.uniformContinuousOn_of_continuous
      (continuous_originalReferenceClockProbe C hF z₀ hz₀ f hf).continuousOn) B hB
  let width := min gap (min meshA meshP)
  have hwidth : 0 < width := lt_min hgap (lt_min hmeshA hmeshP)
  obtain ⟨Q⟩ := exists_finiteScalarBins (I := Icc l r) isCompact_Icc hwidth
  refine ⟨width, hwidth, Q, fun i j p₀ hp₀ hs₀ ht₀ x hx y hy ↦ ?_⟩
  have hxclose := Q.diameter i x hx p₀.1 hs₀
  have hyclose := Q.diameter j y hy p₀.2 ht₀
  have hwgap : width ≤ gap := min_le_left _ _
  have hnewgap : gap / 2 ≤ y - x := by
    have hs := (abs_le.mp hxclose).2
    have ht := (abs_le.mp hyclose).1
    have hg : gap ≤ p₀.2 - p₀.1 := hp₀.2
    linarith
  have hpH : (x, y) ∈ H := ⟨⟨Q.subset i hx, Q.subset j hy⟩, hnewgap⟩
  have hp₀H : p₀ ∈ H := ⟨hp₀.1, by
    change gap / 2 ≤ p₀.2 - p₀.1
    have hg : gap ≤ p₀.2 - p₀.1 := hp₀.2
    linarith⟩
  have hdist : dist (x, y) p₀ < min meshA meshP := by
    have hw : width ≤ min meshA meshP := min_le_right _ _
    have hquarter : width / 4 < min meshA meshP := by linarith
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt_iff.mpr ⟨hxclose.trans_lt hquarter, hyclose.trans_lt hquarter⟩
  refine ⟨hnewgap, sub_pos.mp ((half_pos hgap).trans_le hnewgap),
    hrelative (x, y) hpH p₀ hp₀H (hdist.trans_le (min_le_left _ _)), ?_⟩
  exact (show |originalReferenceClockProbe C z₀ hz₀ f (x, y) -
      originalReferenceClockProbe C z₀ hz₀ f p₀| < B by
    simpa only [Real.dist_eq] using hclose (x, y) hpH p₀ hp₀H
      (hdist.trans_le (min_le_right _ _))).le

end OTSelector.Reconstruction
