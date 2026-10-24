import OTSelector.Reconstruction.FinslerOriginalCoarseClockRepair
import OTSelector.Reconstruction.MarkedStationaryValueLegalFiniteClassLimit
import OTSelector.Reconstruction.MarkedStationaryValueLegalDyadicComparison

/-! The original supported continuous-clock pressure has its actual scalar
legal graph. Fine coefficient class masks can be removed exactly from that
graph, without changing the original iid law, counts, or costs. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- Equality of the legal mask at almost every original independent mark pair
preserves the full original Poisson pressure exactly. -/
theorem finiteClassLegalPressure_eq_clock_of_ae
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (allowed : A → B → Prop) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hcode : ∀ᵐ p ∂α.prod β, allowed p.1 p.2 ↔ source p.1 < target p.2)
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ) :
    finiteClassLegalPressure q allowed α β r kin probe t =
      legalMarkedPressure q source target α β r kin probe t := by
  apply integral_congr_ae
  filter_upwards [ae_all_crossMarks q α β r
    (fun p ↦ allowed p.1 p.2 ↔ source p.1 < target p.2) hcode] with sample hs
  have hgraph : finiteClassLegalGraph q (mSourceCount sample) (mTargetCount sample) allowed sample =
      legalMarkedGraph q (mSourceCount sample) (mTargetCount sample) source target sample := by
    ext e
    simp only [finiteClassLegalGraph,legalMarkedGraph,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hs e.1.val e.2.val
  simp only [finiteClassLegalTilted,legalMarkedTilted,legalMarkedFixedValue,hgraph]


/-- Spatial normalization preserves the exact original almost-everywhere
identification of the fine mask with scalar legality. -/
theorem finiteClassLegalScalePressure_eq_clock_of_ae
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (q : ℕ) (allowed : A → B → Prop) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hcode : ∀ᵐ p ∂α.prod β, allowed p.1 p.2 ↔ source p.1 < target p.2)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (R t : ℝ) :
    finiteClassLegalScalePressure q allowed α β kin probe R t =
      legalMarkedScalePressure q source target α β kin probe R t := by
  by_cases hR : 0 < R
  · simp only [finiteClassLegalScalePressure,legalMarkedScalePressure,hR,↓reduceIte]
    rw [finiteClassLegalPressure_eq_clock_of_ae q allowed source target α β hcode]
  · simp only [finiteClassLegalScalePressure,legalMarkedScalePressure,hR,↓reduceIte]

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}


/-- On the actual original retained clock populations, the fine observed mask
is exactly original scalar legality; its pressure is independent of mask coding. -/
theorem OriginalPopulationCoefficientCore.fine_clock_pressure_eq_original_scalar
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width gap : ℝ} (fine : FiniteScalarBins range width)
    (hwindowGap : (C.window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ i j, C.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧
        y ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 ∧ x < y)
    (α β : Measure range) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : ∀ᵐ x ∂α, x.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hβ : ∀ᵐ y ∂β, y.val ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |p.2.val - p.1.val|)
    (q : ℕ) (r : ℝ≥0) (kin : range → range → (Fin q → ℝ) → ℝ)
    (probe : range → range → ℝ) (t : ℝ) :
    finiteClassLegalPressure q (fun x y ↦ C.clockClassAllowed fine
        (fine.rangeClassify x) (fine.rangeClassify y)) α β r kin probe t =
      legalMarkedPressure q Subtype.val Subtype.val α β r kin probe t := by
  apply finiteClassLegalPressure_eq_clock_of_ae
  filter_upwards [ae_fst_of_ae hα,ae_snd_of_ae hβ,hsep] with p hp₁ hp₂ hpSep
  rw [C.fine_clock_mask_iff_screened_order fine hwindowGap hfull _ _ hpSep]
  simp only [hp₁,hp₂,true_and]

end OTSelector.Reconstruction
