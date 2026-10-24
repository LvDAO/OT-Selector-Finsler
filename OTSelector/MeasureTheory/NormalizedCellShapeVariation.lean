import Mathlib.Analysis.BoxIntegral.UnitPartition
import OTSelector.MeasureTheory.DominatedKernelVariation
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
import OTSelector.MeasureTheory.WeightedKernelVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerConcreteUpperShapeLaw.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerConcreteUpperShapeLaw`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.NormalizedCellShapeVariation

## Lemma skeleton

* **Conditions:** Actual weighted conditional laws and a frozen probability mark law on two finite-mass measurable cell shapes, common dominating mark reference, density/mark oscillation control and positive masses for normalization.
* **Objects:** Exact shape variation, raw actual-cell versus frozen-cube variation and normalized law bounds.
* **Proof detail:** The variation of two restrictions is the original symmetric-difference mass. Add weighted-kernel oscillation error, then compare normalizers only after retaining both raw masses and divide by the actual positive mass.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).

Source relation (composition): Shape/intensity/conditional-law error assembly with full variation; cube-uniformity of the original law is not imposed.
-/

/-!
The actual retained population law is compared to a frozen product law on
approximating cubes. Density and conditional clock oscillation are paid on the
original cell; changing its shape costs its original reference symmetric
difference. Normalization is performed only after keeping both raw masses.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff

noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

/-- Changing the restriction set of a single reference law has full signed
variation exactly its original symmetric-difference mass. -/
theorem totalVariation_sub_restrict_eq_symmDiff
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {s C : Set X}
    (hs : MeasurableSet s) (hC : MeasurableSet C)
    [IsFiniteMeasure (μ.restrict s)] [IsFiniteMeasure (μ.restrict C)] :
    ((μ.restrict s).toSignedMeasure - (μ.restrict C).toSignedMeasure).totalVariation univ =
      μ (s ∆ C) := by
  classical
  have hws : μ.withDensity (s.indicator (fun _ ↦ (1 : ℝ≥0∞))) = μ.restrict s := by
    rw [withDensity_indicator hs]
    exact withDensity_one
  have hwC : μ.withDensity (C.indicator (fun _ ↦ (1 : ℝ≥0∞))) = μ.restrict C := by
    rw [withDensity_indicator hC]
    exact withDensity_one
  rw [totalVariation_sub_eq_lintegral_toReal μ _ _
    ((measurable_const.indicator hs).aemeasurable)
    ((measurable_const.indicator hC).aemeasurable) hws hwC]
  have hpoint : (fun x ↦ ‖(s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x).toReal -
      (C.indicator (fun _ ↦ (1 : ℝ≥0∞)) x).toReal‖ₑ) =
      (s ∆ C).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext x
    by_cases hxs : x ∈ s <;> by_cases hxC : x ∈ C <;>
      simp [hxs, hxC, Set.mem_symmDiff]
  rw [hpoint, lintegral_indicator (hs.symmDiff hC)]
  simp

/-- The shape cost of a frozen constant-density product law is exactly the
frozen intensity times the original reference shape mismatch. -/
theorem totalVariation_frozen_product_shape_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {s C : Set X} (hs : MeasurableSet s) (hC : MeasurableSet C)
    [IsFiniteMeasure (μ.restrict s)] [IsFiniteMeasure (μ.restrict C)]
    (density : ℝ≥0) :
    ((density • (μ.restrict s).prod ν).toSignedMeasure -
      (density • (μ.restrict C).prod ν).toSignedMeasure).totalVariation univ =
      (density : ℝ≥0∞) * μ (s ∆ C) := by
  let base : Measure (X × Y) := density • μ.prod ν
  have heqs : base.restrict (s ×ˢ univ) = density • (μ.restrict s).prod ν := by
    dsimp only [base]
    rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ]
  have heqC : base.restrict (C ×ˢ univ) = density • (μ.restrict C).prod ν := by
    dsimp only [base]
    rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ]
  haveI : IsFiniteMeasure (base.restrict (s ×ˢ univ)) := by rw [heqs]; infer_instance
  haveI : IsFiniteMeasure (base.restrict (C ×ˢ univ)) := by rw [heqC]; infer_instance
  have h := totalVariation_sub_restrict_eq_symmDiff base
    (hs.prod MeasurableSet.univ) (hC.prod MeasurableSet.univ)
  have hset : (s ×ˢ (univ : Set Y)) ∆ (C ×ˢ univ) = (s ∆ C) ×ˢ univ := by
    ext p
    simp [Set.mem_symmDiff]
  have hvalue : base ((s ×ˢ (univ : Set Y)) ∆ (C ×ˢ univ)) =
      (density : ℝ≥0∞) * μ (s ∆ C) := by
    rw [hset]
    dsimp only [base]
    rw [Measure.smul_apply, Measure.prod_prod, measure_univ, mul_one]
    rfl
  rw [hvalue] at h
  simpa only [heqs, heqC] using h

/-- The actual raw density and conditional clock law on a retained cell are
compared to the frozen product law on full cubes. This explicitly pays for
both the cell oscillation and the added/removed reference volume. -/
theorem totalVariation_actual_cell_sub_frozen_cubes_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure X) [SFinite μ]
    {s C : Set X} (hs : MeasurableSet s) (hC : MeasurableSet C)
    [IsFiniteMeasure (μ.restrict s)] [IsFiniteMeasure (μ.restrict C)]
    (τ : Measure Y) [SFinite τ]
    (clock : Kernel X Y) [IsMarkovKernel clock]
    (frozenClock : Measure Y) [IsProbabilityMeasure frozenClock]
    {ρ : X → ℝ≥0∞} [IsFiniteMeasure ((μ.restrict s).withDensity ρ)]
    (hρ : Measurable ρ)
    (hac : ∀ᵐ x ∂μ.restrict s, clock x ≪ τ) (hfac : frozenClock ≪ τ)
    {density tolerance : ℝ} (hdensity : 0 ≤ density) (htolerance : 0 ≤ tolerance)
    (hclose : ∀ᵐ x ∂μ.restrict s, |(ρ x).toReal - density| ≤ tolerance * density)
    (hclock : ∀ᵐ x ∂μ.restrict s,
      ((clock x).toSignedMeasure - frozenClock.toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal tolerance) :
    ((((μ.restrict s).withDensity ρ).compProd clock).toSignedMeasure -
      (density.toNNReal • (μ.restrict C).prod frozenClock).toSignedMeasure).totalVariation univ ≤
      ENNReal.ofReal (2 * tolerance * density) * μ s +
        ENNReal.ofReal density * μ (s ∆ C) := by
  have hraw := totalVariation_weighted_compProd_le_of_absolutelyContinuous
    (μ.restrict s) τ clock frozenClock hρ hac hfac hdensity htolerance hclose hclock
  rw [Measure.restrict_apply_univ] at hraw
  let actual := ((μ.restrict s).withDensity ρ).compProd clock
  let frozenCell := density.toNNReal • (μ.restrict s).prod frozenClock
  let frozenCubes := density.toNNReal • (μ.restrict C).prod frozenClock
  have hsplit : actual.toSignedMeasure - frozenCubes.toSignedMeasure =
      (actual.toSignedMeasure - frozenCell.toSignedMeasure) +
        (frozenCell.toSignedMeasure - frozenCubes.toSignedMeasure) := by abel
  change (actual.toSignedMeasure - frozenCubes.toSignedMeasure).totalVariation univ ≤ _
  rw [hsplit]
  have htriangle := VectorMeasure.variation_add_le (μ :=
    actual.toSignedMeasure - frozenCell.toSignedMeasure)
    (ν := frozenCell.toSignedMeasure - frozenCubes.toSignedMeasure) univ
  simp only [← SignedMeasure.totalVariation_eq_variation] at htriangle
  have hshape := totalVariation_frozen_product_shape_eq μ frozenClock hs hC density.toNNReal
  simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hdensity] using
    htriangle.trans (add_le_add hraw hshape.le)

/-- The normalized actual/frozen law discrepancy is controlled by raw
variation divided by the actual original mass. Mass error is derived from
variation, rather than assumed to vanish or calibrated independently. -/
theorem totalVariation_normalized_le_twice_raw
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : 0 < μ.real univ) (hν : 0 < ν.real univ) :
    ((normalizedFiniteLaw μ).toSignedMeasure -
      (normalizedFiniteLaw ν).toSignedMeasure).totalVariation.real univ ≤
      2 * (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ / μ.real univ := by
  have hmass := (μ.toSignedMeasure - ν.toSignedMeasure).norm_le_totalVariation univ
  simp only [Real.norm_eq_abs, FunLike.coe_sub, Pi.sub_apply,
    Measure.toSignedMeasure_apply_measurable MeasurableSet.univ] at hmass
  exact (totalVariation_normalizedFiniteLaw_le μ ν hμ hν).trans
    (div_le_div_of_nonneg_right (by linarith) hμ.le)


/-- The normalized original cell law is close to the frozen product on the
produced cubes, with the actual original mass as denominator. The two raw
laws may have different masses. -/
theorem totalVariation_normalized_actual_cell_sub_frozen_cubes_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure X) [SFinite μ]
    {s C : Set X} (hs : MeasurableSet s) (hC : MeasurableSet C)
    [IsFiniteMeasure (μ.restrict s)] [IsFiniteMeasure (μ.restrict C)]
    (τ : Measure Y) [SFinite τ]
    (clock : Kernel X Y) [IsMarkovKernel clock]
    (frozenClock : Measure Y) [IsProbabilityMeasure frozenClock]
    {ρ : X → ℝ≥0∞} [IsFiniteMeasure ((μ.restrict s).withDensity ρ)]
    (hρ : Measurable ρ)
    (hac : ∀ᵐ x ∂μ.restrict s, clock x ≪ τ) (hfac : frozenClock ≪ τ)
    {density tolerance : ℝ} (hdensity : 0 ≤ density) (htolerance : 0 ≤ tolerance)
    (hclose : ∀ᵐ x ∂μ.restrict s, |(ρ x).toReal - density| ≤ tolerance * density)
    (hclock : ∀ᵐ x ∂μ.restrict s,
      ((clock x).toSignedMeasure - frozenClock.toSignedMeasure).totalVariation univ ≤
        ENNReal.ofReal tolerance)
    (hactual : 0 < ((((μ.restrict s).withDensity ρ).compProd clock).real univ))
    (hfrozen : 0 < (density.toNNReal • (μ.restrict C).prod frozenClock).real univ) :
    (((normalizedFiniteLaw (((μ.restrict s).withDensity ρ).compProd clock)).toSignedMeasure -
      (normalizedFiniteLaw (density.toNNReal • (μ.restrict C).prod frozenClock)).toSignedMeasure
      ).totalVariation.real univ) ≤
      2 * (2 * tolerance * density * μ.real s + density * μ.real (s ∆ C)) /
        (((μ.restrict s).withDensity ρ).compProd clock).real univ := by
  have hsm : μ s ≠ ∞ := by simpa only [Measure.restrict_apply_univ] using
    (measure_ne_top (μ.restrict s) univ)
  have hCm : μ C ≠ ∞ := by simpa only [Measure.restrict_apply_univ] using
    (measure_ne_top (μ.restrict C) univ)
  have hdiff : μ (s ∆ C) ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hsm, hCm⟩)
    ((measure_mono Set.symmDiff_subset_union).trans (measure_union_le s C))
  have htop₁ : ENNReal.ofReal (2 * tolerance * density) * μ s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsm
  have htop₂ : ENNReal.ofReal density * μ (s ∆ C) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdiff
  have hraw := totalVariation_actual_cell_sub_frozen_cubes_le μ hs hC τ clock frozenClock
    hρ hac hfac hdensity htolerance hclose hclock
  have hrawR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨htop₁, htop₂⟩) hraw
  simp only [ENNReal.toReal_add htop₁ htop₂, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hdensity,
    ENNReal.toReal_ofReal (show 0 ≤ 2 * tolerance * density by positivity)] at hrawR
  have hnorm := totalVariation_normalized_le_twice_raw
    (((μ.restrict s).withDensity ρ).compProd clock)
    (density.toNNReal • (μ.restrict C).prod frozenClock) hactual hfrozen
  exact hnorm.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hrawR (by norm_num)) hactual.le)

end OTSelector.Reconstruction

end
end
