import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
## Lemma skeleton

* **Conditions:** A finite-dimensional real normed ambient space of dimension at least two with any additive Haar measure; a differentiable or Lipschitz real-parameter curve. Manifold versions assume the original measure is chartwise absolutely continuous and the curve is C1.
* **Objects:** Haar-null curve images/ranges and original-measure nullity of chartwise smooth manifold curves and their subsets.
* **Proof detail:** Use Hausdorff dimension/diameter covers and countable Lipschitz pieces to obtain zero ambient volume. Cover the real parameter by compact intervals or countably many chart preimages, transfer nullity through the supplied chartwise absolute continuity and sum.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 2*, Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38
* D. H. Fremlin, *Measure Theory, Volume 2*, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
  https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Lower-dimensional-image corollary of Hausdorff Lipschitz distortion and the top-dimensional Haar/Lebesgue comparison. The manifold transfer uses a countable time cover and does not require a countable global atlas.
-/

/-!
# Null volume of actual curves in dimension at least two

Differentiable and Lipschitz images of real sets have Hausdorff dimension at most one.
Haar measure in the ambient finite-dimensional space therefore vanishes on them.
The full curve is explicitly covered by the images of countably many compact time
intervals. Chartwise absolute continuity transfers the conclusion to original
manifold measures, using a countable subcover in time rather than a countable atlas.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal NNReal MeasureTheory

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A differentiable real-parameter image is Haar null in every ambient dimension
at least two, with no boundedness or measurability requirement on the time set. -/
theorem haar_curve_image_eq_zero_of_differentiableOn
    (μ : Measure E) [IsAddHaarMeasure μ] (hdim : 2 ≤ Module.finrank ℝ E)
    {γ : ℝ → E} {s : Set ℝ} (hγ : DifferentiableOn ℝ γ s) : μ (γ '' s) = 0 := by
  have hμ : μ ≪ (μH[Module.finrank ℝ E] : Measure E) :=
    absolutelyContinuous_isAddHaarMeasure μ _
  apply measure_zero_of_dimH_lt
    (d := (Module.finrank ℝ E : ℝ≥0))
    (by simpa only [NNReal.coe_natCast] using hμ)
  calc
    dimH (γ '' s) ≤ dimH s := hγ.dimH_image_le
    _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ s)
    _ = 1 := Real.dimH_univ
    _ < ((Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast (show 1 < Module.finrank ℝ E by omega)

/-- A Lipschitz real-parameter image is Haar null in every ambient dimension at
least two. The Lipschitz constant can be arbitrary. -/
theorem haar_curve_image_eq_zero_of_lipschitzOn
    (μ : Measure E) [IsAddHaarMeasure μ] (hdim : 2 ≤ Module.finrank ℝ E)
    {γ : ℝ → E} {s : Set ℝ} {C : ℝ≥0} (hγ : LipschitzOnWith C γ s) :
    μ (γ '' s) = 0 := by
  have hμ : μ ≪ (μH[Module.finrank ℝ E] : Measure E) :=
    absolutelyContinuous_isAddHaarMeasure μ _
  apply measure_zero_of_dimH_lt
    (d := (Module.finrank ℝ E : ℝ≥0))
    (by simpa only [NNReal.coe_natCast] using hμ)
  calc
    dimH (γ '' s) ≤ dimH s := hγ.dimH_image_le
    _ ≤ dimH (univ : Set ℝ) := dimH_mono (subset_univ s)
    _ = 1 := Real.dimH_univ
    _ < ((Module.finrank ℝ E : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast (show 1 < Module.finrank ℝ E by omega)

private theorem range_eq_iUnion_compact_intervals {X : Type*} (γ : ℝ → X) :
    range γ = ⋃ n : ℕ, γ '' Icc (-(n : ℝ)) n := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    exact mem_iUnion.mpr ⟨n, t, ⟨by linarith [neg_abs_le t],
      (le_abs_self t).trans hn.le⟩, rfl⟩
  · intro hx
    obtain ⟨n, t, _, rfl⟩ := mem_iUnion.mp hx
    exact mem_range_self t

/-- A globally C1 curve has Haar-null full range, by its explicit countable
cover with images of compact time intervals. -/
theorem haar_curve_range_eq_zero_of_contDiff
    (μ : Measure E) [IsAddHaarMeasure μ] (hdim : 2 ≤ Module.finrank ℝ E)
    {γ : ℝ → E} (hγ : ContDiff ℝ 1 γ) : μ (range γ) = 0 := by
  rw [range_eq_iUnion_compact_intervals, measure_iUnion_null_iff]
  intro n
  exact haar_curve_image_eq_zero_of_differentiableOn μ hdim
    (hγ.differentiable one_ne_zero).differentiableOn

/-- A globally Lipschitz curve has Haar-null full range, including unbounded
curves and arbitrary Lipschitz constants. -/
theorem haar_curve_range_eq_zero_of_lipschitz
    (μ : Measure E) [IsAddHaarMeasure μ] (hdim : 2 ≤ Module.finrank ℝ E)
    {γ : ℝ → E} {C : ℝ≥0} (hγ : LipschitzWith C γ) : μ (range γ) = 0 := by
  rw [range_eq_iUnion_compact_intervals, measure_iUnion_null_iff]
  intro n
  exact haar_curve_image_eq_zero_of_lipschitzOn μ hdim hγ.lipschitzOnWith

section Manifold

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]

private theorem measure_chart_curve_image_eq_zero
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) (old : M)
    (hac : (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ μ) :
    ν (γ '' (γ ⁻¹' (extChartAt 𝓘(ℝ, E) old).source)) = 0 := by
  let χ := extChartAt 𝓘(ℝ, E) old
  let T : Set ℝ := γ ⁻¹' χ.source
  have hcoord : DifferentiableOn ℝ (χ ∘ γ) T := by
    intro t ht
    change γ t ∈ χ.source at ht
    have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 χ (γ t) :=
      contMDiffAt_extChartAt' (by simpa only [χ, extChartAt_source] using ht)
    exact (((hchart.comp t (hγ t)).contDiffAt).differentiableAt
      one_ne_zero).differentiableWithinAt
  have hnull : μ ((χ ∘ γ) '' T) = 0 :=
    haar_curve_image_eq_zero_of_differentiableOn μ hdim hcoord
  have hchart : AEMeasurable χ (ν.restrict χ.source) :=
    (continuousOn_extChartAt old).aemeasurable (isOpen_extChartAt_source old).measurableSet
  have himage : (ν.restrict χ.source).map χ (χ '' (γ '' T)) = 0 := by
    rw [image_image]
    exact hac hnull
  have hrestrict : ν.restrict χ.source (γ '' T) = 0 :=
    nonpos_iff_eq_zero.mp ((le_map_apply_image hchart _).trans_eq himage)
  have hsub : γ '' T ⊆ χ.source := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht
  simpa only [inter_eq_left.mpr hsub] using measure_inter_eq_zero_of_restrict hrestrict

/-- A C1 manifold curve is null for any original measure whose restrictions to
chart domains push forward absolutely continuously with respect to model Haar
measure. A countable cover is selected on the time axis, so no countability of
the manifold or supplied countable chart family is required. -/
theorem measure_curve_range_eq_zero_of_chartwise_ac
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hac : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ μ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) : ν (range γ) = 0 := by
  classical
  let U : ℝ → Set ℝ := fun t ↦ γ ⁻¹' (extChartAt 𝓘(ℝ, E) (γ t)).source
  have hU (t : ℝ) : IsOpen (U t) :=
    (isOpen_extChartAt_source (γ t)).preimage hγ.continuous
  have hcover : univ ⊆ ⋃ t, U t := by
    intro t _
    exact mem_iUnion.mpr ⟨t, mem_extChartAt_source (γ t)⟩
  obtain ⟨S, hS, hScov⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have hnull : ν (⋃ t ∈ S, γ '' U t) = 0 := by
    apply (measure_biUnion_null_iff hS).mpr
    intro t _
    exact measure_chart_curve_image_eq_zero μ ν hdim hγ (γ t) (hac (γ t))
  apply measure_mono_null _ hnull
  rintro _ ⟨t, rfl⟩
  obtain ⟨j, hjS, htj⟩ := mem_iUnion₂.mp (hScov (mem_univ t))
  exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjS, mem_image_of_mem γ htj⟩⟩

/-- The same nullity applies to every subset of one actual C1 manifold curve,
without a measurability assumption on that subset. -/
theorem measure_eq_zero_of_subset_curve_range
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hac : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ μ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ)
    {S : Set M} (hS : S ⊆ range γ) : ν S = 0 :=
  measure_mono_null hS (measure_curve_range_eq_zero_of_chartwise_ac μ ν hdim hac hγ)

end Manifold

end OTSelector.Geometry
