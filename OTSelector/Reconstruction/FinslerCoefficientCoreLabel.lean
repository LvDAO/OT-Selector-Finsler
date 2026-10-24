import OTSelector.Geometry.Finsler.Calibration.RootLabelValue
import OTSelector.Reconstruction.FinslerFiniteCoefficientCores

/-!
# Geometry.Finsler.Calibration.RootLabelValue

* **Conditions:** The actual seed-to-population label embedding with the stated inherited calibration, measurability and regular-domain injectivity hypotheses.
* **Objects:** A globally defined zero-extended original inverse seed label and its exact values on genuine roots and selected pieces.
* **Proof detail:** Extend the inverse of the Borel seed label embedding by zero, then evaluate the extension on its actual image.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (adapter): Only the inverse-label definition and its three elementary readout/measurability statements are selected; compact coefficient-core refinements are outside scope.
-/

/-!
# Continuous original labels on coefficient cores

The measurable inverse of the original population root map admits compact
continuity refinements. These refinements retain the same seed, scalar window,
actual coefficient and conditional laws, and their actual labels form compact sets.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}



variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instLabelCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj





variable {P : ℕ → F.CalibratedSeedWindow u}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}



variable [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z] [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

/-- A compact coefficient core has arbitrarily accurate compact refinements whose actual
seed labels vary continuously and form a compact subset of the original label set. -/
theorem OriginalPopulationCoefficientCore.exists_continuous_label_core
    {δ ε : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hε : ε ≠ 0) :
    ∃ K ⊆ C.roots, IsCompact K ∧ lambda (C.roots \ K) < ε ∧
      ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) K ∧
      IsCompact (populationSeedRootLabelValue (P C.seedIndex).seed a '' K) ∧
      populationSeedRootLabelValue (P C.seedIndex).seed a '' K ⊆ (P C.seedIndex).seed.labels ∧
      ∀ z ∈ K, a ((P C.seedIndex).seed.curve
        (populationSeedRootLabelValue (P C.seedIndex).seed a z) 0) = z := by
  obtain ⟨K, hsub, hK, hmass, hc⟩ := exists_lusin_compact_core (μ := lambda)
    C.roots_compact.measurableSet
    (measure_ne_top _ _)
    (measurable_populationSeedRootLabelValue (P C.seedIndex).seed hF hcomplete hu ha hinj) hε
  refine ⟨K, hsub, hK, hmass, hc, hK.image_of_continuousOn hc, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
      ⟨z, C.roots_subset_piece (hsub hz)⟩]
    exact (populationSeedPieceLabel P a κ lambda C.seedIndex
      ⟨z, C.roots_subset_piece (hsub hz)⟩).property
  · intro z hz
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
      ⟨z, C.roots_subset_piece (hsub hz)⟩]
    exact populationSeedPieceLabel_root P a κ lambda C.seedIndex
      ⟨z, C.roots_subset_piece (hsub hz)⟩

/-- Finitely many original coefficient cores admit simultaneous continuous-label
refinements, with one bound for their total lost original root mass. -/
theorem OriginalPopulationCoefficientCore.exists_finite_continuous_label_refinement
    {N : ℕ} {δ ε : ℝ≥0∞}
    (C : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hε : ε ≠ 0) :
    ∃ K : Fin N → Set Z,
      lambda ((⋃ i, (C i).roots) \ ⋃ i, K i) < ε ∧
      ∀ i, K i ⊆ (C i).roots ∧ IsCompact (K i) ∧
        ContinuousOn (populationSeedRootLabelValue (P (C i).seedIndex).seed a) (K i) ∧
        IsCompact (populationSeedRootLabelValue (P (C i).seedIndex).seed a '' K i) ∧
        populationSeedRootLabelValue (P (C i).seedIndex).seed a '' K i ⊆
          (P (C i).seedIndex).seed.labels ∧
        ∀ z ∈ K i, a ((P (C i).seedIndex).seed.curve
          (populationSeedRootLabelValue (P (C i).seedIndex).seed a z) 0) = z := by
  classical
  obtain ⟨τ, hτ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Fin N)
  choose K hsub hK hsmall hcont hcompact hlabels hroot using fun i ↦
    (C i).exists_continuous_label_core hF hcomplete hu ha hinj (hτ i).ne'
  refine ⟨K, ?_, fun i ↦ ⟨hsub i, hK i, hcont i, hcompact i, hlabels i, hroot i⟩⟩
  have hdiff : (⋃ i, (C i).roots) \ ⋃ i, K i ⊆ ⋃ i, (C i).roots \ K i := by
    rintro z ⟨hz, hnot⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i, hi, fun hki ↦ hnot (mem_iUnion.mpr ⟨i, hki⟩)⟩
  exact ((measure_mono hdiff).trans (measure_iUnion_le _)).trans_lt
    ((ENNReal.tsum_le_tsum fun i ↦ (hsmall i).le).trans_lt hsum)

omit [PolishSpace Z] [BorelSpace Z] [IsFiniteMeasure lambda] in
/-- The entire retained scalar window lies strictly inside the actual calibrated
time interval of its original inverse label. -/
theorem OriginalPopulationCoefficientCore.calibrated_label_interval
    {δ : ℝ≥0∞} (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {z : Z} (hz : z ∈ C.roots) :
    Icc ((C.window.val.1 : ℝ) - (P C.seedIndex).seed.level)
        ((C.window.val.2.1 : ℝ) - (P C.seedIndex).seed.level) ⊆
      interior ((P C.seedIndex).seed.calibrationTimes
        (populationSeedRootLabelValue (P C.seedIndex).seed a z)) := by
  obtain ⟨w, hw, D, hl, hr⟩ := C.original_window z hz
  rw [← hw, populationSeedRootLabelValue_at_label (P C.seedIndex).seed
    hF hcomplete hu ha hinj w]
  have hcal : Ioo D.lo D.hi ⊆ interior ((P C.seedIndex).seed.calibrationTimes w) := by
    simpa only [interior_Icc] using interior_mono D.support.calibrated
  intro t ht
  exact hcal ⟨hl.1.trans_le ht.1, ht.2.trans_lt hr.2⟩

end OTSelector.Reconstruction
