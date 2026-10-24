import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.MeasureTheory.LabelClockWindowDensities
import OTSelector.Probability.ConditionalLawCompactCore
import OTSelector.Probability.LabelClockConditionalDensity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerConditionalCompactCore.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerConditionalCompactCore`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.ConditionalCompactCore

* **Conditions:** Given jointly measurable normalized label–clock densities for two finite populations with a common label law on complete Finsler countable-product labels.
* **Objects:** A common large compact label set where both L1 density representatives vary continuously, with total variation equal to their L1 distance and all supplied AE properties retained.
* **Proof detail:** Identify conditional densities by uniqueness, form measurable L1 representatives, apply Lusin on the Polish label space, and use the density formula for full signed total variation.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110): Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
- [Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213): Section 4.1, conditional-expectation definition and Uniqueness argument, pp. 205–206; Section 4.1.3, Theorems 4.1.16–4.1.18, pp. 214–215.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).

Source relation (derived): A joint compact-continuity refinement of supplied conditional laws. Geometry is used for the label topology, not to infer the density hypotheses.
-/

/-!
# Compact continuity for the original Finsler conditional clock laws

The given original joint densities determine normalized conditional clock measures.
Completeness supplies the Polish topology of the existing countable-product labels,
so both laws admit one large compact continuity set retaining an arbitrary ae property.
The original potential, labels and densities are supplied and never reselected.
-/

open Set MeasureTheory ProbabilityTheory Filter Manifold
open scoped ENNReal Topology ContDiff

noncomputable section

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- The supplied original joint densities give one large compact set of the original
Finsler labels on which both scalar conditional laws are continuous in total variation.
Completeness supplies the Polish label topology, and joint density identities supply
normalization and the original conditional measures without any new choices of labels. -/
theorem exists_finsler_conditional_compact_core
    (F : Geometry.ContinuousFinslerNorm E M)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → (ℚ → M)} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hbalance : μ.map a = ν.map a)
    (H : Fin 2 → (ℚ → M) × ℝ → ℝ≥0∞) (hH : ∀ i, Measurable (H i))
    (hden : ∀ i : Fin 2,
      ((μ.map a).prod (volume : Measure ℝ)).withDensity (H i) =
        (if i = 0 then μ else ν).map (fun x ↦ (a x, u x)))
    {P : (ℚ → M) → Prop} (hP : ∀ᵐ z ∂μ.map a, P z)
    {s : Set (ℚ → M)} (hs : MeasurableSet s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    let κ : Fin 2 → Kernel (ℚ → M) ℝ := fun i ↦
      if i = 0 then condDistrib u a μ else condDistrib u a ν
    let _instFinslerCompactFinite : ∀ i, IsFiniteKernel (κ i) := fun i ↦ by
      dsimp only [κ]
      split <;> infer_instance
    ∃ (S : Fin 2 → (ℚ → M) → Lp ℝ 1 (volume : Measure ℝ)) (K : Set (ℚ → M)),
      (∀ i, @Measurable _ _ _ (borel _) (S i)) ∧ K ⊆ s ∧ IsCompact K ∧
      (μ.map a) (s \ K) < ε ∧ ContinuousOn (fun z i ↦ S i z) K ∧
      (∀ z ∈ K, P z ∧ ∀ i,
        (∫⁻ t, H i (z, t)) = 1 ∧
        (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = κ i z ∧
        (⇑(S i z)) =ᵐ[volume] (fun t ↦ (H i (z, t)).toReal)) ∧
      (∀ i, ∀ z ∈ K, ∀ z' ∈ K,
        ((κ i z).toSignedMeasure - (κ i z').toSignedMeasure).totalVariation univ =
          ENNReal.ofReal ‖S i z - S i z'‖) ∧
      ∀ i, ContinuousOn (fun p : (ℚ → M) × (ℚ → M) ↦
        ((κ i p.1).toSignedMeasure - (κ i p.2).toSignedMeasure).totalVariation univ)
        (K ×ˢ K)
 := by
  classical
  let _instFinslerCompactMetric : MetricSpace M := F.metricSpace
  let _instFinslerCompactComplete : CompleteSpace M := hcomplete
  let _instFinslerCompactProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFinslerCompactPolish : PolishSpace M := inferInstance
  let _instFinslerCompactLabelsPolish : PolishSpace (ℚ → M) := inferInstance
  let _instFinslerCompactLabelsBorel : BorelSpace (ℚ → M) := inferInstance
  let η : Fin 2 → Measure M := fun i ↦ if i = 0 then μ else ν
  let κ : Fin 2 → Kernel (ℚ → M) ℝ := fun i ↦
    if i = 0 then condDistrib u a μ else condDistrib u a ν
  let _instFinslerCompactEtaFinite : ∀ i, IsFiniteMeasure (η i) := fun i ↦ by
    dsimp only [η]
    split <;> infer_instance
  let _instFinslerCompactKernelFinite : ∀ i, IsFiniteKernel (κ i) := fun i ↦ by
    dsimp only [κ]
    split <;> infer_instance
  have hmap (i : Fin 2) : (η i).map a = μ.map a := by
    dsimp only [η]
    split
    · rfl
    · exact hbalance.symm
  have hden' (i : Fin 2) :
      (((η i).map a).prod (volume : Measure ℝ)).withDensity (H i) =
        (η i).map (fun x ↦ (a x, u x)) := by
    rw [hmap i]
    exact hden i
  have hnorm (i : Fin 2) : ∀ᵐ z ∂μ.map a, ∫⁻ t, H i (z, t) = 1 := by
    apply ae_lintegral_eq_one_of_prod_withDensity_fst (μ.map a) volume (hH i)
    rw [hden i]
    change ((η i).map (fun x ↦ (a x, u x))).map Prod.fst = μ.map a
    rw [Measure.map_map measurable_fst (ha.prodMk hu)]
    exact hmap i
  have hκ (i : Fin 2) : ∀ᵐ z ∂μ.map a,
      (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = κ i z := by
    have h := ae_withDensity_clock_eq_condDistrib (η i) hu (hH i) (hden' i)
    rw [hmap i] at h
    have heq : condDistrib u a (η i) = κ i := by
      dsimp only [η, κ]
      split <;> rfl
    exact heq ▸ h
  exact exists_conditionalLaw_compact_core (μ.map a) H κ hH hnorm hκ hP hs
    (measure_ne_top _ _) hε

end OTSelector.Reconstruction

end
end
