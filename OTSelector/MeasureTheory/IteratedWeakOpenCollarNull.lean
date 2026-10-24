import OTSelector.MeasureTheory.IteratedWeakLscDefect
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
import OTSelector.MeasureTheory.ProjectedRetainedAccuracy
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedClockWeakNull.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedClockWeakNull`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakOpenCollarNull

Conditions: The specified inner and outer weak subsequences, a continuous vague-plan coordinate, measurable target set, open collars covering it and uniform expected collar bounds tending to zero.
Objects: The actual same-law iterated limit and its almost-sure zero boundary mass.
Proof detail: Transfer lower-semicontinuous open-collar tail bounds through each limit in order, apply the projected zero-defect argument, and only then send the collar bound to zero.

## Mathematical sources

- D. H. Fremlin, *Measure Theory, Volume 4*: Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
- Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*: Section 3A, Exercise 17(b), p. 86 (Fatou’s lemma). https://measure.axler.net/MIRA.pdf#page=101

Source relation: A two-stage Portmanteau/Fatou and nonnegative-zero-expectation corollary. The order of the actual limits and collar removal is retained; no diagonal limit swap is asserted.
-/

/-! Open original clock collars remove boundary mass after both actual weak stages. -/
open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {S X : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]

/-- Uniform original open-collar bounds remove the fixed boundary from the
SAME sample-then-tilt limit. The collar width is taken to zero only afterward. -/
theorem ae_physicalScenePlan_null_of_iterated_open_collar_bounds
    (P : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ P ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure X) (hplan : Continuous plan)
    {A : Set X} (hA : MeasurableSet A)
    (collar : ℕ → Set X) (hcollar : ∀ m, IsOpen (collar m))
    (hsub : ∀ m, A ⊆ collar m)
    (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ m ℓ n, (∫⁻ s, (plan s : Measure X) (collar m)
      ∂(P ℓ n : Measure S)) ≤ error m) :
    ∀ᵐ s ∂(R : Measure S), (plan s : Measure X) A = 0 := by
  have hW : Measurable (fun s ↦ (plan s : Measure X) A) :=
    (Measure.measurable_coe hA).comp (measurable_localFiniteMeasure_coe.comp hplan.measurable)
  apply ae_eq_zero_of_projected_retained_zero_and_lost_accuracy R (fun _ ↦ R) id measurable_id
    (fun _ ↦ ProbabilityMeasure.toMeasure_injective (Measure.map_id)) _ hW
    (fun _ _ ↦ 0) (fun m s ↦ (plan s : Measure X) (collar m))
    (fun m ↦ ae_of_all _ fun s ↦ by simpa only [id_eq, zero_add] using
      (measure_mono (μ := (plan s : Measure X)) (hsub m)))
    (fun _ ↦ ae_of_all _ fun _ ↦ rfl) error herror
  intro m level hl0 hlt
  apply measure_lsc_gt_le_of_iterated_weak_sample_tilt_defect_bounds
    P Q R φ hφ ψ hψ hinner houter
    (fun s ↦ (plan s : Measure X) (collar m))
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open (hcollar m)).comp hplan)
    (error m) (fun _ ↦ 0) (fun _ ↦ 0) tendsto_const_nhds tendsto_const_nhds
    (Eventually.of_forall fun ℓ ↦ Eventually.of_forall fun n ↦ by
      simpa only [zero_add, add_zero] using hbound m ℓ n) level hl0 hlt
end OTSelector.Reconstruction

end
end
