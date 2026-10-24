import OTSelector.Probability.FiniteClassThinning
import OTSelector.Transport.Coupling.FiniteClockMixture
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawActualBinMarginal.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawActualBinMarginal`; the selected original proof blocks follow. -/
section

/-!
# Probability.NormalizedBinMarginal

## Lemma skeleton

* **Conditions:** A measurable SFinite kernel whose sections are finite and finitely many measurable disjoint bins cover each section almost everywhere in the label.
* **Objects:** The mixture of normalized actual within-bin kernels with their original real bin masses equals the original kernel almost everywhere.
* **Proof detail:** On positive-mass bins cancel normalization against the original mass; zero bins contribute zero regardless of the supplied fallback, and finite additivity recovers the section.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Finite-bin reconstruction of the unchanged conditional law, with explicit harmless fallbacks on null bins.
-/

/-!
Normalized original within-bin kernels recover the actual original clock law when finite bins cover its original support almost everywhere.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Finite actual clock bins need cover only the original conditional laws.
Their ambient union may be the original compact scalar range. -/
theorem finiteClassMarginalKernel_normalized_bins_eq_original_ae
    {I Z X : Type*} [Fintype I] [MeasurableSpace Z] [MeasurableSpace X]
    (r : Measure Z) (κ : Kernel Z X) [IsSFiniteKernel κ] [∀ z, IsFiniteMeasure (κ z)]
    (B : I → Set X) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B))
    (hcover : ∀ᵐ z ∂r, ∀ᵐ x ∂κ z, x ∈ ⋃ i, B i)
    (fallback : I → X) :
    finiteClassMarginalKernel (fun z i ↦ (κ z).real (B i))
      (fun i ↦ normalizedActualBinKernel κ (B i) (hB i) (fallback i)) =ᵐ[r] κ := by
  classical
  have hm (i : I) : Measurable (fun z ↦ (κ z).real (B i)) :=
    (κ.measurable_coe (hB i)).ennreal_toReal
  filter_upwards [hcover] with z hz
  rw [finiteClassMarginalKernel_apply _ hm]
  simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    binMass_smul_normalizedActualBinKernel]
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hB]
  exact Measure.restrict_eq_self_of_ae_mem hz

end OTSelector.Reconstruction

end
end
