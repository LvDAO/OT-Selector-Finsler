import OTSelector.MeasureTheory.IntegralCutoffUpperLimit
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalPressureCutoffIntegralUpperAE.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalPressureCutoffIntegralUpperAE`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.AEIntegralCutoffUpperLimit

## Lemma skeleton

* **Conditions:** Finite original measure, almost-everywhere strongly measurable pressure versions, integrable reference and the stated common lower bound/eventual upper control.
* **Objects:** Large measurable retained cutoffs with integrable original pressure and the same integral upper-limit bound.
* **Proof detail:** Replace each pressure by a measurable representative, apply the measurable cutoff theorem and remove one countable union of representative exceptions before transferring retained-set integrals.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106): Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=107): Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=105): Section 3B, Theorem 3.28, pp. 90–91.

Source relation (composition): AE-representative extension of the retained upper-limit theorem; whole-space approximation integrability remains unnecessary.
-/

/-! Original pressure cutoffs work directly with the actual AE measurable
pressure versions obtained from the unchanged original thermodynamic limits. -/
open Set Function MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Deterministic cutoffs and their actual integral upper depend only on
AE measurable original pressures. Borel versions are constructed internally;
the output uses the original pressures and original population integrals. -/
theorem exists_original_pressure_cutoff_integral_upper_ae
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℕ → X → ℝ) (pref : X → ℝ)
    (hp : ∀ n, AEStronglyMeasurable (p n) μ) (hpref : Integrable pref μ)
    {B : ℝ} (hB : 0 ≤ B) (hlower : ∀ n, ∀ᵐ x ∂μ, -B ≤ p n x)
    (hupper : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, p n x < pref x + ε) :
    ∀ budget tolerance, 0 < budget → 0 < tolerance →
      ∀ᶠ n in atTop, ∃ K : Set X, MeasurableSet K ∧ μ.real Kᶜ < budget ∧
        IntegrableOn (p n) K μ ∧
        (∫ x in K, p n x ∂μ) < (∫ x, pref x ∂μ) + tolerance := by
  let p' := fun n ↦ (hp n).mk (p n)
  let pref' := hpref.aestronglyMeasurable.mk pref
  have hpeq n : p n =ᵐ[μ] p' n := (hp n).ae_eq_mk
  have hrefeq : pref =ᵐ[μ] pref' := hpref.aestronglyMeasurable.ae_eq_mk
  have hIref : Integrable pref' μ := hpref.congr hrefeq
  have hlow' n : ∀ᵐ x ∂μ, -B ≤ p' n x := by
    filter_upwards [hlower n,hpeq n] with x hx heq
    rwa [← heq]
  have hup' : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, p' n x < pref' x + ε := by
    filter_upwards [hupper,ae_all_iff.mpr hpeq,hrefeq] with x hx heq heqref
    intro ε hε
    filter_upwards [hx ε hε] with n hn
    rwa [← heq n,← heqref]
  intro budget tolerance hbudget htolerance
  filter_upwards [exists_original_pressure_cutoff_integral_upper μ p' pref'
    (fun n ↦ (hp n).stronglyMeasurable_mk.measurable) hIref
    hpref.aestronglyMeasurable.stronglyMeasurable_mk.measurable hB hlow' hup'
    budget tolerance hbudget htolerance] with n hn
  obtain ⟨K,hK,hmass,hIK,hint⟩ := hn
  have heqK : p n =ᵐ[μ.restrict K] p' n := ae_restrict_of_ae (hpeq n)
  refine ⟨K,hK,hmass,hIK.congr heqK.symm,?_⟩
  rw [integral_congr_ae heqK,integral_congr_ae hrefeq]
  exact hint

end OTSelector.Reconstruction

end
end
