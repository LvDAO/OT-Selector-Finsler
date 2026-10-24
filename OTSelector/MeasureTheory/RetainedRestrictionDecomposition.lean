import Mathlib.MeasureTheory.Measure.Restrict

/-!
## Lemma skeleton

* **Conditions:** A measurable retained set A contained in W almost everywhere; W is otherwise arbitrary.
* **Objects:** Exact positive restriction decomposition mu|W=mu|A+mu|(W minus A).
* **Proof detail:** Replace A by its intersection with W modulo null sets and use additivity of restriction across the measurable split A/A-complement.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93

**Relationship to the sources:** Restriction/indicator additivity with an almost-everywhere inclusion. Measurability of W is not silently added.
-/

/-! # Exact original-window mass after retaining a Borel subplan -/
open Set Filter MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction

/-- Almost-sure containment is enough to split an original window measure
into its retained atoms and its literal unused atoms. -/
theorem measure_restrict_eq_retained_add_unused_of_ae_subset
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {A W : Set X}
    (hA : MeasurableSet A) (hsub : ∀ᵐ x ∂μ, x ∈ A → x ∈ W) :
    μ.restrict W = μ.restrict A + μ.restrict (W \ A) := by
  have hi : (A ∩ W : Set X) =ᵐ[μ] A := by
    filter_upwards [hsub] with x hx
    exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hx h⟩⟩
  calc
    _ = (μ.restrict W).restrict A + (μ.restrict W).restrict Aᶜ :=
      (Measure.restrict_add_restrict_compl hA).symm
    _ = μ.restrict A + μ.restrict (W \ A) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict hA.compl,
        Measure.restrict_congr_set hi]
      congr 2
      ext x
      simp [and_comm]

end OTSelector.Reconstruction
