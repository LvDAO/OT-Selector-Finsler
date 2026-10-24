import OTSelector.Finite.OrderedHallFlow
import OTSelector.Finite.ReferenceHallFamilyTolerances
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawMeasurableReferenceFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawMeasurableReferenceFlow`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawMeasurableReferenceFlow

**Conditions:** A measurable reference selector and measurable reference/actual entries and intensity; core extensions use continuous positive intensity on a measurable core.

**Objects:** Measurable retained/residual reference flows and a globally positive intensity extension.

**Proof detail:** Compose measurable matrix entries with the selector and apply finite arithmetic; extend intensity by one outside the core, using measurable piecewise construction and the given positivity inside it.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Original reference-bin feasibility and measurable legal population reconstruction.
-/

open MeasureTheory ProbabilityTheory Function
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Actual measurable original reference profiles may be read through any
measurable center map, including the existing finite root-cell reference map. -/
theorem measurable_referenceFamilyRetainedClockFlow
    {C Z : Type*} [MeasurableSpace C] [MeasurableSpace Z] {M L : ℕ}
    (reference : Z → C) (href : Measurable reference)
    (P₀ : C → Fin M → Fin L → ℝ)
    (hP₀ : ∀ i j, Measurable (fun c ↦ P₀ c i j))
    (η : ℝ) (d : Z → ℝ) (hd : Measurable d) (i : Fin M) (j : Fin L) :
    Measurable (fun z ↦ finiteReferenceRetainedClockFlow reference P₀ η d z i j) :=
  measurable_div.comp ((measurable_mul.comp
    (measurable_const.prodMk ((hP₀ i j).comp href))).prodMk hd)

/-- The explicit residual has measurable edge weights on the original label
space, even when its actual reference profiles are defined on a full root space. -/
theorem measurable_referenceFamilyResidualClockFlow
    {C Z : Type*} [MeasurableSpace C] [MeasurableSpace Z] {M L : ℕ}
    (reference : Z → C) (href : Measurable reference)
    (a₀ : C → Fin M → ℝ) (b₀ : C → Fin L → ℝ)
    (ha₀ : ∀ i, Measurable (fun c ↦ a₀ c i)) (hb₀ : ∀ j, Measurable (fun c ↦ b₀ c j))
    (η : ℝ) (d : Z → ℝ) (hd : Measurable d)
    (a : Z → Fin M → ℝ) (b : Z → Fin L → ℝ)
    (ha : ∀ i, Measurable (fun z ↦ a z i)) (hb : ∀ j, Measurable (fun z ↦ b z j))
    (i : Fin M) (j : Fin L) :
    Measurable (fun z ↦ finiteReferenceResidualClockFlow reference a₀ b₀ η d a b z i j) := by
  have hsa (i : Fin M) : Measurable (fun z ↦ d z * a z i - (1 - η) * a₀ (reference z) i) :=
    measurable_sub.comp ((measurable_mul.comp (hd.prodMk (ha i))).prodMk
      (measurable_mul.comp (measurable_const.prodMk ((ha₀ i).comp href))))
  have htb (j : Fin L) : Measurable (fun z ↦ d z * b z j - (1 - η) * b₀ (reference z) j) :=
    measurable_sub.comp ((measurable_mul.comp (hd.prodMk (hb j))).prodMk
      (measurable_mul.comp (measurable_const.prodMk ((hb₀ j).comp href))))
  exact measurable_div.comp
    ((measurable_orderedClockFlow _ _ hsa htb i j).prodMk hd)

/-- A continuous original intensity on a retained measurable core has a
measurable positive extension, leaving all original values on the core intact. -/
def coreIntensityExtension {Z : Type*} (K : Set Z) (d : Z → ℝ) (z : Z) : ℝ := by
  classical
  exact if z ∈ K then d z else 1

theorem measurable_coreIntensityExtension
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (K : Set Z) (hK : MeasurableSet K) (d : Z → ℝ) (hd : ContinuousOn d K) :
    Measurable (coreIntensityExtension K d) := by
  classical
  exact hd.measurable_piecewise continuousOn_const hK

theorem coreIntensityExtension_eq
    {Z : Type*} (K : Set Z) (d : Z → ℝ) {z : Z} (hz : z ∈ K) :
    coreIntensityExtension K d z = d z := by
  classical
  exact ite_eq_left hz

theorem coreIntensityExtension_pos
    {Z : Type*} (K : Set Z) (d : Z → ℝ) (hd : ∀ z ∈ K, 0 < d z) (z : Z) :
    0 < coreIntensityExtension K d z := by
  classical
  by_cases hz : z ∈ K
  · simpa only [coreIntensityExtension, ite_eq_left hz] using hd z hz
  · simp only [coreIntensityExtension, ite_eq_right hz, zero_lt_one]

end OTSelector.Reconstruction

end
end
