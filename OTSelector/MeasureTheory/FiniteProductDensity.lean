import OTSelector.MeasureTheory.MeasurePreservingDensity
import OTSelector.MeasureTheory.SimplexCoordinateVolume

/-!
Conditions: Finitely many measurable nonnegative real-coordinate densities whose individual weighted Lebesgue measures are sigma-finite.

Objects: Equality of the actual finite product of weighted coordinate measures with Lebesgue measure weighted by the product density.

Proof detail: Induct over coordinates, combine product withDensity identities and transfer along the proved coordinate-splitting equivalence.

References: Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38; D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: A finite-product density identity with its stated sigma-finiteness assumptions, rather than an unproved density convention for the Dirichlet construction.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.FiniteProductDensity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.FiniteProductDensity`; the selected original proof blocks follow. -/
section

/-!
# Products of real coordinate densities

A finite product of one-dimensional densities is the density of the actual
product measure. The proof reuses the existing coordinate splitting of Lebesgue
measure and the common measure-preserving density transport lemma.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

theorem finPi_withDensity (n : ℕ) (ρ : Fin n → ℝ → ℝ≥0∞)
    (hρ : ∀ i, Measurable (ρ i)) [∀ i, SigmaFinite (volume.withDensity (ρ i))] :
    Measure.pi (fun i ↦ volume.withDensity (ρ i)) =
      volume.withDensity (fun x : Fin n → ℝ ↦ ∏ i, ρ i (x i)) := by
  induction n with
  | zero =>
    simp only [Fin.prod_univ_zero]
    change (Measure.pi (fun i ↦ volume.withDensity (ρ i))) = volume.withDensity 1
    rw [withDensity_one, Measure.pi_of_empty,
      Measure.volume_pi_eq_dirac]
  | succ n ih =>
    let μ (i : Fin (n + 1)) : Measure ℝ := volume.withDensity (ρ i)
    have hsplit := (measurePreserving_piFinSuccAbove μ 0).symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)
    have hcons : MeasurePreserving
        (fun z : ℝ × (Fin n → ℝ) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ))
        ((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) (Measure.pi μ) := by
      simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using hsplit
    rw [← hcons.map_eq]
    change (((volume.withDensity (ρ 0)).prod
      (Measure.pi (fun i : Fin n ↦ volume.withDensity (ρ i.succ)))).map
        (fun z : ℝ × (Fin n → ℝ) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ))) = _
    rw [ih (fun i ↦ ρ i.succ) (fun i ↦ hρ i.succ),
      prod_withDensity (hρ 0) (by fun_prop)]
    have heq : (fun z : ℝ × (Fin n → ℝ) ↦
        ρ 0 z.1 * ∏ i, ρ i.succ (z.2 i)) =
        (fun x : Fin (n + 1) → ℝ ↦ ∏ i, ρ i (x i)) ∘ (fun z : ℝ × (Fin n → ℝ) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ)) := by
      funext z
      simp [Fin.prod_univ_succ]
    rw [heq]
    exact map_withDensity_comp_of_measurePreserving (volume_preserving_finCons n) (by fun_prop)

end OTSelector.Probability

end
