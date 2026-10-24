import OTSelector.MeasureTheory.SimplexCoordinateVolume

/-!
Conditions: Finite real coordinate spaces with ordinary Lebesgue measure; nonnegative test integration requires measurability of the test.

Objects: The actual unit-determinant total-mass shear and a positive-orthant integral split into positive total mass and its open simplex coordinates.

Proof detail: Split off the last coordinate, subtract the sum of the remaining ones, and use the volume-preserving shear. Its positivity condition is exactly the open simplex inequality, so Tonelli gives the sliced integral.

References: Günter Last and Mathew Penrose: Section 15.5, Exercise 15.1, p. 163; D. H. Fremlin: Section 235G, integration along an inverse-measure-preserving map.
Relation: The explicit coordinate Jacobian calculation behind gamma/Dirichlet normalization. The module proves its own unit volume factor and uses coordinate simplex measure, without silently replacing it by a differently normalized Hausdorff measure.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.SimplexMassCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.SimplexMassCoordinates`; the selected original proof blocks follow. -/
section

/-!
# Total mass coordinates on the positive orthant

The last mass is the total minus all other coordinates. This linear shear has
unit volume factor, so slicing the positive orthant by total mass uses precisely
the simplex coordinate volume.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- Recover a vector from its total mass and all but its last coordinate. -/
def massCoordinateVector (n : ℕ) (z : ℝ × (Fin n → ℝ)) : Fin (n + 1) → ℝ :=
  Fin.snoc z.2 (z.1 - ∑ i, z.2 i)

theorem volume_preserving_finSnoc (n : ℕ) :
    MeasurePreserving (fun z : ℝ × (Fin n → ℝ) ↦
      (Fin.snoc z.2 z.1 : Fin (n + 1) → ℝ)) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ)
    (Fin.last n)).symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n))
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using h

theorem volume_preserving_massCoordinateVector (n : ℕ) :
    MeasurePreserving (massCoordinateVector n) := by
  have hshift : MeasurePreserving (fun z : (Fin n → ℝ) × ℝ ↦
      (z.1, z.2 - ∑ i, z.1 i)) := by
    change MeasurePreserving _ (volume.prod volume) (volume.prod volume)
    apply (MeasurePreserving.id (volume : Measure (Fin n → ℝ))).skew_product
      (g := fun q : Fin n → ℝ ↦ fun s : ℝ ↦ s - ∑ i, q i)
      (μc := volume) (μd := volume)
    · fun_prop
    · exact Filter.Eventually.of_forall fun q ↦
        (measurePreserving_add_right (volume : Measure ℝ) (-∑ i, q i)).map_eq
  have h := (volume_preserving_finSnoc n).comp
    ((Measure.measurePreserving_swap).comp
      (hshift.comp (Measure.measurePreserving_swap)))
  exact h

theorem sum_massCoordinateVector (n : ℕ) (z : ℝ × (Fin n → ℝ)) :
    (∑ i, massCoordinateVector n z i) = z.1 := by
  simp only [massCoordinateVector, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem massCoordinateVector_pos_iff (n : ℕ) (z : ℝ × (Fin n → ℝ)) :
    (∀ i, 0 < massCoordinateVector n z i) ↔
      0 < z.1 ∧ z.2 ∈ openSimplexCoordinates n z.1 := by
  constructor
  · intro h
    have hq : ∀ i, 0 < z.2 i := fun i ↦ by simpa [massCoordinateVector] using h i.castSucc
    have hl : 0 < z.1 - ∑ i, z.2 i := by
      simpa [massCoordinateVector] using h (Fin.last n)
    have hs : 0 ≤ ∑ i, z.2 i := Finset.sum_nonneg fun i _ ↦ (hq i).le
    exact ⟨by linarith, hq, by linarith⟩
  · rintro ⟨_, hq, hs⟩ i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [massCoordinateVector, Fin.snoc_last] using sub_pos.mpr hs
    · simpa only [massCoordinateVector, Fin.snoc_castSucc] using hq j

/-- The positive orthant in a finite real coordinate space. -/
def positiveCoordinateOrthant (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, 0 < x i}

theorem measurableSet_positiveCoordinateOrthant (n : ℕ) :
    MeasurableSet (positiveCoordinateOrthant n) := by
  unfold positiveCoordinateOrthant
  measurability

/-- The positive orthant is sliced by its true total mass using simplex volume. -/
theorem lintegral_positiveOrthant_massCoordinates (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in positiveCoordinateOrthant (n + 1), f x) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ q in openSimplexCoordinates n s,
        f (massCoordinateVector n (s, q)) := by
  classical
  let D := positiveCoordinateOrthant (n + 1)
  have hD : MeasurableSet D := measurableSet_positiveCoordinateOrthant _
  have hT := volume_preserving_massCoordinateVector n
  rw [← lintegral_indicator hD, ← hT.lintegral_comp (hf.indicator hD)]
  change (∫⁻ z : ℝ × (Fin n → ℝ), D.indicator f (massCoordinateVector n z)
    ∂volume.prod volume) = _
  rw [lintegral_prod (fun z : ℝ × (Fin n → ℝ) ↦
      D.indicator f (massCoordinateVector n z))
    ((hf.indicator hD).comp hT.measurable).aemeasurable,
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs), ← lintegral_indicator (measurableSet_openSimplexCoordinates n s)]
    apply lintegral_congr
    intro q
    by_cases hq : q ∈ openSimplexCoordinates n s
    · have hmem : massCoordinateVector n (s, q) ∈ D :=
        (massCoordinateVector_pos_iff n (s, q)).mpr ⟨hs, hq⟩
      simp only [indicator_of_mem hq, indicator_of_mem hmem]
    · have hn : massCoordinateVector n (s, q) ∉ D :=
        fun h ↦ hq ((massCoordinateVector_pos_iff n (s, q)).mp h).2
      simp only [indicator_of_notMem hq, indicator_of_notMem hn]
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]
    apply (lintegral_eq_zero_iff
      ((hf.indicator hD).comp (hT.measurable.comp measurable_prodMk_left))).mpr
    apply Filter.Eventually.of_forall
    intro q
    have hn : massCoordinateVector n (s, q) ∉ D :=
      fun h ↦ hs ((massCoordinateVector_pos_iff n (s, q)).mp h).1
    exact indicator_of_notMem hn _

end OTSelector.Probability

end
