import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod

/-!
## Lemma skeleton

* **Conditions:** The coordinate dimension n is any natural number; the open coordinate simplex is defined for any real total mass a. Dilation and its pushforward/integral formulas require a>0. Integral identities use a measurable extended-nonnegative integrand and require no finite-integral assumption.
* **Objects:** Delta_n(a)={q:Fin n -> R | every q_i>0 and sum_i q_i<a}, measured by product Lebesgue volume. The dilation q -> a*q and its pushforward of volume restricted to Delta_n(1). The coordinate insertion (x,q) -> Fin.cons x q and the slice Delta_n(1-x).
* **Proof detail:** Check the defining inequalities to prove measurability, the dilation preimage identity and the first-coordinate slice identity. Restrict the scalar Lebesgue pushforward formula to obtain the inverse Jacobian a^(-n); integrate against it to recover the forward a^n factor. Use the measure-preserving insertion of the first coordinate and apply Tonelli to the simplex indicator times the integrand. Keep dimension zero within the finite-product definitions, where positive total mass gives the single empty tuple.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 5C, Theorem 5.41, printed p. 140, PDF page 155.
  https://measure.axler.net/MIRA.pdf#page=155
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 5C, Definition 5.40 and following discussion, printed p. 139, PDF page 154.
  https://measure.axler.net/MIRA.pdf#page=154
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144.
  https://measure.axler.net/MIRA.pdf#page=144

**Relationship to the sources:** These are explicit restricted-measure and integral corollaries of Lebesgue dilation and product-coordinate integration. The inequalities describing the simplex and the zero-dimensional extension are local. This module does not assert a closed-form simplex volume.
-/

/-!
# Lebesgue measure in simplex coordinates

The open simplex in the independent coordinates consists of positive entries
whose sum is less than the available mass. Scalar dilation and first-coordinate
slicing give its exact change-of-variables formulas, including dimension zero.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Probability

/-- Independent positive simplex coordinates with total mass less than `a`. -/
def openSimplexCoordinates (n : ℕ) (a : ℝ) : Set (Fin n → ℝ) :=
  {q | (∀ i, 0 < q i) ∧ ∑ i, q i < a}

theorem measurableSet_openSimplexCoordinates (n : ℕ) (a : ℝ) :
    MeasurableSet (openSimplexCoordinates n a) := by
  unfold openSimplexCoordinates
  measurability

theorem mem_openSimplexCoordinates_cons {n : ℕ} {x : ℝ} {q : Fin n → ℝ} :
    Fin.cons x q ∈ openSimplexCoordinates (n + 1) 1 ↔
      x ∈ Ioo (0 : ℝ) 1 ∧ q ∈ openSimplexCoordinates n (1 - x) := by
  simp only [openSimplexCoordinates, mem_ofPred_eq, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨hx, hq⟩, hs⟩
    have hsum : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ ↦ (hq i).le
    exact ⟨⟨hx, by linarith⟩, hq, by linarith⟩
  · rintro ⟨⟨hx, _⟩, hq, hs⟩
    exact ⟨⟨hx, hq⟩, by linarith⟩

theorem preimage_smul_openSimplexCoordinates (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (fun q : Fin n → ℝ ↦ a • q) ⁻¹' openSimplexCoordinates n a =
      openSimplexCoordinates n 1 := by
  ext q
  simp only [mem_preimage, openSimplexCoordinates, mem_ofPred_eq,
    Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  constructor
  · rintro ⟨hq, hs⟩
    exact ⟨fun i ↦ (mul_pos_iff_of_pos_left ha).mp (hq i),
      (by nlinarith)⟩
  · rintro ⟨hq, hs⟩
    exact ⟨fun i ↦ mul_pos ha (hq i), by nlinarith⟩

/-- Dilation of the restricted coordinate volume has the expected inverse
Jacobian, with no boundary contribution because both domains are open. -/
theorem map_smul_openSimplexCoordinates (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (volume.restrict (openSimplexCoordinates n 1)).map (fun q ↦ a • q) =
      (ENNReal.ofReal (a ^ n))⁻¹ • volume.restrict (openSimplexCoordinates n a) := by
  rw [← preimage_smul_openSimplexCoordinates n ha,
    ← Measure.restrict_map (measurable_const_smul a)
      (measurableSet_openSimplexCoordinates n a),
    Measure.map_addHaar_smul volume ha.ne', Measure.restrict_smul]
  congr 1
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, abs_inv,
    abs_of_pos (pow_pos ha n)]
  exact ENNReal.ofReal_inv_of_pos (pow_pos ha n)

/-- The scalar volume factor cancels the dilation of a simplex integral. -/
theorem mul_lintegral_smul_openSimplexCoordinates (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal (a ^ n) *
      (∫⁻ q in openSimplexCoordinates n 1, f (a • q)) =
        ∫⁻ q in openSimplexCoordinates n a, f q := by
  rw [← lintegral_map hf (measurable_const_smul a),
    map_smul_openSimplexCoordinates n ha, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]

/-- First-coordinate insertion preserves product Lebesgue measure. -/
theorem volume_preserving_finCons (n : ℕ) :
    MeasurePreserving (fun z : ℝ × (Fin n → ℝ) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ)) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0)
  simpa [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using h

/-- Fubini's formula slices the open simplex at its first coordinate. -/
theorem lintegral_openSimplexCoordinates_succ (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q in openSimplexCoordinates (n + 1) 1, f q) =
      ∫⁻ x in Ioo (0 : ℝ) 1,
        ∫⁻ q in openSimplexCoordinates n (1 - x), f (Fin.cons x q) := by
  classical
  let D := openSimplexCoordinates (n + 1) 1
  have hD : MeasurableSet D := measurableSet_openSimplexCoordinates _ _
  have hcons := volume_preserving_finCons n
  rw [← lintegral_indicator hD,
    ← hcons.lintegral_comp (hf.indicator hD)]
  change (∫⁻ z : ℝ × (Fin n → ℝ), D.indicator f (Fin.cons z.1 z.2)
    ∂volume.prod volume) = _
  rw [lintegral_prod (fun z : ℝ × (Fin n → ℝ) ↦ D.indicator f (Fin.cons z.1 z.2))
    ((hf.indicator hD).comp hcons.measurable).aemeasurable,
    ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hx, ← lintegral_indicator (measurableSet_openSimplexCoordinates n _)]
    apply lintegral_congr
    intro q
    by_cases hq : q ∈ openSimplexCoordinates n (1 - x)
    · have hmem : Fin.cons x q ∈ D := mem_openSimplexCoordinates_cons.mpr ⟨hx, hq⟩
      simp only [indicator_of_mem hq, indicator_of_mem hmem]
    · have hn : Fin.cons x q ∉ D := fun h ↦ hq (mem_openSimplexCoordinates_cons.mp h).2
      simp only [indicator_of_notMem hq, indicator_of_notMem hn]
  · rw [indicator_of_notMem hx]
    apply (lintegral_eq_zero_iff (by fun_prop)).mpr
    exact Filter.Eventually.of_forall fun q ↦
      indicator_of_notMem (fun h ↦ hx (mem_openSimplexCoordinates_cons.mp h).1) _

end OTSelector.Probability
