import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Topology.MetricSpace.CanonicalMcShaneExtension

## Lemma skeleton

* **Conditions:** A nonempty index type of scalar data satisfying an L-Lipschitz inequality up to the supplied additive roughness b; countability/measurability hypotheses only for the measurable family statement.

* **Objects:** The infimum-cone extension, its Lipschitz bound, approximate interpolation and invariance under isometries/reindexing.

* **Proof detail:** Bound the infimum below using one fixed node. Compare every cone at two points by the triangle inequality and pass to the infimum in both directions. Evaluate a node’s cone for the upper bound and use the rough data inequality for the lower bound.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=148): Section 1.10, Exercise 1.10.8, p. 139.
- [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18): Section C, Definitions 0.32 and 0.35, pp. 18–19.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106): Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.

Source relation (generalization): The exact Lipschitz-extension principle is classical; the additive-roughness node error and measurable countable-family packaging are locally proved generalizations/adapters.
-/

/-! Canonical scalar momentum extension from countable rough Lipschitz data. -/
open Set Function
open scoped NNReal
noncomputable section
namespace OTSelector.Probability
variable {I X : Type*} [Nonempty I] [PseudoMetricSpace X]

/-- The literal infimum formula, so later measurability and covariance need no
noncanonical choice of an exact Lipschitz extension. -/
def roughMcShane (L : ℝ≥0) (z : I → X) (p : I → ℝ) (x : X) : ℝ :=
  ⨅ i, p i + L * dist x (z i)

theorem roughMcShane_bddBelow (L : ℝ≥0) (z : I → X) (p : I → ℝ) {b : ℝ}
    (hrough : ∀ i j, p i ≤ p j + L * dist (z i) (z j) + b) (x : X) :
    BddBelow (range (fun i ↦ p i + L * dist x (z i))) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  refine ⟨p i₀ - b - L * dist x (z i₀), ?_⟩
  rintro y ⟨i, rfl⟩
  have hr := hrough i₀ i
  have htri := mul_le_mul_of_nonneg_left (dist_triangle_left (z i₀) (z i) x) L.coe_nonneg
  linarith

/-- The canonical field is genuinely Lipschitz, although the original data have
an additive rough error. -/
theorem lipschitzWith_roughMcShane (L : ℝ≥0) (z : I → X) (p : I → ℝ) {b : ℝ}
    (hrough : ∀ i j, p i ≤ p j + L * dist (z i) (z j) + b) :
    LipschitzWith L (roughMcShane L z p) := by
  apply LipschitzWith.of_le_add_mul L
  intro x y
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro i
  rw [sub_le_iff_le_add]
  calc
    roughMcShane L z p x ≤ p i + L * dist x (z i) :=
      ciInf_le (roughMcShane_bddBelow L z p hrough x) i
    _ ≤ p i + L * dist y (z i) + L * dist x y := by
      have h := mul_le_mul_of_nonneg_left (dist_triangle x y (z i)) L.coe_nonneg
      linarith

/-- At each actual node the field stays within the original one-sided rough error. -/
theorem roughMcShane_node_bounds (L : ℝ≥0) (z : I → X) (p : I → ℝ) {b : ℝ}
    (hrough : ∀ i j, p i ≤ p j + L * dist (z i) (z j) + b) (i : I) :
    p i - b ≤ roughMcShane L z p (z i) ∧ roughMcShane L z p (z i) ≤ p i := by
  constructor
  · apply le_ciInf
    intro j
    have h := hrough i j
    linarith
  · simpa only [roughMcShane, dist_self, mul_zero, add_zero] using
      ciInf_le (roughMcShane_bddBelow L z p hrough (z i)) i

omit [Nonempty I] in
/-- The literal formula commutes with every spatial isometry, including translations. -/
theorem roughMcShane_isometry {Y : Type*} [PseudoMetricSpace Y]
    (e : X → Y) (he : Isometry e) (L : ℝ≥0) (z : I → X) (p : I → ℝ) (x : X) :
    roughMcShane L (e ∘ z) p (e x) = roughMcShane L z p x := by
  simp only [roughMcShane, Function.comp_apply, he.dist_eq]

omit [Nonempty I] in
/-- Countable actual node data give a jointly Borel field in environment and position. -/
theorem measurable_roughMcShane [Countable I] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    {Ω : Type*} [MeasurableSpace Ω] (L : ℝ≥0)
    (z : I → Ω → X) (p : I → Ω → ℝ)
    (hz : ∀ i, Measurable (z i)) (hp : ∀ i, Measurable (p i)) :
    Measurable (fun w : Ω × X ↦ roughMcShane L (fun i ↦ z i w.1)
      (fun i ↦ p i w.1) w.2) := by
  apply Measurable.iInf
  intro i
  exact ((hp i).comp measurable_fst).add
    ((measurable_snd.dist ((hz i).comp measurable_fst)).const_mul (L : ℝ))

omit [Nonempty I] in
/-- Re-enumerating or repeating nodes does not change the field: only the set of
actual position-momentum pairs enters its definition. -/
theorem roughMcShane_eq_of_range_eq {J : Type*}
    (L : ℝ≥0) (z : I → X) (p : I → ℝ) (w : J → X) (r : J → ℝ)
    (h : range (fun i ↦ (z i, p i)) = range (fun j ↦ (w j, r j))) :
    roughMcShane L z p = roughMcShane L w r := by
  funext x
  change sInf (range (fun i ↦ p i + L * dist x (z i))) =
    sInf (range (fun j ↦ r j + L * dist x (w j)))
  congr 1
  have he := congrArg (fun A : Set (X × ℝ) ↦
    (fun v : X × ℝ ↦ v.2 + L * dist x v.1) '' A) h
  simpa only [← range_comp, Function.comp_def] using he

end OTSelector.Probability
