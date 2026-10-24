import OTSelector.Finite.OrderedHallFlow
import OTSelector.Finite.ResidualHallStability
import OTSelector.Transport.Coupling.FiniteClockMixture
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawResidualPopulation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawResidualPopulation`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawResidualPopulation

**Conditions:** An ordered legal finite class graph has a feasible reference matrix; actual row/column masses have equal totals, satisfy the explicit Hall cuts and are uniformly close to the reference.

**Objects:** The post-thinning residual ordered-clock flow, exact whole-population marginals and residual mass bound.

**Proof detail:** Apply the finite tolerance theorem for residual Hall feasibility, use the explicit ordered interval-overlap flow, and add the scaled reference coupling; finite summation gives the residual mass estimate.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=39), Section 2.6, Remarks 2.27–2.28, pp. 35–37, equations (2.31)–(2.37); [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Measurable forward weighted Hall construction](main.tex#measurable-forward-hall), main.tex label measurable-forward-hall, line 6889.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Subtracting a fixed class reference preserves equality of the total mass. -/
theorem reference_residual_total {M L : ℕ}
    (a a₀ : Fin M → ℝ) (b b₀ : Fin L → ℝ) (θ : ℝ)
    (htotal : ∑ i, a i = ∑ j, b j) (htotal₀ : ∑ i, a₀ i = ∑ j, b₀ j) :
    (∑ i, (a i - θ * a₀ i)) = ∑ j, (b j - θ * b₀ j) := by
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, htotal, htotal₀]

/-- The residual class flow after exact scalar reference thinning. -/
def referenceResidualClockFlow {M L : ℕ}
    (a₀ : Fin M → ℝ) (b₀ : Fin L → ℝ) (η : ℝ)
    (a : Fin M → ℝ) (b : Fin L → ℝ) : Fin M → Fin L → ℝ :=
  orderedClockFlow (fun i ↦ a i - (1 - η) * a₀ i)
    (fun j ↦ b j - (1 - η) * b₀ j)

/-- The explicit residual flow is measurable in all actual original class masses. -/
theorem measurable_referenceResidualClockFlow
    {Z : Type*} [MeasurableSpace Z] {M L : ℕ}
    (a₀ : Fin M → ℝ) (b₀ : Fin L → ℝ) (η : ℝ)
    (a : Z → Fin M → ℝ) (b : Z → Fin L → ℝ)
    (ha : ∀ i, Measurable (fun z ↦ a z i)) (hb : ∀ j, Measurable (fun z ↦ b z j))
    (i : Fin M) (j : Fin L) :
    Measurable (fun z ↦ referenceResidualClockFlow a₀ b₀ η (a z) (b z) i j) := by
  exact measurable_orderedClockFlow _ _
    (fun i ↦ by simpa only [Pi.sub_apply] using (ha i).sub_const ((1 - η) * a₀ i))
    (fun j ↦ by simpa only [Pi.sub_apply] using (hb j).sub_const ((1 - η) * b₀ j)) i j

/-- A uniform finite-class tolerance yields an explicit measurable legal
residual flow, with exact residual marginals. Reference-tight Hall cuts are allowed. -/
theorem exists_tolerance_reference_residual_clockFlow
    {M L : ℕ} (allowed : Fin M → Fin L → Prop)
    (horder : ∀ i i' j j', i ≤ i' → j' ≤ j → allowed i' j' → allowed i j)
    (a₀ : Fin M → ℝ) (b₀ : Fin L → ℝ)
    (ha₀ : ∀ i, 0 ≤ a₀ i) (hb₀ : ∀ j, 0 ≤ b₀ j)
    (htotal₀ : ∑ i, a₀ i = ∑ j, b₀ j)
    (hhall₀ : ∀ A : Finset (Fin M), (∑ i ∈ A, a₀ i) ≤
      ∑ j ∈ orderedClockNeighbors allowed A, b₀ j)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : Fin M → ℝ) (b : Fin L → ℝ),
      (∀ i, 0 ≤ a i) → (∀ j, 0 ≤ b j) →
      (∑ i, a i = ∑ j, b j) →
      (∀ A : Finset (Fin M), (∑ i ∈ A, a i) ≤
        ∑ j ∈ orderedClockNeighbors allowed A, b j) →
      (∀ i, |a i - a₀ i| ≤ δ) → (∀ j, |b j - b₀ j| ≤ δ) →
      (∀ i j, 0 ≤ referenceResidualClockFlow a₀ b₀ η a b i j) ∧
      (∀ i, ∑ j, referenceResidualClockFlow a₀ b₀ η a b i j = a i - (1 - η) * a₀ i) ∧
      (∀ j, ∑ i, referenceResidualClockFlow a₀ b₀ η a b i j = b j - (1 - η) * b₀ j) ∧
      ∀ i j, ¬ allowed i j → referenceResidualClockFlow a₀ b₀ η a b i j = 0 := by
  obtain ⟨δ, hδ, hstable⟩ := exists_tolerance_reference_residual_hall
    (orderedClockNeighbors allowed) a₀ b₀ ha₀ hb₀
    (fun A ↦ sub_nonneg.mpr (hhall₀ A)) hη
  refine ⟨δ, hδ, ?_⟩
  intro a b ha hb htotal hhall hsa htb
  obtain ⟨hRa, hRb, hRhall⟩ := hstable a b ha hb
    (fun A ↦ sub_nonneg.mpr (hhall A)) hsa htb
  exact orderedClockFlow_of_hall allowed horder _ _ hRa hRb
    (reference_residual_total a a₀ b b₀ (1 - η) htotal htotal₀)
    (fun A ↦ sub_nonneg.mp (hRhall A))

/-- Recombine any fixed legal reference flow with its explicit residual.
All actual original class marginals are recovered exactly. -/
theorem referenceWholeClockFlow_marginals
    {M L : ℕ} (allowed : Fin M → Fin L → Prop)
    (a₀ : Fin M → ℝ) (b₀ : Fin L → ℝ) (a : Fin M → ℝ) (b : Fin L → ℝ)
    (P₀ R : Fin M → Fin L → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hP₀ : ∀ i j, 0 ≤ P₀ i j) (hR : ∀ i j, 0 ≤ R i j)
    (hrow₀ : ∀ i, ∑ j, P₀ i j = a₀ i) (hcol₀ : ∀ j, ∑ i, P₀ i j = b₀ j)
    (hrowR : ∀ i, ∑ j, R i j = a i - θ * a₀ i)
    (hcolR : ∀ j, ∑ i, R i j = b j - θ * b₀ j)
    (hlegal₀ : ∀ i j, ¬ allowed i j → P₀ i j = 0)
    (hlegalR : ∀ i j, ¬ allowed i j → R i j = 0) :
    (∀ i j, 0 ≤ θ * P₀ i j + R i j) ∧
    (∀ i, ∑ j, (θ * P₀ i j + R i j) = a i) ∧
    (∀ j, ∑ i, (θ * P₀ i j + R i j) = b j) ∧
    ∀ i j, ¬ allowed i j → θ * P₀ i j + R i j = 0 := by
  refine ⟨fun i j ↦ add_nonneg (mul_nonneg hθ (hP₀ i j)) (hR i j), ?_, ?_, ?_⟩
  · intro i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrow₀ i, hrowR i]
    ring
  · intro j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcol₀ j, hcolR j]
    ring
  · intro i j hij
    rw [hlegal₀ i j hij, hlegalR i j hij, mul_zero, add_zero]

/-- Retained and residual couplings built with the actual within-bin laws
form a whole coupling of the unchanged original class mixtures. -/
theorem referenceWholePopulationCoupling
    {M L : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (a₀ : Fin M → ℝ) (b₀ : Fin L → ℝ) (a : Fin M → ℝ) (b : Fin L → ℝ)
    (P₀ R : Fin M → Fin L → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hP₀ : ∀ i j, 0 ≤ P₀ i j) (hR : ∀ i j, 0 ≤ R i j)
    (hrow₀ : ∀ i, ∑ j, P₀ i j = a₀ i) (hcol₀ : ∀ j, ∑ i, P₀ i j = b₀ j)
    (hrowR : ∀ i, ∑ j, R i j = a i - θ * a₀ i)
    (hcolR : ∀ j, ∑ i, R i j = b j - θ * b₀ j)
    (α : Fin M → Measure X) (β : Fin L → Measure Y)
    [∀ i, IsProbabilityMeasure (α i)] [∀ j, IsProbabilityMeasure (β j)] :
    let χ := finiteClassPopulationCoupling (fun i j ↦ θ * P₀ i j) α β
    let ξ := finiteClassPopulationCoupling R α β
    ((χ + ξ).map Prod.fst = ∑ i, ENNReal.ofReal (a i) • α i) ∧
    ((χ + ξ).map Prod.snd = ∑ j, ENNReal.ofReal (b j) • β j) ∧
    ξ ≤ χ + ξ := by
  dsimp only
  have hn i j := add_nonneg (mul_nonneg hθ (hP₀ i j)) (hR i j)
  have hs : finiteClassPopulationCoupling (fun i j ↦ θ * P₀ i j) α β +
      finiteClassPopulationCoupling R α β =
      finiteClassPopulationCoupling (fun i j ↦ θ * P₀ i j + R i j) α β :=
    (finiteClassPopulationCoupling_add _ _ _ _ (fun i j ↦ mul_nonneg hθ (hP₀ i j)) hR).symm
  refine ⟨?_, ?_, Measure.le_add_left le_rfl⟩
  · rw [hs, finiteClassPopulationCoupling_fst _ α β hn]
    congr 1
    funext i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrow₀ i, hrowR i]
    congr 2
    ring
  · rw [hs, finiteClassPopulationCoupling_snd _ α β hn]
    congr 1
    funext j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcol₀ j, hcolR j]
    congr 2
    ring

/-- The deterministic residual flow has small raw mass when the original finite
class profile is uniformly close to its reference. -/
theorem referenceResidualClockFlow_mass_le
    {M L : ℕ} (a₀ : Fin M → ℝ) (b₀ : Fin L → ℝ) (η : ℝ)
    (a : Fin M → ℝ) (b : Fin L → ℝ) (δ : ℝ)
    (hrow : ∀ i, ∑ j, referenceResidualClockFlow a₀ b₀ η a b i j =
      a i - (1 - η) * a₀ i)
    (hclose : ∀ i, |a i - a₀ i| ≤ δ) :
    (∑ i, ∑ j, referenceResidualClockFlow a₀ b₀ η a b i j) ≤
      η * (∑ i, a₀ i) + (M : ℝ) * δ := by
  have herr : (∑ i, a i) - ∑ i, a₀ i ≤ (M : ℝ) * δ := by
    calc
      _ = ∑ i, (a i - a₀ i) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ _i : Fin M, δ := Finset.sum_le_sum fun i hi ↦ (le_abs_self _).trans (hclose i)
      _ = _ := by simp
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  nlinarith

end OTSelector.Reconstruction

end
end
