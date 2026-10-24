import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Analysis.Convex.ProductVarianceTensorization

Conditions: A finite product of uniform interval laws, square-integrable or explicitly integrable readouts and coordinate-energy bounds as stated.

Objects: Coordinate replacement identities, product measure preservation, independent squared-difference identity and a dimension-factor variance estimate.

Proof detail: Telescope by replacing coordinates one at a time, bound the square of the sum by dimension times the sum of squares, and integrate using product laws and the independent-copy identity.

## Mathematical sources

- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=41): Section 1.6.3, variance identities (1.6.2)–(1.6.4), p. 33; Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49.
- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.3 (Hölder), p. 29.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf): Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).

Source relation: Locally constructed product replacement argument. The result carries a dimension factor and is not labeled the sharp Efron–Stein inequality.
-/

/-! Coordinate telescoping and true finite-product energy tensorization. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- Replace the first `k` coordinates of `x` by those of `y`. -/
def cubeCoordinateMix {q : ℕ} {α : Type*} (k : ℕ) (x y : Fin q → α) : Fin q → α :=
  fun i ↦ if i.val < k then y i else x i

@[simp] theorem cubeCoordinateMix_zero {q : ℕ} {α : Type*} (x y : Fin q → α) :
    cubeCoordinateMix 0 x y = x := by
  funext i
  simp [cubeCoordinateMix]

@[simp] theorem cubeCoordinateMix_dim {q : ℕ} {α : Type*} (x y : Fin q → α) :
    cubeCoordinateMix q x y = y := by
  funext i
  simp [cubeCoordinateMix, i.isLt]

/-- Each telescoping step changes exactly the original coordinate being integrated. -/
theorem cubeCoordinateMix_succ {q : ℕ} {α : Type*} (x y : Fin q → α) (i : Fin q) :
    cubeCoordinateMix (i.val + 1) x y =
      Function.update (cubeCoordinateMix i.val x y) i (y i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [cubeCoordinateMix]
  · have hj : j.val ≠ i.val := fun he ↦ h (Fin.ext he)
    simp only [Function.update_of_ne h, cubeCoordinateMix]
    split_ifs <;> first | rfl | omega

/-- The exact finite coordinate decomposition of a function difference. -/
theorem sum_cubeCoordinateMix_sub {q : ℕ} {α : Type*}
    (f : (Fin q → α) → ℝ) (x y : Fin q → α) :
    (∑ i : Fin q, (f (cubeCoordinateMix (i.val + 1) x y) -
      f (cubeCoordinateMix i.val x y))) = f y - f x := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ f (cubeCoordinateMix (k + 1) x y) -
    f (cubeCoordinateMix k x y)) q]
  simpa using Finset.sum_range_sub (fun k ↦ f (cubeCoordinateMix k x y)) q

/-- Cauchy--Schwarz for the actual coordinate path, with no regularity hypothesis. -/
theorem cubeCoordinateMix_sub_sq_le {q : ℕ} {α : Type*}
    (f : (Fin q → α) → ℝ) (x y : Fin q → α) :
    (f y - f x) ^ 2 ≤ (q : ℝ) * ∑ i : Fin q,
      (f (cubeCoordinateMix (i.val + 1) x y) -
        f (cubeCoordinateMix i.val x y)) ^ 2 := by
  rw [← sum_cubeCoordinateMix_sub f x y]
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_id] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin q ↦ f (cubeCoordinateMix (i.val + 1) x y) -
        f (cubeCoordinateMix i.val x y)))

/-- Mixing independent finite-product samples preserves the original product law. -/
theorem measurePreserving_cubeCoordinateMix {q : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin q → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (k : ℕ) :
    MeasurePreserving (fun p : (Fin q → α) × (Fin q → α) ↦
      cubeCoordinateMix k p.1 p.2) ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
  classical
  have hm : Measurable (fun p : (Fin q → α) × (Fin q → α) ↦
      cubeCoordinateMix k p.1 p.2) := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp only [cubeCoordinateMix]
    split_ifs <;> fun_prop
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun p : (Fin q → α) × (Fin q → α) ↦ cubeCoordinateMix k p.1 p.2) ⁻¹'
      univ.pi s =
      (univ.pi fun i ↦ if i.val < k then univ else s i) ×ˢ
        (univ.pi fun i ↦ if i.val < k then s i else univ) := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, cubeCoordinateMix, mem_prod]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · intro i
        split_ifs with hi
        · trivial
        · simpa [hi] using hp i
      · intro i
        split_ifs with hi
        · simpa [hi] using hp i
        · trivial
    · rintro ⟨hx, hy⟩ i
      by_cases hi : i.val < k
      · simpa [hi] using hy i
      · simpa [hi] using hx i
  rw [he, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- Refreshing one coordinate with an independent sample preserves the cube law. -/
theorem measurePreserving_cubeCoordinateUpdate {q : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin q → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin q) :
    MeasurePreserving (fun p : (Fin q → α) × α ↦ Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  classical
  have hm : Measurable (fun p : (Fin q → α) × α ↦ Function.update p.1 i p.2) := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases h : j = i
    · subst j
      simpa using (measurable_snd : Measurable (fun p : (Fin q → α) × α ↦ p.2))
    · simpa [Function.update_of_ne h, Function.comp_def] using (measurable_pi_apply j).comp
        (measurable_fst : Measurable (fun p : (Fin q → α) × α ↦ p.1))
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun p : (Fin q → α) × α ↦ Function.update p.1 i p.2) ⁻¹' univ.pi s =
      (univ.pi fun j ↦ if j = i then univ else s j) ×ˢ s i := by
    ext p
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro hp
      refine ⟨fun j ↦ ?_, ?_⟩
      · by_cases hj : j = i
        · simp [hj]
        · simpa [hj, Function.update_of_ne hj] using hp j
      · simpa using hp i
    · rintro ⟨hx, ht⟩ j
      by_cases hj : j = i
      · simpa [hj] using ht
      · simpa [hj] using hx j
  rw [he, Measure.prod_prod, Measure.pi_pi]
  have hi : (∏ j : Fin q, μ j (if j = i then univ else s j)) * μ i (s i) =
      ∏ j : Fin q, μ j (s j) := by
    have : (fun j : Fin q ↦ μ j (if j = i then univ else s j)) =
        Function.update (fun j ↦ μ j (s j)) i 1 := by
      funext j
      by_cases hj : j = i <;> simp [hj]
    rw [this, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp only [one_mul]
    simpa [mul_comm, Finset.sdiff_singleton_eq_erase] using (Finset.prod_erase_mul (Finset.univ) (fun j ↦ μ j (s j))
      (Finset.mem_univ i))
  exact hi

/-- Integrating a coordinate refresh returns the original finite-product integral. -/
theorem integral_cubeCoordinateUpdate {q : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin q → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin q)
    {g : (Fin q → α) → ℝ} (hg : Integrable g (Measure.pi μ)) :
    (∫ z, ∫ t, g (Function.update z i t) ∂μ i ∂Measure.pi μ) =
      ∫ z, g z ∂Measure.pi μ := by
  let T : (Fin q → α) × α → (Fin q → α) := fun p ↦ Function.update p.1 i p.2
  have hm : MeasurePreserving T ((Measure.pi μ).prod (μ i)) (Measure.pi μ) :=
    measurePreserving_cubeCoordinateUpdate μ i
  have hint := hm.integrable_comp_of_integrable hg
  dsimp only [Function.comp_def, T] at hint
  rw [← integral_prod _ hint]
  have he := integral_map hm.measurable.aemeasurable
    (show AEStronglyMeasurable g (Measure.map T ((Measure.pi μ).prod (μ i))) by
      rw [hm.map_eq]; exact hg.aestronglyMeasurable)
  rw [hm.map_eq] at he
  exact he.symm

/-- Slice averaging of a true integrable energy is integrable, without differentiating an integral. -/
theorem integrable_cubeCoordinateUpdate {q : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin q → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin q)
    {g : (Fin q → α) → ℝ} (hg : Integrable g (Measure.pi μ)) :
    Integrable (fun z ↦ ∫ t, g (Function.update z i t) ∂μ i) (Measure.pi μ) := by
  exact ((measurePreserving_cubeCoordinateUpdate μ i).integrable_comp_of_integrable hg).integral_prod_left

/-- The square difference of two independent samples is integrable under actual L2 hypotheses. -/
theorem integrable_independent_sub_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x ↦ (f x)^2) μ) :
    Integrable (fun p : X × X ↦ (f p.2 - f p.1)^2) (μ.prod μ) := by
  convert ((hf2.comp_fst μ).add (hf2.comp_snd μ)).sub ((hf.mul_prod hf).const_mul 2) using 1
  funext p
  dsimp
  ring

/-- Exact variance identity for independent samples; the mean-zero bulk energy is twice the variance. -/
theorem integral_independent_sub_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x ↦ (f x)^2) μ) :
    (∫ p : X × X, (f p.2 - f p.1)^2 ∂μ.prod μ) =
      2 * ((∫ x, (f x)^2 ∂μ) - (∫ x, f x ∂μ)^2) := by
  have he : (fun p : X × X ↦ (f p.2 - f p.1)^2) =
      (fun p ↦ (f p.1)^2 + (f p.2)^2 - 2*(f p.1 * f p.2)) := by
    funext p; ring
  rw [he, integral_sub (f := fun p : X × X ↦ (f p.1)^2 + (f p.2)^2)
    (g := fun p : X × X ↦ 2*(f p.1 * f p.2))
    ((hf2.comp_fst μ).add (hf2.comp_snd μ)) ((hf.mul_prod hf).const_mul 2),
    integral_add (f := fun p : X × X ↦ (f p.1)^2)
      (g := fun p : X × X ↦ (f p.2)^2) (hf2.comp_fst μ) (hf2.comp_snd μ),
    integral_const_mul, integral_fun_fst (fun x ↦ (f x)^2),
    integral_fun_snd (fun x ↦ (f x)^2), integral_prod_mul]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

/-- Coordinate tensorization of true slice energies on a finite-product probability space.
The hypothesis compares each single-coordinate difference with its own actual slice energy;
it does not assume the resulting multidimensional Poincare inequality. -/
theorem cube_tensorization_sq_le {q : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin q → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin q → α) → ℝ} (hf : Integrable f (Measure.pi μ))
    (hf2 : Integrable (fun x ↦ (f x)^2) (Measure.pi μ))
    {G : Fin q → (Fin q → α) → ℝ} (hG : ∀ i, Integrable (G i) (Measure.pi μ))
    (hcoord : ∀ i : Fin q, ∀ᵐ p : (Fin q → α) × (Fin q → α)
      ∂(Measure.pi μ).prod (Measure.pi μ),
      (f (cubeCoordinateMix (i.val + 1) p.1 p.2) -
        f (cubeCoordinateMix i.val p.1 p.2))^2 ≤ G i (cubeCoordinateMix i.val p.1 p.2)) :
    2 * ((∫ x, (f x)^2 ∂Measure.pi μ) - (∫ x, f x ∂Measure.pi μ)^2) ≤
      (q : ℝ) * ∑ i : Fin q, ∫ x, G i x ∂Measure.pi μ := by
  let ν := (Measure.pi μ).prod (Measure.pi μ)
  have hGi (i : Fin q) : Integrable
      (fun p : (Fin q → α) × (Fin q → α) ↦ G i (cubeCoordinateMix i.val p.1 p.2)) ν :=
    (measurePreserving_cubeCoordinateMix μ i.val).integrable_comp_of_integrable (hG i)
  have hsum : Integrable (fun p : (Fin q → α) × (Fin q → α) ↦
      (q : ℝ) * ∑ i : Fin q, G i (cubeCoordinateMix i.val p.1 p.2)) ν :=
    (integrable_finsetSum _ (fun i _ ↦ hGi i)).const_mul (q : ℝ)
  have hbound : ∀ᵐ p : (Fin q → α) × (Fin q → α) ∂ν,
      (f p.2 - f p.1)^2 ≤ (q : ℝ) * ∑ i : Fin q, G i (cubeCoordinateMix i.val p.1 p.2) := by
    filter_upwards [ae_all_iff.mpr hcoord] with p hp
    exact (cubeCoordinateMix_sub_sq_le f p.1 p.2).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hp i)) (Nat.cast_nonneg q))
  have hm := integral_mono_ae (integrable_independent_sub_sq hf hf2) hsum hbound
  rw [integral_independent_sub_sq hf hf2, integral_const_mul, integral_finsetSum _
    (fun i _ ↦ hGi i)] at hm
  have he (i : Fin q) : (∫ p : (Fin q → α) × (Fin q → α),
      G i (cubeCoordinateMix i.val p.1 p.2) ∂ν) = ∫ z, G i z ∂Measure.pi μ := by
    have hmp := measurePreserving_cubeCoordinateMix μ i.val
    have he := integral_map hmp.measurable.aemeasurable
      (show AEStronglyMeasurable (G i) (Measure.map
        (fun p : (Fin q → α) × (Fin q → α) ↦ cubeCoordinateMix i.val p.1 p.2) ν) by
        rw [hmp.map_eq]; exact (hG i).aestronglyMeasurable)
    rw [hmp.map_eq] at he
    exact he.symm
  simpa only [he] using hm

/-- Derivative-energy form of the finite-product theorem, using literal coordinate-slice integrals. -/
theorem cube_tensorization_integrated_energy_sq_le
    {q : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Fin q → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (Fin q → α) → ℝ} (hf : Integrable f (Measure.pi μ))
    (hf2 : Integrable (fun x ↦ (f x)^2) (Measure.pi μ))
    {g : Fin q → (Fin q → α) → ℝ} (hg : ∀ i, Integrable (g i) (Measure.pi μ))
    (hcoord : ∀ i : Fin q, ∀ᵐ p : (Fin q → α) × (Fin q → α)
      ∂(Measure.pi μ).prod (Measure.pi μ),
      (f (cubeCoordinateMix (i.val + 1) p.1 p.2) -
        f (cubeCoordinateMix i.val p.1 p.2))^2 ≤
          ∫ t, g i (Function.update (cubeCoordinateMix i.val p.1 p.2) i t) ∂μ i) :
    2 * ((∫ x, (f x)^2 ∂Measure.pi μ) - (∫ x, f x ∂Measure.pi μ)^2) ≤
      (q : ℝ) * ∑ i : Fin q, ∫ x, g i x ∂Measure.pi μ := by
  have h := cube_tensorization_sq_le μ hf hf2
    (fun i ↦ integrable_cubeCoordinateUpdate μ i (hg i)) hcoord
  simpa only [integral_cubeCoordinateUpdate μ _ (hg _)] using h

end OTSelector.Reconstruction
