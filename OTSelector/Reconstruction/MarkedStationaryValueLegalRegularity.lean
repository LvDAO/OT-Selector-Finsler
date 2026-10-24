import OTSelector.Finite.LegalMatchingValue

/-!
# Regularity of finite legal matching values

All cost comparisons and probe bounds are imposed only on actual allowed edges.
Changing illegal entries, including zero extension there, leaves the legal
minimum unchanged. The attained finite minimum gives allowed-only perturbation,
absolute bounds, concavity and tilt-Lipschitz control at its true legal maximum
cardinality.
-/

open Set Function MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ}

/-- A legal matching's cost only uses entries on its actual allowed graph. -/
theorem cost_eq_of_eq_on_allowed {allowed : Finset (Fin m × Fin n)}
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal allowed σ)
    {c d : Fin m → Fin n → ℝ} (h : ∀ i j, (i, j) ∈ allowed → c i j = d i j) :
    σ.cost c = σ.cost d := by
  exact Finset.sum_congr rfl (fun e he ↦ h e.1 e.2 (hσ he))

/-- The literal legal minimum is invariant under changes of illegal cost entries. -/
theorem legalMaximumValue_congr_on_allowed (allowed : Finset (Fin m × Fin n))
    {c d : Fin m → Fin n → ℝ} (h : ∀ i j, (i, j) ∈ allowed → c i j = d i j) :
    legalMaximumValue allowed c = legalMaximumValue allowed d := by
  have hcost : (fun σ : LegalMaximumMatching allowed ↦ σ.val.cost c) =
      fun σ : LegalMaximumMatching allowed ↦ σ.val.cost d :=
    funext (fun σ ↦ cost_eq_of_eq_on_allowed σ.val σ.property.1 h)
  unfold legalMaximumValue
  rw [hcost]

/-- A zero extension of the cost off the allowed graph; the minimization stays legal. -/
def allowedMaskedCost (allowed : Finset (Fin m × Fin n)) (c : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  if (i, j) ∈ allowed then c i j else 0

/-- Masking never alters the true legal minimum. -/
@[simp]
theorem legalMaximumValue_allowedMaskedCost (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) :
    legalMaximumValue allowed (allowedMaskedCost allowed c) = legalMaximumValue allowed c := by
  apply legalMaximumValue_congr_on_allowed
  intro i j hij
  simp [allowedMaskedCost, hij]

/-- An allowed-edge probe bound controls every legal matching's probe readout. -/
theorem abs_cost_le_card_mul_of_allowed {allowed : Finset (Fin m × Fin n)}
    {c : Fin m → Fin n → ℝ} {B : ℝ} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) (hB : ∀ i j, (i, j) ∈ allowed → |c i j| ≤ B) :
    |σ.cost c| ≤ (σ.card : ℝ) * B := by
  calc |σ.cost c| ≤ ∑ e ∈ σ.edges, |c e.1 e.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ σ.edges, B := Finset.sum_le_sum (fun e he ↦ hB e.1 e.2 (hσ he))
    _ = (σ.card : ℝ) * B := by
      simp only [Finset.sum_const, nsmul_eq_mul, OTSelector.PartialMatching.card]

/-- No bound or interpretation of illegal entries is needed for the legal value bound. -/
theorem abs_legalMaximumValue_le_of_allowed (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) {B : ℝ}
    (hB : ∀ i j, (i, j) ∈ allowed → |c i j| ≤ B) :
    |legalMaximumValue allowed c| ≤ (legalMaximumCard allowed : ℝ) * B := by
  obtain ⟨σ, hlegal, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed c
  rw [← hcost, ← hcard]
  exact abs_cost_le_card_mul_of_allowed σ hlegal hB

/-- One-sided entry perturbations only on legal edges control the true signed minimum. -/
theorem legalMaximumValue_le_add_of_allowed (allowed : Finset (Fin m × Fin n))
    (c d : Fin m → Fin n → ℝ) {B : ℝ}
    (hB : ∀ i j, (i, j) ∈ allowed → c i j ≤ d i j + B) :
    legalMaximumValue allowed c ≤ legalMaximumValue allowed d +
      (legalMaximumCard allowed : ℝ) * B := by
  obtain ⟨σ, hlegal, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed d
  refine (legalMaximumValue_le c hlegal hcard).trans ?_
  calc σ.cost c ≤ ∑ e ∈ σ.edges, (d e.1 e.2 + B) :=
      Finset.sum_le_sum (fun e he ↦ hB e.1 e.2 (hlegal he))
    _ = σ.cost d + (σ.card : ℝ) * B := by
      simp only [OTSelector.PartialMatching.cost, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, OTSelector.PartialMatching.card]
    _ = _ := by rw [hcard, hcost]

/-- Absolute legal-edge perturbations control the true legal minimum. -/
theorem abs_legalMaximumValue_sub_le_of_allowed (allowed : Finset (Fin m × Fin n))
    (c d : Fin m → Fin n → ℝ) {B : ℝ}
    (hB : ∀ i j, (i, j) ∈ allowed → |c i j - d i j| ≤ B) :
    |legalMaximumValue allowed c - legalMaximumValue allowed d| ≤
      (legalMaximumCard allowed : ℝ) * B := by
  have hcd := legalMaximumValue_le_add_of_allowed allowed c d
    (fun i j hij ↦ by have h := (abs_le.mp (hB i j hij)).2; linarith)
  have hdc := legalMaximumValue_le_add_of_allowed allowed d c
    (fun i j hij ↦ by have h := (abs_le.mp (hB i j hij)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The legal finite pressure is Lipschitz with its actual maximum cardinality. -/
theorem abs_legalMaximumValue_tilt_sub_le (allowed : Finset (Fin m × Fin n))
    (c g : Fin m → Fin n → ℝ) {G : ℝ}
    (hG : ∀ i j, (i, j) ∈ allowed → |g i j| ≤ G) (t u : ℝ) :
    |legalMaximumValue allowed (fun i j ↦ c i j + t * g i j) -
      legalMaximumValue allowed (fun i j ↦ c i j + u * g i j)| ≤
        (legalMaximumCard allowed : ℝ) * (G * |t - u|) := by
  apply abs_legalMaximumValue_sub_le_of_allowed
  intro i j hij
  have hid : (c i j + t * g i j) - (c i j + u * g i j) = (t - u) * g i j := by ring
  calc
    |(c i j + t * g i j) - (c i j + u * g i j)| = |(t - u) * g i j| := congrArg abs hid
    _ = |t - u| * |g i j| := abs_mul _ _
    _ ≤ |t - u| * G := mul_le_mul_of_nonneg_left (hG i j hij) (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- The legal finite pressure is concave; legality and maximum cardinality are fixed in tilt. -/
theorem concaveOn_legalMaximumValue_tilt (allowed : Finset (Fin m × Fin n))
    (c g : Fin m → Fin n → ℝ) :
    ConcaveOn ℝ univ (fun t ↦ legalMaximumValue allowed (fun i j ↦ c i j + t * g i j)) := by
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  obtain ⟨σ, hlegal, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed
    (fun i j ↦ c i j + (a * t + b * u) * g i j)
  have hdecomp : σ.cost (fun i j ↦ c i j + (a * t + b * u) * g i j) =
      a * σ.cost (fun i j ↦ c i j + t * g i j) +
        b * σ.cost (fun i j ↦ c i j + u * g i j) := by
    unfold OTSelector.PartialMatching.cost
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    calc c e.1 e.2 + (a * t + b * u) * g e.1 e.2 =
        (a + b) * c e.1 e.2 + (a * t + b * u) * g e.1 e.2 := by rw [hab]; ring
      _ = _ := by ring
  have ht := mul_le_mul_of_nonneg_left
    (legalMaximumValue_le (fun i j ↦ c i j + t * g i j) hlegal hcard) ha
  have hu := mul_le_mul_of_nonneg_left
    (legalMaximumValue_le (fun i j ↦ c i j + u * g i j) hlegal hcard) hb
  simp only [smul_eq_mul]
  rw [← hcost, hdecomp]
  exact add_le_add ht hu


/-- An allowed-only edge bound gives a global bound after zero extension. -/
theorem abs_allowedMaskedCost_le (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, (i, j) ∈ allowed → |c i j| ≤ B) :
    ∀ i j, |allowedMaskedCost allowed c i j| ≤ B := by
  intro i j
  by_cases hij : (i, j) ∈ allowed
  · simpa [allowedMaskedCost, hij] using hB i j hij
  · simpa [allowedMaskedCost, hij] using hB0

/-- A lower bound only on allowed edges controls the actual legal minimum. -/
theorem le_legalMaximumValue_of_allowed (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : ∀ i j, (i, j) ∈ allowed → L ≤ c i j) :
    (legalMaximumCard allowed : ℝ) * L ≤ legalMaximumValue allowed c := by
  obtain ⟨σ, hlegal, hcard, hcost⟩ := exists_cost_eq_legalMaximumValue allowed c
  rw [← hcost, ← hcard]
  calc
    (σ.card : ℝ) * L = ∑ _e ∈ σ.edges, L := by
      simp only [Finset.sum_const, nsmul_eq_mul, OTSelector.PartialMatching.card]
    _ ≤ σ.cost c := Finset.sum_le_sum (fun e he ↦ hL e.1 e.2 (hlegal he))

end OTSelector.Reconstruction.PartialMatching
