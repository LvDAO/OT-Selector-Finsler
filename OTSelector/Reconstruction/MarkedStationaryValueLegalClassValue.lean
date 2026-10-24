import OTSelector.Reconstruction.MarkedStationaryValueLegalClasses

/-!
# Quantitative legal maximum-cardinality recovery on finite class graphs

Every increment uses a genuine short alternating chain. Iterating reaches the
true legal maximum while charging all removed signed edges. The coefficient
depends only on the fixed number of source classes, rather than sample size.
-/

open Set Function
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {J : Type*} [Fintype J]

/-- A single bounded-cost augmentation, constructed on the actual legal graph. -/
theorem exists_legal_class_augmentation
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (hcard : σ.card < legalMaximumCard allowed)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal allowed τ ∧ τ.card = σ.card + 1 ∧
        τ.cost c ≤ σ.cost c + (2 * (Fintype.card J : ℝ) - 1) * B := by
  obtain ⟨k, hk, ⟨P⟩⟩ := exists_bounded_classAugmentingChain σ sourceClass sourceAllows
    hallowed hcard
  refine ⟨P.flip, P.flip_isLegal hσ, P.flip_card, (P.flip_cost_le_add_signed c hB).trans ?_⟩
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hB0
  have hkR : (k : ℝ) + 1 ≤ (Fintype.card J : ℝ) := by exact_mod_cast hk
  linarith

/-- Recover any larger feasible cardinality by actual legal augmentations.
Edges may change; the signed cost bound accounts for all changes. -/
theorem exists_legal_class_recovery
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    ∀ k : ℕ, σ.card + k ≤ legalMaximumCard allowed →
      ∃ τ : OTSelector.PartialMatching m n,
        IsLegal allowed τ ∧ τ.card = σ.card + k ∧
          τ.cost c ≤ σ.cost c + (k : ℝ) * ((2 * (Fintype.card J : ℝ) - 1) * B) := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨σ, hσ, by omega, by simp⟩
  | succ k ih =>
      intro hk
      obtain ⟨τ, hτlegal, hτcard, hτcost⟩ := ih (by omega)
      obtain ⟨υ, hυlegal, hυcard, hυcost⟩ := exists_legal_class_augmentation τ hτlegal
        sourceClass sourceAllows hallowed (by omega) c hB0 hB
      refine ⟨υ, hυlegal, by omega, ?_⟩
      push_cast
      nlinarith

/-- A legal core controls the actual signed optimum at the graph's maximum
cardinality, with a fixed source-class coefficient times its true deficit. -/
theorem legalMaximumValue_le_cost_add_class_deficit
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    legalMaximumValue allowed c ≤ σ.cost c +
      ((legalMaximumCard allowed - σ.card : ℕ) : ℝ) *
        ((2 * (Fintype.card J : ℝ) - 1) * B) := by
  have hcard := card_le_legalMaximumCard hσ
  obtain ⟨τ, hτlegal, hτcard, hτcost⟩ := exists_legal_class_recovery σ hσ
    sourceClass sourceAllows hallowed c hB0 hB (legalMaximumCard allowed - σ.card) (by omega)
  exact (legalMaximumValue_le c hτlegal (by omega)).trans hτcost

end OTSelector.Reconstruction.PartialMatching
