import OTSelector.Reconstruction.FinslerConcreteUpperForwardCoreBound
import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity

/-! Only actual allowed edges need a frozen cost bound. Inactive original
sample indices keep their places and impose no artificial geometric carrier. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ} {J : Type*} [Fintype J]

/-- The inverse relative comparison uses only legal entries, including in the
finite-class augmentation correction. Illegal costs may be arbitrary. -/
theorem legalMaximumValue_le_inverse_relative_core_of_allowed
    (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (physical frozen probe : Fin m → Fin n → ℝ)
    {ρ G edgeBound : ℝ} (hρ : ρ < 1) (hG : 0 ≤ G) (hB : 0 ≤ edgeBound)
    (hrelative : ∀ e ∈ σ.edges,
      |physical e.1 e.2 - frozen e.1 e.2| ≤ ρ * frozen e.1 e.2)
    (hprobe : ∀ i j, (i, j) ∈ allowed → |probe i j| ≤ G) (tilt : ℝ)
    (hedge : ∀ i j, (i, j) ∈ allowed → |frozen i j + tilt * probe i j| ≤ edgeBound) :
    legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * probe i j) ≤
      σ.cost physical / (1 - ρ) + (σ.card : ℝ) * (|tilt| * G) +
      ((legalMaximumCard allowed - σ.card : ℕ) : ℝ) *
        ((2 * (Fintype.card J : ℝ) - 1) * edgeBound) := by
  classical
  let frozen' := allowedMaskedCost allowed frozen
  let probe' := allowedMaskedCost allowed probe
  have hrel' : ∀ e ∈ σ.edges,
      |physical e.1 e.2 - frozen' e.1 e.2| ≤ ρ * frozen' e.1 e.2 := by
    intro e he
    simpa only [frozen', allowedMaskedCost, ite_eq_left (hσ he)] using hrelative e he
  have hp' : ∀ i j, |probe' i j| ≤ G :=
    abs_allowedMaskedCost_le allowed probe hG hprobe
  have he' : ∀ i j, |frozen' i j + tilt * probe' i j| ≤ edgeBound := by
    intro i j
    by_cases hij : (i, j) ∈ allowed
    · simpa only [frozen', probe', allowedMaskedCost, ite_eq_left hij] using hedge i j hij
    · simpa only [frozen', probe', allowedMaskedCost, ite_eq_right hij, mul_zero, add_zero,
        abs_zero] using hB
  have hvalue : legalMaximumValue allowed (fun i j ↦ frozen' i j + tilt * probe' i j) =
      legalMaximumValue allowed (fun i j ↦ frozen i j + tilt * probe i j) := by
    apply legalMaximumValue_congr_on_allowed
    intro i j hij
    simp only [frozen', probe', allowedMaskedCost, ite_eq_left hij]
  have h := legalMaximumValue_le_inverse_relative_core allowed σ hσ sourceClass sourceAllows
    hallowed physical frozen' probe' hρ hG hB hrel' hp' tilt he'
  rwa [hvalue] at h

end OTSelector.Reconstruction.PartialMatching
