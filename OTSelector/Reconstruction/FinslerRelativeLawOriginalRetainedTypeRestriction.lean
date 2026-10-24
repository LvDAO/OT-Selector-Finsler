import OTSelector.Probability.RNSubplanTypeRefinement
import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction

/-! Deterministic label restrictions preserve the literal retained share of every old type. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PopulationSubcouplingTypes

variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
    {π : Measure (X × Y)} [IsFiniteMeasure π] (D : PopulationSubcouplingTypes π T)

/-- Adding two original subplans adds their shares inside each fixed original type. -/
theorem rnSubplanComponent_add (η ζ : Measure (X × Y))
    [IsFiniteMeasure η] [IsFiniteMeasure ζ] (t : T) :
    D.rnSubplanComponent (η + ζ) t =
      D.rnSubplanComponent η t + D.rnSubplanComponent ζ t := by
  unfold rnSubplanComponent
  rw [withDensity_congr_ae (ae_mono (D.component_le t) (Measure.rnDeriv_add' η ζ π)),
    withDensity_add_left (Measure.measurable_rnDeriv η π)]

/-- The whole original population has unit Radon--Nikodym weight on every old type. -/
theorem rnSubplanComponent_self (t : T) : D.rnSubplanComponent π t = D.component t := by
  unfold rnSubplanComponent
  rw [withDensity_congr_ae (ae_mono (D.component_le t) (Measure.rnDeriv_self π))]
  exact withDensity_one

/-- Restricting a deterministic original subplan restricts its share of each old type. -/
theorem rnSubplanComponent_restrict (η : Measure (X × Y)) [IsFiniteMeasure η]
    {S : Set (X × Y)} (hS : MeasurableSet S) (t : T) :
    D.rnSubplanComponent (η.restrict S) t = (D.rnSubplanComponent η t).restrict S := by
  unfold rnSubplanComponent
  rw [withDensity_congr_ae (ae_mono (D.component_le t) (Measure.rnDeriv_restrict η π hS)),
    withDensity_indicator hS, ← restrict_withDensity hS]

/-- A retained flag is exactly the original complementary subplan's share, type by type. -/
theorem rnSubplanTypes_retained_component_eq (χ ξ : Measure (X × Y))
    [IsFiniteMeasure χ] [IsFiniteMeasure ξ] (hwhole : χ + ξ = π) (hξ : ξ ≤ π) (t : T) :
    (D.rnSubplanTypes ξ hξ).component (false, t) = D.rnSubplanComponent χ t := by
  let _ := D.rnSubplanComponent_isFinite ξ hξ t
  have hsplit : D.rnSubplanComponent χ t + D.rnSubplanComponent ξ t = D.component t := by
    rw [← D.rnSubplanComponent_add χ ξ t, hwhole, D.rnSubplanComponent_self]
  change D.component t - D.rnSubplanComponent ξ t = _
  rw [← hsplit, Measure.add_sub_cancel]

end PopulationSubcouplingTypes

variable {X Z T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (D : PopulationSubcouplingTypes (χ + ξ) T)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)

/-- The actual retained old-type share after label truncation is the restriction of the
same original retained share. The whole original coupling and its old types are unchanged. -/
theorem original_retained_type_label_restriction (t : T) :
    (D.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
      (restrictOriginalRetainedResidual_le χ ξ a ha hG)).component (false, t) =
        ((D.rnSubplanTypes ξ (Measure.le_add_left le_rfl)).component (false, t)).restrict
          {p | a p.1 ∈ G} := by
  rw [D.rnSubplanTypes_retained_component_eq (χ.restrict {p | a p.1 ∈ G})
    (restrictOriginalRetainedResidual χ ξ a G)
    (original_retained_label_restriction_split χ ξ a ha hG)]
  rw [D.rnSubplanTypes_retained_component_eq χ ξ rfl]
  exact D.rnSubplanComponent_restrict χ (S := {p | a p.1 ∈ G})
    ((ha.comp measurable_fst) hG) t

/-- All deterministic empirical-order truncations are dominated by the same retained old type. -/
theorem original_retained_type_label_restriction_le (t : T) :
    (D.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
      (restrictOriginalRetainedResidual_le χ ξ a ha hG)).component (false, t) ≤
        (D.rnSubplanTypes ξ (Measure.le_add_left le_rfl)).component (false, t) := by
  rw [original_retained_type_label_restriction χ ξ D a ha hG t]
  exact Measure.restrict_le_self

/-- The same restriction identity uses an already chosen original ambient population,
without transporting or choosing a new atlas of types. -/
theorem original_retained_type_label_restriction_of_sum_eq
    {π : Measure (X × X)} [IsFiniteMeasure π]
    (D' : PopulationSubcouplingTypes π T) (hwhole : χ + ξ = π) (t : T) :
    (D'.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
      ((restrictOriginalRetainedResidual_le χ ξ a ha hG).trans_eq hwhole)).component
        (false, t) =
      ((D'.rnSubplanTypes ξ ((Measure.le_add_left le_rfl).trans_eq hwhole)).component
        (false, t)).restrict {p | a p.1 ∈ G} := by
  rw [D'.rnSubplanTypes_retained_component_eq (χ.restrict {p | a p.1 ∈ G})
    (restrictOriginalRetainedResidual χ ξ a G)
    ((original_retained_label_restriction_split χ ξ a ha hG).trans hwhole)]
  rw [D'.rnSubplanTypes_retained_component_eq χ ξ hwhole]
  exact D'.rnSubplanComponent_restrict χ (S := {p | a p.1 ∈ G})
    ((ha.comp measurable_fst) hG) t

/-- Every prescribed empirical-order truncation is dominated inside the same already
chosen original old-type population. -/
theorem original_retained_type_label_restriction_le_of_sum_eq
    {π : Measure (X × X)} [IsFiniteMeasure π]
    (D' : PopulationSubcouplingTypes π T) (hwhole : χ + ξ = π) (t : T) :
    (D'.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
      ((restrictOriginalRetainedResidual_le χ ξ a ha hG).trans_eq hwhole)).component
        (false, t) ≤
      (D'.rnSubplanTypes ξ ((Measure.le_add_left le_rfl).trans_eq hwhole)).component
        (false, t) := by
  rw [original_retained_type_label_restriction_of_sum_eq χ ξ a ha hG D' hwhole t]
  exact Measure.restrict_le_self

end OTSelector.Reconstruction
