import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedTypeRestriction
import OTSelector.Reconstruction.FinslerConcreteUpperCompactColorSplit

/-! Fixed compact good/bad restrictions commute with deterministic retained label truncation. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

section CompactRestrictions

variable {X Z W C : Type*} [MeasurableSpace X] [Fintype C]

/-- A deterministic restriction commutes with the compact good share, including its
finite sum over the original literal cells. -/
theorem compactColorGoodComponent_restrict (τ : Measure X) (label : X → Z)
    (coord : X → W) (cell : C → Set Z) (K : C → Set W)
    {S : Set X} (hS : MeasurableSet S) :
    compactColorGoodComponent (τ.restrict S) label coord cell K =
      (compactColorGoodComponent τ label coord cell K).restrict S := by
  unfold compactColorGoodComponent
  calc
    _ = ∑ c, (τ.restrict ((label ⁻¹' cell c) ∩ (coord ⁻¹' K c))).restrict S := by
      apply Finset.sum_congr rfl
      intro c _
      exact (Measure.restrict_comm hS).symm
    _ = _ := (map_sum (Measure.restrictₗ S) _ _).symm

omit [Fintype C] in
/-- Each original bad cell share has the same exact restriction identity. -/
theorem compactColorBadComponent_restrict (τ : Measure X) (label : X → Z)
    (coord : X → W) (cell : C → Set Z) (K : C → Set W)
    {S : Set X} (hS : MeasurableSet S) (c : C) :
    compactColorBadComponent (τ.restrict S) label coord cell K c =
      (compactColorBadComponent τ label coord cell K c).restrict S := by
  exact (Measure.restrict_comm hS).symm

end CompactRestrictions

variable {X Z W C T : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {π : Measure (X × X)} [IsFiniteMeasure π]
    (D : PopulationSubcouplingTypes π T) (hwhole : χ + ξ = π)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (label : X × X → Z) (coord : T → X × X → W)
    (cell : C → Set Z) (K : T → C → Set W)

/-- Under every prescribed label truncation the good part uses the same compact
sets, old atlas indices, and original retained component before restriction. -/
theorem original_retained_compact_good_label_restriction (t : T) :
    compactColorGoodComponent
      ((D.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
        ((restrictOriginalRetainedResidual_le χ ξ a ha hG).trans_eq hwhole)).component
          (false, t)) label (coord t) cell (K t) =
      (compactColorGoodComponent
        ((D.rnSubplanTypes ξ ((Measure.le_add_left le_rfl).trans_eq hwhole)).component
          (false, t)) label (coord t) cell (K t)).restrict {p | a p.1 ∈ G} := by
  rw [original_retained_type_label_restriction_of_sum_eq χ ξ a ha hG D hwhole t]
  exact compactColorGoodComponent_restrict _ label (coord t) cell (K t)
    (S := {p | a p.1 ∈ G}) ((ha.comp measurable_fst) hG)

omit [Fintype C] in
/-- The small discarded compact share of each original cell is restricted exactly;
the truncation does not create a new bad population. -/
theorem original_retained_compact_bad_label_restriction (c : C) (t : T) :
    compactColorBadComponent
      ((D.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
        ((restrictOriginalRetainedResidual_le χ ξ a ha hG).trans_eq hwhole)).component
          (false, t)) label (coord t) cell (K t) c =
      (compactColorBadComponent
        ((D.rnSubplanTypes ξ ((Measure.le_add_left le_rfl).trans_eq hwhole)).component
          (false, t)) label (coord t) cell (K t) c).restrict {p | a p.1 ∈ G} := by
  rw [original_retained_type_label_restriction_of_sum_eq χ ξ a ha hG D hwhole t]
  exact compactColorBadComponent_restrict _ label (coord t) cell (K t)
    (S := {p | a p.1 ∈ G}) ((ha.comp measurable_fst) hG) c

end OTSelector.Reconstruction
