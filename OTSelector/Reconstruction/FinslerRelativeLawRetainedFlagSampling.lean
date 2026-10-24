import OTSelector.Reconstruction.FinslerPopulationSelectedSubplanLaw
import OTSelector.Reconstruction.FinslerPopulationMarkedAssignmentTransfer
import OTSelector.Reconstruction.FinslerRelativeLawUniformRebuiltResidualRepair

/-!
Forgetting the original geometric atlas marks in the residual repair experiment
recovers the literal retained/residual population mixture. The same experiment
therefore supplies both the original residual estimate and retained iid laws.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The prescribed subplan flag, with the absent full-retention mark completed
as a residual flag. Full original type coverage makes that completion null. -/
def subplanRetentionFlag {T : Type*} : Option (Bool × T) → Bool
  | none => true
  | some t => t.1

theorem finiteRNMarkLaw_full_flag_law
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : Bool × T → Measure X) [∀ t, IsFiniteMeasure (m t)]
    (hfull : ∑ t, m t = μ) :
    (finiteRNMarkLaw μ m).map (fun p ↦ (p.1, subplanRetentionFlag p.2)) =
      (∑ t, m (false, t)).map (fun x ↦ (x, false)) +
      (∑ t, m (true, t)).map (fun x ↦ (x, true)) := by
  have hm : Measurable (fun p : X × Option (Bool × T) ↦
      (p.1, subplanRetentionFlag p.2)) :=
    measurable_fst.prodMk ((measurable_of_countable (subplanRetentionFlag (T := T))).comp measurable_snd)
  have hmap (ρ : Measure X) (t : Bool × T) :
      (ρ.map (fun x ↦ (x, some t))).map (fun p ↦ (p.1, subplanRetentionFlag p.2)) =
        ρ.map (fun x ↦ (x, t.1)) := by
    rw [Measure.map_map hm (show Measurable (fun x : X ↦ (x, some t)) from
      measurable_id.prodMk measurable_const)]
    rfl
  rw [finiteRNMarkLaw, hfull, Measure.sub_self, Measure.map_zero, zero_add,
    Measure.map_finset_sum' hm.aemeasurable, Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [hmap]
  rw [Measure.map_finset_sum' (show Measurable (fun x : X ↦ (x, false)) from
      measurable_id.prodMk measurable_const).aemeasurable,
    Measure.map_finset_sum' (show Measurable (fun x : X ↦ (x, true)) from
      measurable_id.prodMk measurable_const).aemeasurable]
  exact add_comm _ _

namespace PopulationSubcouplingTypes
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)

/-- The complementary refined components recover the whole original
population outside the prescribed deterministic subplan. -/
theorem rnSubplanTypes_complementary_sum_eq
    (η : Measure (X × Y)) (hη : η ≤ π) (hfull : ∑ t, D.component t = π) :
    (∑ t, (D.rnSubplanTypes η hη).component (false, t)) = π - η := by
  let _instη : IsFiniteMeasure η := isFiniteMeasure_of_le π hη
  have hsum := D.rnSubplanTypes_sum_eq η hη hfull
  rw [Fintype.sum_prod_type, Fintype.sum_bool,
    D.rnSubplanTypes_selected_sum_eq η hη hfull] at hsum
  calc
    _ = ((∑ t, (D.rnSubplanTypes η hη).component (false, t)) + η) - η :=
      Measure.add_sub_cancel.symm
    _ = π - η := by rw [add_comm _ η, hsum]

end PopulationSubcouplingTypes

namespace PopulationTypedCostData
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  [MeasurableSpace (Option (Bool × T))]
  [MeasurableSingletonClass (Option (Bool × T))]

/-- In the exact marked experiment used for the residual energy estimate,
forgetting the atlas mark leaves the literal original retained/residual law. -/
theorem refineSubplan_flagged_physical_laws
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π) :
    let R := D.refineSubplan η hη
    (R.types.sourceMarkedLaw μ).map (fun p ↦ (p.1, subplanRetentionFlag p.2)) =
      ((π - η).map Prod.fst).map (fun x ↦ (x, false)) +
        (η.map Prod.fst).map (fun x ↦ (x, true)) ∧
    (R.types.targetMarkedLaw ν).map (fun p ↦ (p.1, subplanRetentionFlag p.2)) =
      ((π - η).map Prod.snd).map (fun y ↦ (y, false)) +
        (η.map Prod.snd).map (fun y ↦ (y, true)) := by
  let R := D.refineSubplan η hη
  have hsum : ∑ t, R.types.component t = π := D.types.rnSubplanTypes_sum_eq η hη D.sum_eq
  have hsource : ∑ t, R.types.source t = μ := by
    simp_rw [PopulationSubcouplingTypes.source]
    rw [← Measure.map_finset_sum' measurable_fst.aemeasurable,
      hsum, hπ.1]
  have htarget : ∑ t, R.types.target t = ν := by
    simp_rw [PopulationSubcouplingTypes.target]
    rw [← Measure.map_finset_sum' measurable_snd.aemeasurable,
      hsum, hπ.2]
  have hfalse : ∑ t, R.types.component (false, t) = π - η :=
    D.types.rnSubplanTypes_complementary_sum_eq η hη D.sum_eq
  have htrue : ∑ t, R.types.component (true, t) = η :=
    D.types.rnSubplanTypes_selected_sum_eq η hη D.sum_eq
  constructor
  · rw [PopulationSubcouplingTypes.sourceMarkedLaw, finiteRNMarkLaw_full_flag_law μ _ hsource]
    simp_rw [PopulationSubcouplingTypes.source]
    rw [← Measure.map_finset_sum' measurable_fst.aemeasurable,
      ← Measure.map_finset_sum' measurable_fst.aemeasurable, hfalse, htrue]
  · rw [PopulationSubcouplingTypes.targetMarkedLaw, finiteRNMarkLaw_full_flag_law ν _ htarget]
    simp_rw [PopulationSubcouplingTypes.target]
    rw [← Measure.map_finset_sum' measurable_snd.aemeasurable,
      ← Measure.map_finset_sum' measurable_snd.aemeasurable, hfalse, htrue]

/-- The two independent arrays in the original residual repair experiment have
the exact retained/residual mixture law after only the atlas marks are forgotten. -/
theorem refineSubplan_flagged_iid_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π) :
    let R := D.refineSubplan η hη
    ((Measure.pi (fun _ : I ↦ R.types.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.types.targetMarkedLaw ν))).map
        (Prod.map (fun x i ↦ ((x i).1, subplanRetentionFlag (x i).2))
          (fun y j ↦ ((y j).1, subplanRetentionFlag (y j).2))) =
      (Measure.pi (fun _ : I ↦
        ((π - η).map Prod.fst).map (fun x ↦ (x, false)) +
          (η.map Prod.fst).map (fun x ↦ (x, true)))).prod
      (Measure.pi (fun _ : J ↦
        ((π - η).map Prod.snd).map (fun y ↦ (y, false)) +
          (η.map Prod.snd).map (fun y ↦ (y, true)))) := by
  have hs : Measurable (fun p : X × Option (Bool × T) ↦
      (p.1, subplanRetentionFlag p.2)) :=
    measurable_fst.prodMk ((measurable_of_countable (subplanRetentionFlag (T := T))).comp measurable_snd)
  have ht : Measurable (fun p : Y × Option (Bool × T) ↦
      (p.1, subplanRetentionFlag p.2)) :=
    measurable_fst.prodMk ((measurable_of_countable (subplanRetentionFlag (T := T))).comp measurable_snd)
  have hxs : Measurable (fun x : I → X × Option (Bool × T) ↦
      fun i ↦ ((x i).1, subplanRetentionFlag (x i).2)) :=
    measurable_pi_lambda _ (fun i ↦ hs.comp (measurable_pi_apply i))
  have hys : Measurable (fun y : J → Y × Option (Bool × T) ↦
      fun j ↦ ((y j).1, subplanRetentionFlag (y j).2)) :=
    measurable_pi_lambda _ (fun j ↦ ht.comp (measurable_pi_apply j))
  dsimp only
  rw [← Measure.map_prod_map _ _ hxs hys,
    Measure.pi_map_pi (fun _ ↦ hs.aemeasurable), Measure.pi_map_pi (fun _ ↦ ht.aemeasurable)]
  simp_rw [(D.refineSubplan_flagged_physical_laws hπ η hη).1,
    (D.refineSubplan_flagged_physical_laws hπ η hη).2]

/-- Literal original coordinate observations and residual flags have an exact
independent law on the same original marked arrays used for residual repair. -/
theorem refineSubplan_flagged_coordinate_iid_law
    {I J Z W : Type*} [Fintype I] [Fintype J] [MeasurableSpace Z] [MeasurableSpace W]
    (hπ : Vlasov.IsCoupling π μ ν) (η : Measure (X × Y)) (hη : η ≤ π)
    (f : X → Z) (g : Y → W) (hf : Measurable f) (hg : Measurable g) :
    let R := D.refineSubplan η hη
    ((Measure.pi (fun _ : I ↦ R.types.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.types.targetMarkedLaw ν))).map
        (Prod.map (fun x i ↦ (f (x i).1, subplanRetentionFlag (x i).2))
          (fun y j ↦ (g (y j).1, subplanRetentionFlag (y j).2))) =
      (Measure.pi (fun _ : I ↦
        (((π - η).map Prod.fst).map f).map (fun z ↦ (z, false)) +
          ((η.map Prod.fst).map f).map (fun z ↦ (z, true)))).prod
      (Measure.pi (fun _ : J ↦
        (((π - η).map Prod.snd).map g).map (fun w ↦ (w, false)) +
          ((η.map Prod.snd).map g).map (fun w ↦ (w, true)))) := by
  have hflagX : Measurable (fun p : X × Option (Bool × T) ↦
      (p.1, subplanRetentionFlag p.2)) :=
    measurable_fst.prodMk ((measurable_of_countable (subplanRetentionFlag (T := T))).comp measurable_snd)
  have hflagY : Measurable (fun p : Y × Option (Bool × T) ↦
      (p.1, subplanRetentionFlag p.2)) :=
    measurable_fst.prodMk ((measurable_of_countable (subplanRetentionFlag (T := T))).comp measurable_snd)
  have hs := congrArg (fun ρ : Measure (X × Bool) ↦ ρ.map (Prod.map f id))
    (D.refineSubplan_flagged_physical_laws hπ η hη).1
  have ht := congrArg (fun ρ : Measure (Y × Bool) ↦ ρ.map (Prod.map g id))
    (D.refineSubplan_flagged_physical_laws hπ η hη).2
  have hmapX (ρ : Measure X) (flag : Bool) :
      (ρ.map (fun x ↦ (x, flag))).map (Prod.map f id) =
        (ρ.map f).map (fun z ↦ (z, flag)) := by
    rw [Measure.map_map (hf.prodMap measurable_id)
      (show Measurable (fun x : X ↦ (x, flag)) from measurable_id.prodMk measurable_const),
      Measure.map_map (show Measurable (fun z : Z ↦ (z, flag)) from
        measurable_id.prodMk measurable_const) hf]
    rfl
  have hmapY (ρ : Measure Y) (flag : Bool) :
      (ρ.map (fun y ↦ (y, flag))).map (Prod.map g id) =
        (ρ.map g).map (fun w ↦ (w, flag)) := by
    rw [Measure.map_map (hg.prodMap measurable_id)
      (show Measurable (fun y : Y ↦ (y, flag)) from measurable_id.prodMk measurable_const),
      Measure.map_map (show Measurable (fun w : W ↦ (w, flag)) from
        measurable_id.prodMk measurable_const) hg]
    rfl
  dsimp only at hs ht ⊢
  rw [Measure.map_map (hf.prodMap measurable_id) hflagX,
    Measure.map_add _ _ (hf.prodMap measurable_id), hmapX, hmapX] at hs
  rw [Measure.map_map (hg.prodMap measurable_id) hflagY,
    Measure.map_add _ _ (hg.prodMap measurable_id), hmapY, hmapY] at ht
  have hxobs : Measurable (fun p : X × Option (Bool × T) ↦
      (f p.1, subplanRetentionFlag p.2)) :=
    (hf.comp measurable_fst).prodMk
      ((measurable_of_countable (subplanRetentionFlag (T := T))).comp measurable_snd)
  have hyobs : Measurable (fun p : Y × Option (Bool × T) ↦
      (g p.1, subplanRetentionFlag p.2)) :=
    (hg.comp measurable_fst).prodMk
      ((measurable_of_countable (subplanRetentionFlag (T := T))).comp measurable_snd)
  have hxs : Measurable (fun x : I → X × Option (Bool × T) ↦
      fun i ↦ (f (x i).1, subplanRetentionFlag (x i).2)) :=
    measurable_pi_lambda _ (fun i ↦ hxobs.comp (measurable_pi_apply i))
  have hys : Measurable (fun y : J → Y × Option (Bool × T) ↦
      fun j ↦ (g (y j).1, subplanRetentionFlag (y j).2)) :=
    measurable_pi_lambda _ (fun j ↦ hyobs.comp (measurable_pi_apply j))
  rw [← Measure.map_prod_map _ _ hxs hys,
    Measure.pi_map_pi (fun _ ↦ hxobs.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ hyobs.aemeasurable)]
  simp only [Function.comp_def, Prod.map_apply, id_eq] at hs ht
  simp_rw [hs, ht]

end PopulationTypedCostData
end OTSelector.Reconstruction
