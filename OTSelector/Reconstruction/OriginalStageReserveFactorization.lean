import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Probability.InfiniteProductLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact original Poisson count/mark/position factorization, preserving original indices. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Probability

/-- Splitting every original iid pair into its two infinite coordinate sequences gives
exactly the product of the two original iid sequence laws. -/
theorem map_split_original_infinitePairLaw
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (σ : Measure X) [IsProbabilityMeasure σ] (α : Measure Y) [IsProbabilityMeasure α] :
    (Measure.infinitePi (fun _ : ℕ ↦ σ.prod α)).map
      (fun z ↦ ((fun i ↦ (z i).1), (fun i ↦ (z i).2))) =
      (Measure.infinitePi (fun _ : ℕ ↦ σ)).prod (Measure.infinitePi (fun _ : ℕ ↦ α)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow X Y ℕ
  have hzip : ((Measure.infinitePi (fun _ : ℕ ↦ σ)).prod
      (Measure.infinitePi (fun _ : ℕ ↦ α))).map e.symm =
      Measure.infinitePi (fun _ : ℕ ↦ σ.prod α) := by
    apply Measure.eq_infinitePi
    intro s t ht
    let F : ((ℕ → X) × (ℕ → Y)) → ((s → X) × (s → Y)) :=
      fun p ↦ (fun i ↦ p.1 i, fun i ↦ p.2 i)
    have hF : Measurable F := by fun_prop
    have hresX : (Measure.infinitePi (fun _ : ℕ ↦ σ)).map (fun z ↦ fun i : s ↦ z i) =
        Measure.pi (fun _ : s ↦ σ) := by
      have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ σ)
        (f := fun i : s ↦ (i : ℕ)) Subtype.val_injective
      simpa only [Measure.infinitePi_eq_pi] using h
    have hresY : (Measure.infinitePi (fun _ : ℕ ↦ α)).map (fun z ↦ fun i : s ↦ z i) =
        Measure.pi (fun _ : s ↦ α) := by
      have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ α)
        (f := fun i : s ↦ (i : ℕ)) Subtype.val_injective
      simpa only [Measure.infinitePi_eq_pi] using h
    have hFlaw : ((Measure.infinitePi (fun _ : ℕ ↦ σ)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ α))).map F =
        (Measure.pi (fun _ : s ↦ σ)).prod (Measure.pi (fun _ : s ↦ α)) := by
      rw [show F = Prod.map (fun z ↦ fun i : s ↦ z i) (fun z ↦ fun i : s ↦ z i) from rfl,
        ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hresX, hresY]
    let es := MeasurableEquiv.arrowProdEquivProdArrow X Y s
    have hsplit := (measurePreserving_arrowProdEquivProdArrow X Y s (fun _ ↦ σ) (fun _ ↦ α)).map_eq
    have hfinite : ((Measure.pi (fun _ : s ↦ σ)).prod (Measure.pi (fun _ : s ↦ α))).map es.symm =
        Measure.pi (fun _ : s ↦ σ.prod α) := by
      conv_lhs => rw [← hsplit]
      rw [Measure.map_map es.symm.measurable es.measurable]
      simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
    have hprojection : ((Measure.infinitePi (fun _ : ℕ ↦ σ)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ α))).map
        (fun p ↦ fun i : s ↦ (p.1 i, p.2 i)) = Measure.pi (fun _ : s ↦ σ.prod α) := by
      change ((Measure.infinitePi (fun _ : ℕ ↦ σ)).prod
        (Measure.infinitePi (fun _ : ℕ ↦ α))).map (es.symm ∘ F) = _
      rw [← Measure.map_map es.symm.measurable hF, hFlaw, hfinite]
    have hV : MeasurableSet (Set.pi univ (fun i : s ↦ t i)) :=
      MeasurableSet.pi (Set.to_countable _) (fun i _ ↦ ht i)
    have hpre : e.symm ⁻¹' Set.pi s t =
        (fun p : (ℕ → X) × (ℕ → Y) ↦ fun i : s ↦ (p.1 i, p.2 i)) ⁻¹'
          Set.pi univ (fun i : s ↦ t i) := by
      ext p
      simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, e,
        MeasurableEquiv.arrowProdEquivProdArrow]
      exact ⟨fun h i ↦ h i i.2, fun h i hi ↦ h ⟨i, hi⟩⟩
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.pi s.countable_toSet (fun i _ ↦ ht i)),
      hpre, ← Measure.map_apply (by fun_prop) hV, hprojection, Measure.pi_pi]
    exact Finset.prod_coe_sort s (fun i ↦ (σ.prod α) (t i))
  have hmap : (Measure.infinitePi (fun _ : ℕ ↦ σ.prod α)).map e =
      (Measure.infinitePi (fun _ : ℕ ↦ σ)).prod (Measure.infinitePi (fun _ : ℕ ↦ α)) := by
    rw [← hzip, Measure.map_map e.measurable e.symm.measurable]
    simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]
  exact hmap

end OTSelector.Probability
