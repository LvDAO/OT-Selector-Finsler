import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell
import OTSelector.Probability.BlockDataTransport

/-! Exact fixed-sample extraction of the original retained cell observations.
The selected original indices keep their increasing order, the count is the
literal binomial count, and observations have the original normalized law. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The original finite observations in a prescribed measurable point event,
in their original increasing-index order. -/
def finiteOriginalRestrictedData {X : Type*} {N : ℕ} (S : Set X) (x : Fin N → X) : BlockData X :=
  blockDataOfPairsGen true (fun i ↦ (restrictionLabel S (x i), x i))

/-- The literal original indices used by the extracted finite observations. -/
def finiteOriginalRestrictedEmbedding {X : Type*} {N : ℕ} (S : Set X) (x : Fin N → X) :
    Fin (finiteOriginalRestrictedData S x).1 ↪ Fin N := by
  classical
  let s := Finset.univ.filter (fun i : Fin N ↦ restrictionLabel S (x i) = true)
  exact ⟨fun j ↦ (s.orderIsoOfFin rfl j).1, fun i j hij ↦
    (s.orderIsoOfFin rfl).injective (Subtype.ext hij)⟩

/-- No original selected observation is omitted, and none outside the event is
added. This identity does not condition on a matching or on unused partners. -/
theorem finiteOriginalRestrictedEmbedding_range {X : Type*} {N : ℕ}
    (S : Set X) (x : Fin N → X) (i : Fin N) :
    i ∈ range (finiteOriginalRestrictedEmbedding S x) ↔ x i ∈ S := by
  classical
  let s := Finset.univ.filter (fun i : Fin N ↦ restrictionLabel S (x i) = true)
  constructor
  · rintro ⟨j, rfl⟩
    change x ((s.orderIsoOfFin rfl j).1) ∈ S
    have hm : restrictionLabel S (x ((s.orderIsoOfFin rfl j).1)) = true :=
      (Finset.mem_filter.mp (s.orderIsoOfFin rfl j).2).2
    by_cases hx : x ((s.orderIsoOfFin rfl j).1) ∈ S
    · exact hx
    · have hfalse : restrictionLabel S (x ((s.orderIsoOfFin rfl j).1)) = false := by
        rw [restrictionLabel, ite_eq_right hx]
      exact False.elim (by cases hfalse.symm.trans hm)
  · intro hi
    have his : i ∈ s := by simp [s, restrictionLabel, hi]
    refine ⟨(s.orderIsoOfFin rfl).symm ⟨i, his⟩, ?_⟩
    change ((s.orderIsoOfFin rfl) ((s.orderIsoOfFin rfl).symm ⟨i, his⟩)).1 = i
    rw [OrderIso.apply_symm_apply]

/-- The extracted data reads the same original point at its original index. -/
theorem finiteOriginalRestrictedData_point {X : Type*} {N : ℕ}
    (S : Set X) (x : Fin N → X) (i : Fin (finiteOriginalRestrictedData S x).1) :
    (finiteOriginalRestrictedData S x).2 i = x (finiteOriginalRestrictedEmbedding S x i) := rfl

/-- Original finite event extraction is measurable. -/
theorem measurable_finiteOriginalRestrictedData {X : Type*} [MeasurableSpace X] {N : ℕ}
    {S : Set X} (hS : MeasurableSet S) : Measurable (finiteOriginalRestrictedData (N := N) S) := by
  exact (measurable_blockDataOfPairsGen true).comp
    (measurable_pi_lambda _ fun i ↦
      ((measurable_restrictionLabel hS).comp (measurable_pi_apply i)).prodMk (measurable_pi_apply i))

/-- Under the original fixed iid sample, the count is exactly binomial and the
ordered selected points have exactly the original normalized event law. -/
theorem finiteOriginalRestrictedData_law {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ) {S : Set X} (hS : MeasurableSet S) :
    (Measure.pi (fun _ : Fin N ↦ ν)).map (finiteOriginalRestrictedData S) =
      blockDataLaw (restrictedPointLaw ν S) (binomWeight N (restrictionWeight ν S)) := by
  let pairMap : X → Bool × X := fun x ↦ (restrictionLabel S x, x)
  have hpair : Measurable pairMap := (measurable_restrictionLabel hS).prodMk measurable_id
  have hjoint (i : Fin N) : (Measure.pi (fun _ : Fin N ↦ ν)).map
      (fun x ↦ (restrictionLabel S (x i), x i)) =
      mixturePointLaw (fun b ↦ restrictionWeight ν (restrictionPart S b))
        (fun b ↦ restrictedPointLaw ν (restrictionPart S b)) := by
    rw [show (fun x : Fin N → X ↦ (restrictionLabel S (x i), x i)) = pairMap ∘ (fun x ↦ x i) from rfl,
      ← Measure.map_map hpair (measurable_pi_apply i), (measurePreserving_eval (fun _ : Fin N ↦ ν) i).map_eq]
    exact map_restrictionLabel_pair ν hS
  have h := map_blockDataOfPairsGen_law
    (P := Measure.pi (fun _ : Fin N ↦ ν))
    (fun i x ↦ restrictionLabel S (x i)) (fun i x ↦ x i)
    (fun i ↦ (measurable_restrictionLabel hS).comp (measurable_pi_apply i))
    (fun i ↦ measurable_pi_apply i)
    (iIndepFun_pi (X := fun _ : Fin N ↦ pairMap) (fun _ ↦ hpair.aemeasurable))
    (fun b ↦ restrictionWeight ν (restrictionPart S b)) (sum_restrictionWeight ν hS)
    (fun b ↦ restrictedPointLaw ν (restrictionPart S b)) hjoint true
  unfold finiteOriginalRestrictedData
  simpa only [restrictionPart, ↓reduceIte] using h

/-- Observing the exact selected original prefix changes only its literal
conditional point law and preserves the original binomial count distribution.
This version includes null events, whose unused fallback law is harmless. -/
theorem finiteOriginalRestrictedData_map_law
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ) {S : Set X}
    (hS : MeasurableSet S) (f : X → Y) (hf : Measurable f) :
    let _inst : IsProbabilityMeasure ((restrictedPointLaw ν S).map f) :=
      Measure.isProbabilityMeasure_map hf.aemeasurable
    (Measure.pi (fun _ : Fin N ↦ ν)).map
      (fun x ↦ mapBlockData f (finiteOriginalRestrictedData S x)) =
      blockDataLaw ((restrictedPointLaw ν S).map f) (binomWeight N (restrictionWeight ν S)) := by
  let _inst : IsProbabilityMeasure ((restrictedPointLaw ν S).map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  dsimp only
  rw [show (fun x : Fin N → X ↦ mapBlockData f (finiteOriginalRestrictedData S x)) =
    mapBlockData f ∘ finiteOriginalRestrictedData S from rfl,
    ← Measure.map_map (measurable_mapBlockData hf) (measurable_finiteOriginalRestrictedData hS),
    finiteOriginalRestrictedData_law ν N hS]
  exact blockDataLaw_mapPoints _ _ hf rfl _

/-- A positive literal original event law gives the exact observed iid point
law. The original count remains binomial, with the unchanged original mass. -/
theorem finiteOriginalRestrictedData_observed_law
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℕ) {S : Set X}
    (hS : MeasurableSet S) (hpositive : ν S ≠ 0)
    (f : X → Y) (hf : Measurable f) (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (hlaw : (ν.restrict S).map f = ν S • ρ) :
    (Measure.pi (fun _ : Fin N ↦ ν)).map
      (fun x ↦ mapBlockData f (finiteOriginalRestrictedData S x)) =
      blockDataLaw ρ (binomWeight N (restrictionWeight ν S)) := by
  have hpoint : (restrictedPointLaw ν S).map f = ρ := by
    unfold restrictedPointLaw
    rw [ite_eq_right hpositive, ProbabilityTheory.cond, Measure.map_smul, hlaw, smul_smul,
      ENNReal.inv_mul_cancel hpositive (measure_ne_top ν S), one_smul]
  rw [show (fun x : Fin N → X ↦ mapBlockData f (finiteOriginalRestrictedData S x)) =
    mapBlockData f ∘ finiteOriginalRestrictedData S from rfl,
    ← Measure.map_map (measurable_mapBlockData hf) (measurable_finiteOriginalRestrictedData hS),
    finiteOriginalRestrictedData_law ν N hS]
  exact blockDataLaw_mapPoints _ _ hf hpoint _

end OTSelector.Reconstruction
