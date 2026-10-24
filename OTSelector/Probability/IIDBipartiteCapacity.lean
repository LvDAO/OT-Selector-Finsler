import OTSelector.Probability.IIDCapacityAssignmentUniqueness
import OTSelector.Probability.IIDBipartiteAssignment
import OTSelector.Finite.CapacityRestriction

/-!
# Simultaneous capacity uniqueness for the original two iid colors

Conditioning on the actual target tuple gives distinct target labels almost
surely. Independence identifies the law of the two original arrays with their
product law. Distinct allocation costs, and hence quota uniqueness on every
actual retained subset, transfer back to the original probability space.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace OTSelector.Probability

variable {ι α S T Ω : Type*} [Fintype ι] [Fintype α]

/-- Distinct costs of all finite label allocations form a measurable event. -/
theorem measurableSet_injective_capacityAssignmentCost
    {A : Type*} [MeasurableSpace A] (cost : A → ι → α → ℝ)
    (hcost : ∀ i j, Measurable (fun a ↦ cost a i j)) :
    MeasurableSet {a | Function.Injective (capacityAssignmentCost (cost a))} := by
  classical
  have hm (b : ι → α) : Measurable (fun a ↦ capacityAssignmentCost (cost a) b) :=
    Finset.measurable_sum _ fun i _ ↦ hcost i (b i)
  change MeasurableSet {a | ∀ b c, capacityAssignmentCost (cost a) b =
    capacityAssignmentCost (cost a) c → b = c}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun b ↦ MeasurableSet.iInter fun c ↦
    (measurableSet_eq_fun (hm b) (hm c)).imp (MeasurableSet.const (b = c))

variable [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableEq T]

/-- Almost every actual pair of source and target arrays has distinct costs for
all label allocations; source and target counts may differ. -/
theorem ae_injective_capacityAssignmentCost_bipartite_product
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ c x y - c x z))) :
    ∀ᵐ q ∂(Measure.pi (fun _ : α ↦ ν)).prod (Measure.pi (fun _ : ι ↦ μ)),
      Function.Injective (capacityAssignmentCost (fun i j ↦ c (q.2 i) (q.1 j))) := by
  have hm : MeasurableSet {q : (α → T) × (ι → S) |
      Function.Injective (capacityAssignmentCost (fun i j ↦ c (q.2 i) (q.1 j)))} :=
    measurableSet_injective_capacityAssignmentCost _ fun i j ↦ by
      have hp : Measurable (fun q : (α → T) × (ι → S) ↦ (q.2 i, q.1 j)) :=
        ((measurable_pi_apply i).comp measurable_snd).prodMk
          ((measurable_pi_apply j).comp measurable_fst)
      exact hc.comp hp
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := α) ν] with y hy
  exact ae_injective_capacityAssignmentCost_of_iid_atomless
    (Measure.pi (fun _ : ι ↦ μ)) μ (fun i x ↦ x i)
    (fun i ↦ measurable_pi_apply i)
    (iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id))
    (fun i ↦ (measurePreserving_eval (fun _ : ι ↦ μ) i).map_eq)
    (fun j x ↦ c x (y j))
    (fun j ↦ hc.comp (measurable_id.prodMk measurable_const))
    (fun j k hjk ↦ hatom (y j) (y k) (hy.ne hjk))

/-- The full-array cost injectivity event belongs to the original two-color
probability space and is simultaneous over all allocations. -/
theorem ae_injective_capacityAssignmentCost_of_bipartite_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (X : ι → Ω → S) (Y : α → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P)
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ c x y - c x z))) :
    ∀ᵐ ω ∂P, Function.Injective (capacityAssignmentCost (fun i j ↦ c (X i ω) (Y j ω))) := by
  have hmX : Measurable (fun ω i ↦ X i ω) := measurable_pi_lambda _ hX
  have hmY : Measurable (fun ω j ↦ Y j ω) := measurable_pi_lambda _ hY
  have hlX : P.map (fun ω i ↦ X i ω) = Measure.pi (fun _ : ι ↦ μ) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable) hXi]
    simp_rw [hXlaw]
  have hlY : P.map (fun ω j ↦ Y j ω) = Measure.pi (fun _ : α ↦ ν) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun j ↦ (hY j).aemeasurable) hYi]
    simp_rw [hYlaw]
  have hpair := hXY.symm.map_prod_eq_prod_map_map hmY.aemeasurable hmX.aemeasurable
  rw [hlY, hlX] at hpair
  have hp := ae_injective_capacityAssignmentCost_bipartite_product
    (ι := ι) (α := α) μ ν c hc hatom
  rw [← hpair] at hp
  exact ae_of_ae_map (hmY.prodMk hmX).aemeasurable hp

/-- One original full-probability event gives cost uniqueness on every retained
source subset, even when the subset is selected using the sampled costs. -/
theorem ae_injective_retained_capacityAssignmentCost_of_bipartite_iid_atomless
    [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (X : ι → Ω → S) (Y : α → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P)
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ c x y - c x z))) :
    ∀ᵐ ω ∂P, ∀ s : Finset ι, Function.Injective
      (capacityAssignmentCost (fun (i : s) j ↦ c (X i ω) (Y j ω))) := by
  filter_upwards [ae_injective_capacityAssignmentCost_of_bipartite_iid_atomless
    P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY c hc hatom] with ω hω
  intro s
  have h := injective_capacityAssignmentCost_subtype _ hω (fun i ↦ i ∈ s)
  have hinst : Subtype.fintype (fun i ↦ i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hinst] at h
  exact h

end OTSelector.Probability
