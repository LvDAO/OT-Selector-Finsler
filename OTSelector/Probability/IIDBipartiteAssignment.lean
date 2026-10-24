import OTSelector.Probability.IIDAssignmentUniqueness
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Unique assignments for the original two-color iid samples

Atomless target sampling gives distinct target tuples almost surely. Conditioning
on that actual tuple in the true product law, atomless source cost differences give
a unique optimal permutation. Independence of the two entire iid arrays identifies
their actual joint pushforward with this product law, so uniqueness holds on the
original probability space. The full fractional optimal face is the same singleton.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

/-- The event that a measurable finite cost matrix has exactly one minimizing
permutation is measurable, without selecting a minimizer. -/
theorem measurableSet_existsUnique_optimalAssignment {n : ℕ} {A : Type*}
    [MeasurableSpace A] (cost : A → Fin n → Fin n → ℝ)
    (hcost : ∀ i j, Measurable (fun a ↦ cost a i j)) :
    MeasurableSet {a | ∃! σ, OptimalAssignment (cost a) σ} := by
  classical
  have hopt (σ : Assignment n) : MeasurableSet {a | OptimalAssignment (cost a) σ} := by
    simp only [OptimalAssignment, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro τ
    apply measurableSet_le <;> unfold assignmentCost
    · exact Finset.measurable_sum _ (fun i _ ↦ hcost i _)
    · exact Finset.measurable_sum _ (fun i _ ↦ hcost i _)
  change MeasurableSet {a | ∃ σ, OptimalAssignment (cost a) σ ∧
    ∀ τ, OptimalAssignment (cost a) τ → τ = σ}
  simp only [Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
  exact MeasurableSet.iUnion (fun σ ↦ (hopt σ).inter
    (MeasurableSet.iInter (fun τ ↦ (hopt τ).imp (MeasurableSet.const (τ = σ)))))

/-- A finite array of independent samples from an atomless law is almost surely injective. -/
theorem ae_injective_pi_of_nullSingletonClass {ι T : Type*} [Fintype ι]
    [MeasurableSpace T] [MeasurableEq T] (ν : Measure T)
    [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ∀ᵐ y ∂Measure.pi (fun _ : ι ↦ ν), Function.Injective y := by
  classical
  have hdiag : ∀ᵐ z ∂ν.prod ν, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
    exact Eventually.of_forall fun x ↦ (ν.ae_ne x).mono fun _ h ↦ h.symm
  have hind : iIndepFun (fun i (y : ι → T) ↦ y i) (Measure.pi (fun _ : ι ↦ ν)) :=
    iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hne (i j : ι) : ∀ᵐ y ∂Measure.pi (fun _ : ι ↦ ν), i ≠ j → y i ≠ y j := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h ↦ (h hij).elim
    · have hmap := (hind.indepFun hij).map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
      rw [(measurePreserving_eval (fun _ : ι ↦ ν) i).map_eq,
        (measurePreserving_eval (fun _ : ι ↦ ν) j).map_eq] at hmap
      have hpair : ∀ᵐ y ∂Measure.pi (fun _ : ι ↦ ν), y i ≠ y j := by
        have hdiag' : ∀ᵐ z ∂(Measure.pi (fun _ : ι ↦ ν)).map (fun y ↦ (y i, y j)),
            z.1 ≠ z.2 := by rwa [hmap]
        exact ae_of_ae_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
          hdiag'
      exact hpair.mono fun _ h _ ↦ h
  filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hne i)] with y hy
  intro i j hij
  by_contra hne
  exact hy i j hne hij

variable {n : ℕ} {S T Ω : Type*}
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableEq T]

/-- Under the actual product of the two iid array laws, almost every bipartite
cost matrix has a unique optimal permutation. Only distinct target pairs require
atomless source cost differences. -/
theorem ae_existsUnique_optimalAssignment_bipartite_product
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ c x y - c x z))) :
    ∀ᵐ q ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ μ)),
      ∃! σ, OptimalAssignment (fun i j ↦ c (q.2 i) (q.1 j)) σ := by
  have hmeas : MeasurableSet {q : (Fin (n + 1) → T) × (Fin (n + 1) → S) |
      ∃! σ, OptimalAssignment (fun i j ↦ c (q.2 i) (q.1 j)) σ} :=
    measurableSet_existsUnique_optimalAssignment _ (fun i j ↦ by
      have hp : Measurable (fun q : (Fin (n + 1) → T) × (Fin (n + 1) → S) ↦
          (q.2 i, q.1 j)) :=
        ((measurable_pi_apply i).comp measurable_snd).prodMk
          ((measurable_pi_apply j).comp measurable_fst)
      exact hc.comp hp)
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1)) ν] with y hy
  exact ae_existsUnique_optimalAssignment_of_iid_atomless
    (Measure.pi (fun _ : Fin (n + 1) ↦ μ)) μ (fun i x ↦ x i)
    (fun i ↦ measurable_pi_apply i)
    (iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id))
    (fun i ↦ (measurePreserving_eval (fun _ : Fin (n + 1) ↦ μ) i).map_eq)
    (fun j x ↦ c x (y j))
    (fun j ↦ hc.comp (measurable_id.prodMk measurable_const))
    (fun j k hjk ↦ hatom (y j) (y k) (hy.ne hjk))

/-- The unique minimizing permutation is an almost-sure property of the original
two-color iid samples, using independence of their entire arrays and their actual laws. -/
theorem ae_existsUnique_optimalAssignment_of_bipartite_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S) (ν : Measure T)
    [NullSingletonClass ν]
    (X : Fin (n + 1) → Ω → S) (Y : Fin (n + 1) → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P)
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ c x y - c x z))) :
    ∀ᵐ ω ∂P, ∃! σ, OptimalAssignment (fun i j ↦ c (X i ω) (Y j ω)) σ := by
  let _instBipartiteSourceProbability : IsProbabilityMeasure μ := by
    rw [← hXlaw 0]
    exact Measure.isProbabilityMeasure_map (hX 0).aemeasurable
  let _instBipartiteTargetProbability : IsProbabilityMeasure ν := by
    rw [← hYlaw 0]
    exact Measure.isProbabilityMeasure_map (hY 0).aemeasurable
  have hmX : Measurable (fun ω i ↦ X i ω) := measurable_pi_lambda _ hX
  have hmY : Measurable (fun ω j ↦ Y j ω) := measurable_pi_lambda _ hY
  have hlX : P.map (fun ω i ↦ X i ω) = Measure.pi (fun _ : Fin (n + 1) ↦ μ) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX i).aemeasurable) hXi]
    simp_rw [hXlaw]
  have hlY : P.map (fun ω j ↦ Y j ω) = Measure.pi (fun _ : Fin (n + 1) ↦ ν) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun j ↦ (hY j).aemeasurable) hYi]
    simp_rw [hYlaw]
  have hpair := hXY.symm.map_prod_eq_prod_map_map hmY.aemeasurable hmX.aemeasurable
  rw [hlY, hlX] at hpair
  have hp := ae_existsUnique_optimalAssignment_bipartite_product μ ν c hc hatom (n := n)
  rw [← hpair] at hp
  exact ae_of_ae_map (hmY.prodMk hmX).aemeasurable hp

/-- The full doubly stochastic optimal face of the actual two-color iid cost
matrix is almost surely a singleton. -/
theorem ae_existsUnique_optimalFractionalAssignment_of_bipartite_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S) (ν : Measure T)
    [NullSingletonClass ν]
    (X : Fin (n + 1) → Ω → S) (Y : Fin (n + 1) → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P)
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ c x y - c x z))) :
    ∀ᵐ ω ∂P, ∃! A, OptimalFractionalAssignment (fun i j ↦ c (X i ω) (Y j ω)) A := by
  filter_upwards [ae_existsUnique_optimalAssignment_of_bipartite_iid_atomless
    P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY c hc hatom] with ω hω
  exact existsUnique_optimalFractionalAssignment_of_existsUnique_optimalAssignment _ hω

/-- Almost surely, every fractional optimum is exactly the permutation matrix of
the unique original assignment, and that matrix is itself optimal. -/
theorem ae_optimalFractionalAssignment_iff_permMatrix_of_bipartite_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S) (ν : Measure T)
    [NullSingletonClass ν]
    (X : Fin (n + 1) → Ω → S) (Y : Fin (n + 1) → Ω → T)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : iIndepFun X P) (hYi : iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P)
    (c : S → T → ℝ) (hc : Measurable (Function.uncurry c))
    (hatom : ∀ y z, y ≠ z →
      NullSingletonClass (μ.map (fun x ↦ c x y - c x z))) :
    ∀ᵐ ω ∂P, ∃ σ, OptimalAssignment (fun i j ↦ c (X i ω) (Y j ω)) σ ∧
      (∀ τ, OptimalAssignment (fun i j ↦ c (X i ω) (Y j ω)) τ → τ = σ) ∧
      ∀ A, OptimalFractionalAssignment (fun i j ↦ c (X i ω) (Y j ω)) A ↔
        A = σ.permMatrix ℝ := by
  filter_upwards [ae_existsUnique_optimalAssignment_of_bipartite_iid_atomless
    P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY c hc hatom] with ω hω
  obtain ⟨σ, hσ, huniq⟩ := hω
  refine ⟨σ, hσ, huniq, fun A ↦ ⟨?_, ?_⟩⟩
  · exact optimalFractionalAssignment_eq_permMatrix_of_unique _ A σ huniq
  · intro hA
    subst A
    refine ⟨permMatrix_mem_doublyStochastic, fun B hB ↦ ?_⟩
    rw [fractionalAssignmentCost_permMatrix]
    exact assignmentCost_le_fractionalAssignmentCost _ B σ hσ hB

end OTSelector.Probability
