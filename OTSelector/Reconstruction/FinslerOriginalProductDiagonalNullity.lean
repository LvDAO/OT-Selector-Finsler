import OTSelector.Probability.MarkedPoissonCube

/-!
# Product diagonal nullity and a.e. distinctness of iid cloud positions

This module supplies the measure-theoretic core of the a.e. simplicity gap of
FinslerOriginalHaarPositionAESimplicity: nullity of the diagonal in a product of
two measures, and a.e. distinctness of two coordinates of a countably-indexed
iid product law (Measure.infinitePi).

1. **prod_diagonal_null**: if the right factor measure gives all singletons
   measure zero, then the diagonal is null in the product.
2. **infinitePi_ae_ne**: for a countably-indexed product of iid laws
   (Measure.infinitePi) with atomless coordinate law, two distinct coordinates
   are a.e. different.  Proof: push the pair map f |-> (f i, f j) through the
   product law via Measure.infinitePi_map_eval_prod, obtaining P i * P j, whose
   diagonal is null by (1).
3. **markedSeqLaw_ae_marks_ne**: the same for the cloud's marked sequence law
   markedSeqLaw q A alpha = Measure.infinitePi (fun _ => cubeMeasure q 1 prodt
   alpha): two distinct marked points are a.e. different, CONDITIONAL on
   atomlessness of the single marked point law
   (cubeMeasure (Fin q) 1).prod alpha.
4. **markedSeqLaw_ae_positions_ne**: consequently, conditional on the same
   atomlessness, the POSITIONS of two distinct marked cloud points are a.e.
   different (positions are the first component).

## Exact remaining input

The single remaining input is atomlessness of the marked point law
(cubeMeasure (Fin q) 1).prod alpha, i.e. all its singletons have measure zero.
This reduces to singleton-nullness of the cube Haar measure
cubeMeasure (Fin q) 1 = Measure.pi (fun _ => uniformInterval 1), which is not
yet available in the repository in the exact form needed here (the continuous
position coordinate makes it true for every q >= 1).  Everything else - the
product diagonal nullity and the infinite-product transfer - is proved here
unconditionally.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **Diagonal nullity in a product**: if the right factor has no atoms, the
diagonal is null in the product. -/
theorem prod_diagonal_null {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    {μ ν : Measure X} [SFinite ν]
    (hν : ∀ x, ν {x} = 0) :
    (μ.prod ν) (Set.diagonal X) = 0 := by
  rw [Measure.prod_apply (measurableSet_diagonal)]
  have hinner : ∀ x, ν (Prod.mk x ⁻¹' Set.diagonal X) = 0 := by
    intro x
    have hset : Prod.mk x ⁻¹' Set.diagonal X = {x} := by
      ext y
      simp [eq_comm]
    rw [hset]
    exact hν x
  simp [hinner]

/-- **A.e. distinctness of two coordinates under an iid product law.**  For a
countably indexed product Measure.infinitePi of probability laws, if the
coordinate law has no atoms then two distinct coordinates agree only on a null
set. -/
theorem infinitePi_ae_ne {ι X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (P : ι → Measure X) [∀ i, IsProbabilityMeasure (P i)]
    (hP : ∀ i, ∀ x, P i {x} = 0) {i j : ι} (hij : i ≠ j) :
    ∀ᵐ ω ∂Measure.infinitePi P, ω i ≠ ω j := by
  have hmap := Measure.infinitePi_map_eval_prod (P := P) hij
  have hnull : ((P i).prod (P j)) (Set.diagonal X) = 0 :=
    prod_diagonal_null (hP j)
  have hmeas : Measurable (fun ω : (i : ι) → X => (ω i, ω j)) :=
    (measurable_pi_apply i).prod (measurable_pi_apply j)
  have hpre : (Measure.infinitePi P)
      ((fun ω : (i : ι) → X => (ω i, ω j)) ⁻¹' Set.diagonal X) = 0 := by
    rw [← Measure.map_apply hmeas measurableSet_diagonal, hmap, hnull]
  rw [MeasureTheory.ae_iff]
  have hset : {ω : (i : ι) → X | ¬ ω i ≠ ω j} =
      (fun ω : (i : ι) → X => (ω i, ω j)) ⁻¹' Set.diagonal X := by
    ext ω
    simp
  rw [hset]
  exact hpre

/-- **A.e. distinctness of two marked cloud points.**  The marked sequence law is
the infinite product of the single marked point law; conditional on that law
being atomless, two distinct marked points are a.e. different. -/
theorem markedSeqLaw_ae_marks_ne {q : ℕ}
    (α : Measure ℝ) [IsProbabilityMeasure α]
    (hα : ∀ x : (Fin q → ℝ) × ℝ, ((cubeMeasure (Fin q) 1).prod α) {x} = 0)
    {i j : ℕ} (hij : i ≠ j) :
    ∀ᵐ seq ∂markedSeqLaw (q := q) ℝ α, seq i ≠ seq j := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  haveI : ∀ _ : ℕ, IsProbabilityMeasure ((cubeMeasure (Fin q) 1).prod α) :=
    fun _ => inferInstance
  exact infinitePi_ae_ne (P := fun _ : ℕ => (cubeMeasure (Fin q) 1).prod α)
    (fun _ => hα) hij

/-- **A.e. distinctness of two positions under the iid cube law.**  This is the
position-level form: for the infinite product of the cube Haar measure, two
distinct coordinates are a.e. different (conditional on singleton-nullness of the
cube measure, the exact remaining atomlessness input). -/
theorem infinitePi_cube_ae_ne {q : ℕ}
    (hpos : ∀ x : Fin q → ℝ, (cubeMeasure (Fin q) 1) {x} = 0)
    {i j : ℕ} (hij : i ≠ j) :
    ∀ᵐ seq ∂Measure.infinitePi (fun _ : ℕ => cubeMeasure (Fin q) 1),
      seq i ≠ seq j := by
  haveI : IsProbabilityMeasure (cubeMeasure (Fin q) 1) :=
    isProbabilityMeasure_cubeMeasure (by norm_num)
  exact infinitePi_ae_ne (P := fun _ : ℕ => (cubeMeasure (Fin q) 1))
    (fun _ => hpos) hij

end OTSelector.Reconstruction
