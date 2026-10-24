import OTSelector.Reconstruction.MarkedStationaryValueLegalInputSimpleCarrier
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowLocalLaw
import OTSelector.Probability.IIDBipartiteAssignment

/-!
# Simplicity comes from the original independent Poisson inputs

Positive-dimensional Haar point laws have no atoms. The original finite
Poisson prefixes therefore have injective point arrays almost surely; the
immutable color tags distinguish opposite colors even when clocks overlap.
Their literal colored measures and every restriction have unit atoms.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

local instance markedStationaryValueLegalInputFiniteSimplicityColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- Distinct original finite labels have one occupied unit atom each. -/
theorem isLegalSimpleCountingMeasure_of_injective_fintype
    {X ι : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [Fintype ι]
    (base : X) (f : ι → X) (hf : Injective f) :
    IsLegalSimpleCountingMeasure base ⟨∑ i, Measure.dirac (f i), inferInstance⟩ := by
  let e := (Fintype.equivFin ι).symm
  have h := isLegalSimpleCountingMeasure_of_injective_tuple base (fun k ↦ f (e k))
    (hf.comp e.injective)
  have heq : (⟨∑ k, Measure.dirac (f (e k)), inferInstance⟩ : LocalFiniteMeasure X) =
      ⟨∑ i, Measure.dirac (f i), inferInstance⟩ := by
    apply Subtype.ext
    exact e.sum_comp (fun i ↦ Measure.dirac (f i))
  rwa [heq] at h

/-- No equal-clock assumption is needed: finite source and target colors
are distinguished by their original immutable finite tag. -/
theorem isLegalSimpleCountingMeasure_legalInputTwoBlockLocal
    (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hs : Injective b.1.2) (ht : Injective b.2.2) :
    IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) (legalInputTwoBlockLocal q b) := by
  let f : Fin b.1.1 ⊕ Fin b.2.1 → LegalColoredInputPoint q :=
    Sum.elim (fun i ↦ (b.1.2 i, (0 : Fin 2))) (fun i ↦ (b.2.2 i, (1 : Fin 2)))
  have hf : Injective f := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hs (congrArg Prod.fst hij))
      | inr j => have h := congrArg Prod.snd hij; norm_num [f] at h
    | inr i =>
      cases j with
      | inl j => have h := congrArg Prod.snd hij; norm_num [f] at h
      | inr j => exact congrArg Sum.inr (ht (congrArg Prod.fst hij))
  have h := isLegalSimpleCountingMeasure_of_injective_fintype (0 : LegalColoredInputPoint q) f hf
  have heq : (⟨∑ i, Measure.dirac (f i), inferInstance⟩ : LocalFiniteMeasure (LegalColoredInputPoint q)) =
      legalInputTwoBlockLocal q b := by
    apply Subtype.ext
    change (∑ i, Measure.dirac (f i)) = legalInputTwoBlockMeasure q b
    rw [Fintype.sum_sum_type]
    rfl
  rwa [heq] at h

private theorem measurableSet_legalBlockData_injective
    {X : Type*} [MeasurableSpace X] [MeasurableEq X] :
    MeasurableSet {b : BlockData X | Injective b.2} := by
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet {f : Fin n → X | Injective f}
  simp only [Function.Injective, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).imp
      (MeasurableSet.const (i = j))

/-- Every original Poissonized finite iid tuple from an atomless law is
injective, before any selected matching is formed. -/
theorem ae_injective_legalBlockDataLaw {X : Type*} [MeasurableSpace X] [MeasurableEq X]
    (ν : Measure X) [IsProbabilityMeasure ν] [NullSingletonClass ν] (w : ℕ → ℝ≥0∞) :
    ∀ᵐ b ∂blockDataLaw ν w, Injective b.2 := by
  rw [blockDataLaw, Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  exact (ae_map_iff (measurable_sigma_mk n).aemeasurable measurableSet_legalBlockData_injective).mpr
    (ae_injective_pi_of_nullSingletonClass (ι := Fin n) ν)

/-- The actual physical cube Poisson inputs have injective arrays in positive
transverse dimension, with no atomlessness assumption on the scalar clocks. -/
theorem ae_injective_legalInputPoissonWindowLaw (q : ℕ) (hq : 0 < q)
    {S : ℝ} (hS : 0 < S)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    ∀ᵐ b ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β,
      Injective b.1.2 ∧ Injective b.2.2 := by
  letI : NeZero q := ⟨hq.ne'⟩
  let μ := (volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S)
  have hμfin : μ univ < ∞ := by
    change ((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S)) univ < ∞
    rw [Measure.restrict_apply_univ, volume_haarRootCube (Fin q) hS.le]
    exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure μ := ⟨hμfin⟩
  have hμ0 : μ univ ≠ 0 := by
    change ((volume : Measure (Fin q → ℝ)).restrict (haarRootCube (Fin q) S)) univ ≠ 0
    rw [Measure.restrict_apply_univ, volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  let ν := normalizedFiniteLaw μ
  haveI : IsProbabilityMeasure ν := normalizedFiniteLaw_probability μ
    (ENNReal.toReal_pos hμ0 hμfin.ne)
  haveI : NullSingletonClass μ := by dsimp only [μ]; infer_instance
  haveI : NullSingletonClass ν := by
    constructor
    intro x
    change (((μ.real univ)⁻¹.toNNReal : ℝ≥0) • μ) {x} = 0
    rw [Measure.smul_apply, measure_singleton, smul_zero]
  have hsf (γ : Measure ℝ) [IsProbabilityMeasure γ] :
      SFinite (blockDataLaw (ν.prod γ)
        (fun n ↦ poissonMeasure (volume (haarRootCube (Fin q) S)).toNNReal {n})) := by
    unfold blockDataLaw
    haveI (n : ℕ) : IsFiniteMeasure
        ((poissonMeasure (volume (haarRootCube (Fin q) S)).toNNReal {n}) •
          (Measure.pi (fun _ : Fin n ↦ ν.prod γ)).map
            (fun y ↦ (⟨n, y⟩ : BlockData (LegalMarkedPhysicalPoint q)))) :=
      Measure.smul_finite _ (measure_ne_top _ _)
    infer_instance
  haveI := hsf α
  haveI := hsf β
  change ∀ᵐ b ∂(blockDataLaw (ν.prod α) (fun n ↦ poissonMeasure (volume (haarRootCube (Fin q) S)).toNNReal {n})).prod
      (blockDataLaw (ν.prod β) (fun n ↦ poissonMeasure (volume (haarRootCube (Fin q) S)).toNNReal {n})), _
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_legalBlockData_injective.preimage measurable_fst).inter
      (measurableSet_legalBlockData_injective.preimage measurable_snd))).mpr
  filter_upwards [ae_injective_legalBlockDataLaw (ν.prod α) _] with bs hs
  exact (ae_injective_legalBlockDataLaw (ν.prod β) _).mono fun bt ht ↦ ⟨hs, ht⟩

/-- Original finite Poisson unit atoms remain simple in every literal marked
window restriction. No properties of an adaptively retained cloud are used. -/
theorem ae_isLegalSimpleCountingMeasure_originalPoisson_restriction
    (q : ℕ) (hq : 0 < q) {S : ℝ} (hS : 0 < S)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (U : Set (LegalColoredInputPoint q)) :
    ∀ᵐ b ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β,
      IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
        (legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)) := by
  filter_upwards [ae_injective_legalInputPoissonWindowLaw q hq hS α β] with b hb
  exact isLegalSimpleCountingMeasure_restrict _ _
    (isLegalSimpleCountingMeasure_legalInputTwoBlockLocal q b hb.1 hb.2) U

end OTSelector.Reconstruction
