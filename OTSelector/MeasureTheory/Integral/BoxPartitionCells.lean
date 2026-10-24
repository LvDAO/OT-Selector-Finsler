import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalCubeTraceCompactnessCells.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalCubeTraceCompactnessCells`; the selected original proof blocks follow. -/
section

/-!
Conditions: A finite dyadic prepartition of the unit box and the stated continuity or integrability of the readouts.

Objects: Explicit face cells, finite-dimensional step-function readouts and exact additive integral identities, including collars.

Proof detail: Use dyadic box disjointness and almost-everywhere coverage, sum cell indicators and apply finite additivity/Fubini.

Sources: D. H. Fremlin, Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Explicit finite-dimensional approximation encoding; a full compactness theorem is not assumed in these cell identities.
-/

/-! Actual finite dyadic face cells and their finite-dimensional step readouts. -/
open Set Function Filter MeasureTheory BoxIntegral
open scoped ENNReal Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction

variable {ι : Type*} [Fintype ι]

/-- The original unit face box with its actual half-open measurable carrier. -/
def originalUnitFaceBox (ι : Type*) : Box ι where
  lower := fun _ ↦ 0
  upper := fun _ ↦ 1
  lower_lt_upper := fun _ ↦ zero_lt_one

/-- The actual dyadic face partition reuses Mathlib's disjoint center splits. -/
def originalDyadicFacePartition (n : ℕ) : Prepartition (originalUnitFaceBox ι) :=
  match n with
  | 0 => ⊤
  | n + 1 => (originalDyadicFacePartition n).biUnion Prepartition.splitCenter

/-- Each actual dyadic family partitions the same original unit face. -/
theorem isPartition_originalDyadicFacePartition (n : ℕ) :
    (originalDyadicFacePartition (ι := ι) n).IsPartition := by
  induction n with
  | zero => exact Prepartition.isPartitionTop _
  | succ n ih =>
    exact ih.biUnion (fun J _ ↦ Prepartition.isPartition_splitCenter J)

/-- Every actual cell has the same true dyadic side length. -/
theorem originalDyadicFacePartition_side {n : ℕ} {J : Box ι}
    (hJ : J ∈ originalDyadicFacePartition (ι := ι) n) (i : ι) :
    J.upper i - J.lower i = (1 : ℝ) / 2 ^ n := by
  induction n generalizing J with
  | zero =>
    have h : J = originalUnitFaceBox ι := Prepartition.mem_top.1 hJ
    subst J
    simp [originalUnitFaceBox]
  | succ n ih =>
    obtain ⟨K, hK, hJK⟩ :=
      (Prepartition.mem_biUnion (originalDyadicFacePartition n)).1 hJ
    rw [Prepartition.upper_sub_lower_of_mem_splitCenter hJK, ih hK, pow_succ]
    ring

/-- The actual cells cover the closed unit face up to its null coordinate boundary. -/
theorem originalDyadicFacePartition_ae_cover (n : ℕ) :
    (originalDyadicFacePartition (ι := ι) n).iUnion =ᵐ[volume]
      Icc (fun _ : ι ↦ (0 : ℝ)) (fun _ ↦ 1) := by
  rw [(isPartition_originalDyadicFacePartition n).iUnion_eq]
  exact (originalUnitFaceBox ι).coe_ae_eq_Icc

/-- The literal finite step readout on an actual disjoint face prepartition. -/
def boxFaceStepLinear {I : Box ι} (π : Prepartition I) :
    (π.boxes → ℝ) →ₗ[ℝ] ((ι → ℝ) → ℝ) where
  toFun c y := ∑ J : π.boxes, c J * (J.1 : Set (ι → ℝ)).indicator (fun _ ↦ 1) y
  map_add' c d := by
    funext y
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

omit [Fintype ι] in
/-- The actual step readout has finite-dimensional range before any
analytic approximation estimate is used. -/
theorem finiteDimensional_boxFaceStepLinear_range {I : Box ι} (π : Prepartition I) :
    FiniteDimensional ℝ (boxFaceStepLinear π).range := inferInstance

omit [Fintype ι] in
/-- On each original disjoint cell the actual finite step is exactly that
cell's coefficient; no representative is silently changed at interfaces. -/
theorem boxFaceStepLinear_apply_of_mem {I : Box ι} (π : Prepartition I)
    (c : π.boxes → ℝ) (J : π.boxes) {y : ι → ℝ} (hy : y ∈ (J.1 : Set (ι → ℝ))) :
    boxFaceStepLinear π c y = c J := by
  classical
  change (∑ K : π.boxes,
    c K * (K.1 : Set (ι → ℝ)).indicator (fun _ ↦ 1) y) = c J
  rw [Finset.sum_eq_single J]
  · simp [hy]
  · intro K _ hK
    have hnot : y ∉ (K.1 : Set (ι → ℝ)) := by
      intro hKy
      exact hK (Subtype.ext (π.eq_of_mem_of_mem K.2 J.2 hKy hy))
    simp [hnot]
  · simp

/-- The actual full-face error of a finite step readout is exactly the sum
of its original disjoint cell errors. Closed-face interfaces contribute no
extra terms because Mathlib's half-open boxes retain their exact AE carrier. -/
theorem integral_boxFaceStep_error_sq_eq_sum
    {I : Box ι} (π : Prepartition I) (hπ : π.IsPartition)
    {g : (ι → ℝ) → ℝ} (hg : Continuous g) (c : π.boxes → ℝ) :
    (∫ y in I.Icc, (g y - boxFaceStepLinear π c y) ^ 2) =
      ∑ J : π.boxes, ∫ y in J.1.Icc, (g y - c J) ^ 2 := by
  classical
  have hcover : (⋃ J : π.boxes, (J.1 : Set (ι → ℝ))) = (I : Set (ι → ℝ)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨J, hJ⟩ := mem_iUnion.1 hy
      exact π.le_of_mem J.2 hJ
    · intro hy
      obtain ⟨J, hJ, hyJ⟩ := hπ y hy
      exact mem_iUnion.2 ⟨⟨J, hJ⟩, hyJ⟩
  have hpair : Pairwise (Disjoint on (fun J : π.boxes ↦ (J.1 : Set (ι → ℝ)))) := by
    intro J K hne
    exact π.disjoint_coe_of_mem J.2 K.2 (fun h ↦ hne (Subtype.ext h))
  have hint : ∀ J : π.boxes, IntegrableOn
      (fun y ↦ (g y - boxFaceStepLinear π c y) ^ 2) (J.1 : Set (ι → ℝ)) volume := by
    intro J
    have hc : IntegrableOn (fun y ↦ (g y - c J) ^ 2) J.1.Icc volume :=
      ((hg.sub continuous_const).pow 2).continuousOn.integrableOn_Icc
    apply (hc.mono_set Box.coe_subset_Icc).congr_fun ?_ J.1.measurableSet_coe
    intro y hy
    simp only [boxFaceStepLinear_apply_of_mem π c J hy]
  calc
    _ = ∫ y in (I : Set (ι → ℝ)), (g y - boxFaceStepLinear π c y) ^ 2 :=
      (setIntegral_congr_set I.coe_ae_eq_Icc).symm
    _ = ∫ y in ⋃ J : π.boxes, (J.1 : Set (ι → ℝ)),
        (g y - boxFaceStepLinear π c y) ^ 2 := by rw [hcover]
    _ = ∑ J : π.boxes, ∫ y in (J.1 : Set (ι → ℝ)),
        (g y - boxFaceStepLinear π c y) ^ 2 :=
      integral_iUnion_fintype (fun J ↦ J.1.measurableSet_coe) hpair hint
    _ = _ := by
      apply Finset.sum_congr rfl
      intro J _
      calc
        _ = ∫ y in (J.1 : Set (ι → ℝ)), (g y - c J) ^ 2 :=
          setIntegral_congr_fun J.1.measurableSet_coe
            (fun y hy ↦ by simp only [boxFaceStepLinear_apply_of_mem π c J hy])
        _ = _ := setIntegral_congr_set J.1.coe_ae_eq_Icc

/-- Integration over the original finite cells exactly reconstructs the
closed-box integral, including all null interfaces. -/
theorem sum_integral_box_cells_eq_integral
    {I : Box ι} (π : Prepartition I) (hπ : π.IsPartition)
    {g : (ι → ℝ) → ℝ} (hg : IntegrableOn g I.Icc volume) :
    (∑ J : π.boxes, ∫ y in J.1.Icc, g y) = ∫ y in I.Icc, g y := by
  classical
  have hcover : (⋃ J : π.boxes, (J.1 : Set (ι → ℝ))) = (I : Set (ι → ℝ)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨J, hJ⟩ := mem_iUnion.1 hy
      exact π.le_of_mem J.2 hJ
    · intro hy
      obtain ⟨J, hJ, hyJ⟩ := hπ y hy
      exact mem_iUnion.2 ⟨⟨J, hJ⟩, hyJ⟩
  have hpair : Pairwise (Disjoint on (fun J : π.boxes ↦ (J.1 : Set (ι → ℝ)))) := by
    intro J K hne
    exact π.disjoint_coe_of_mem J.2 K.2 (fun h ↦ hne (Subtype.ext h))
  calc
    _ = ∑ J : π.boxes, ∫ y in (J.1 : Set (ι → ℝ)), g y := by
      apply Finset.sum_congr rfl
      intro J _
      exact (setIntegral_congr_set J.1.coe_ae_eq_Icc).symm
    _ = ∫ y in ⋃ J : π.boxes, (J.1 : Set (ι → ℝ)), g y := by
      symm
      apply integral_iUnion_fintype (fun J ↦ J.1.measurableSet_coe) hpair
      intro J
      exact hg.mono_set (fun _ hy ↦ Box.coe_subset_Icc (π.le_of_mem J.2 hy))
    _ = ∫ y in (I : Set (ι → ℝ)), g y := by rw [hcover]
    _ = _ := setIntegral_congr_set I.coe_ae_eq_Icc

/-- Actual disjoint face cells also reconstruct every continuous collar
integral; the normal interval is the same original interval in every cell. -/
theorem sum_integral_box_cell_collars_eq_integral
    {I : Box ι} (π : Prepartition I) (hπ : π.IsPartition)
    {F : (ι → ℝ) × ℝ → ℝ} (hF : Continuous F) (h : ℝ) :
    (∑ J : π.boxes, ∫ p in J.1.Icc ×ˢ Icc 0 h, F p) =
      ∫ p in I.Icc ×ˢ Icc 0 h, F p := by
  have hint (J : Box ι) : IntegrableOn F (J.Icc ×ˢ Icc 0 h)
      ((volume : Measure (ι → ℝ)).prod volume) := by
    change IntegrableOn F (Icc J.lower J.upper ×ˢ Icc 0 h) _
    rw [← Icc_prod_eq (J.lower, (0 : ℝ)) (J.upper, h)]
    exact hF.continuousOn.integrableOn_Icc
  have hint' : Integrable F
      ((volume.restrict I.Icc).prod (volume.restrict (Icc 0 h))) := by
    rw [Measure.prod_restrict]
    exact hint I
  simp only [Measure.volume_eq_prod]
  calc
    _ = ∑ J : π.boxes, ∫ y in J.1.Icc, ∫ t in Icc 0 h, F (y, t) := by
      apply Finset.sum_congr rfl
      intro J _
      exact setIntegral_prod F (hint J.1)
    _ = ∫ y in I.Icc, ∫ t in Icc 0 h, F (y, t) :=
      sum_integral_box_cells_eq_integral π hπ hint'.integral_prod_left
    _ = _ := (setIntegral_prod F (hint I)).symm

end OTSelector.Reconstruction

end
end
