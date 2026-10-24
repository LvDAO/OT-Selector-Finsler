import OTSelector.Reconstruction.FinslerOriginalLabelDependentThinning

/-!
# The single-particle block law of the kernel-marked cloud

This file closes the single remaining sub-gap of
FinslerOriginalLabelDependentThinning.lean: the single-particle block law

  (markedPointLaw q K).map (blockOnePoint q m)
    = mixturePointLaw (fun _ : Fin (m ^ q) => (m ^ q) ^ -1)
        (fun c => markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))).

The proof follows the Fubini-over-the-block-partition route:

* blockRescaleMap_blockScaledLocalPoint: on the block of label c and on the unit
  cube, the block rescaling inverts the dilated local coordinate;
* map_restrict_blockScaledLocalPoint: the restriction of the cube measure to the
  block of encoded label c, pushed forward by the dilated local coordinate, is
  the inverse of the number of blocks times the cube measure (the in-block
  change of variables);
* map_markedPointLaw_blockOnePoint: the single-particle block law, obtained by
  expanding both sides on the boxes {c} x U and using Measure.compProd_apply,
  the block identity and the in-block change of variables;
* kernelMarkedCloudLaw_blockLocalCloudEncoded_law_unconditional: the leaf-block
  law identification of FinslerOriginalLabelDependentThinning.lean with the
  hypothesis discharged.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open OTSelector OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A : Type*} [MeasurableSpace A]

/-! ## The block identity and the in-block change of variables -/

/-- Almost every point of the unit cube lies in the open cube. -/
theorem ae_mem_unitCubeSet_cubeMeasure (q : ℕ) :
    ∀ᵐ x ∂(cubeMeasure (Fin q) 1), x ∈ unitCubeSet q := by
  filter_upwards [ae_mem_cubeMeasure_Ioo (q := q) (L := 1) one_pos] with x hx
  simpa only [unitCubeSet, Set.mem_pi, Set.mem_univ, forall_true_left] using hx

/-- On the unit cube, inside the block of label c, the block rescaling inverts
the dilated local coordinate. -/
theorem blockRescaleMap_blockScaledLocalPoint (q m : ℕ) [NeZero m] (hm : 0 < m)
    (c : Fin q → Fin m) {x : Fin q → ℝ} (hx : x ∈ unitCubeSet q)
    (hlabel : blockLabelCode q m x = finFunctionFinEquiv c) :
    blockRescaleMap c (blockScaledLocalPoint q m x) = x := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hb : ∀ l : Fin q, blockIndex ((m : ℝ)⁻¹) (x l) = (c l).val :=
    (blockLabelCode_eq_finFunctionFinEquiv_iff hx c).mp hlabel
  funext l
  have hbR : ((blockIndex ((m : ℝ)⁻¹) (x l) : ℕ) : ℝ) = ((c l).val : ℝ) := by
    rw [hb l]
  unfold blockRescaleMap blockCorner blockScaledLocalPoint localCoord
  rw [hbR]
  field_simp
  ring

/-- The in-block change of variables.  The cube measure restricted to the
block of encoded label c, pushed forward by the dilated local coordinate, is
(m ^ q) ^ -1 times the cube measure. -/
theorem map_restrict_blockScaledLocalPoint (q m : ℕ) [NeZero m] (hm : 0 < m)
    (c : Fin q → Fin m) :
    ((cubeMeasure (Fin q) 1).restrict
        {x : Fin q → ℝ | blockLabelCode q m x = finFunctionFinEquiv c}).map
        (blockScaledLocalPoint q m) =
      (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ • cubeMeasure (Fin q) 1 := by
  classical
  have hBmeas : MeasurableSet {x : Fin q → ℝ | blockLabelCode q m x = finFunctionFinEquiv c} :=
    (measurableSet_singleton (finFunctionFinEquiv c)).preimage (measurable_blockLabelCode q m)
  have hpair := map_blockLabelCode_scaledLocal_cubeMeasure (q := q) (m := m) hm
  have hbox : ∀ T : Set (Fin q → ℝ), MeasurableSet T →
      ((cubeMeasure (Fin q) 1).map (fun x : Fin q → ℝ =>
          (blockLabelCode q m x, blockScaledLocalPoint q m x))) ({finFunctionFinEquiv c} ×ˢ T)
        = (cubeMeasure (Fin q) 1) (blockScaledLocalPoint q m ⁻¹' T ∩
            {x : Fin q → ℝ | blockLabelCode q m x = finFunctionFinEquiv c}) := by
    intro T hT
    rw [Measure.map_apply
      ((measurable_blockLabelCode q m).prod (measurable_blockScaledLocalPoint q m))
      ((measurableSet_singleton (finFunctionFinEquiv c)).prod hT)]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_inter_iff,
      ]
    tauto
  ext T hT
  rw [Measure.map_apply (measurable_blockScaledLocalPoint q m) hT,
    Measure.restrict_apply (hT.preimage (measurable_blockScaledLocalPoint q m)),
    Measure.smul_apply, smul_eq_mul]
  have hboxval : ((uniformMeasure (Fin (m ^ q))).prod (cubeMeasure (Fin q) 1))
      ({finFunctionFinEquiv c} ×ˢ T) =
      (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ * (cubeMeasure (Fin q) 1) T := by
    rw [Measure.prod_prod, uniformMeasure_singleton, Fintype.card_fin]
  rw [← hbox T hT, hpair]
  exact hboxval

/-! ## Box masses of the label-dependent mixture -/

/-- The mass of a box {c} x U under a label-dependent mixture. -/
theorem mixturePointLaw_box {γ Pos : Type*} [Fintype γ] [DecidableEq γ]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] [MeasurableSpace Pos]
    (p : γ → ℝ≥0) (ν : γ → Measure Pos) [∀ d, IsProbabilityMeasure (ν d)]
    (c : γ) (U : Set Pos)
    (hU : MeasurableSet U) :
    mixturePointLaw p ν ({c} ×ˢ U) = (p c : ℝ≥0∞) * (ν c) U := by
  classical
  rw [mixturePointLaw, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hsingle : ∀ b ∈ (Finset.univ : Finset γ), b ≠ c →
      ((Measure.dirac b).prod (ν b)) ({c} ×ˢ U) = 0 := by
    intro b _ hb
    rw [Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left ((measurableSet_singleton c).prod hU)]
    have hpre : (Prod.mk b) ⁻¹' ({c} ×ˢ U : Set (γ × Pos)) = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro h1 -
      exact hb h1
    rw [hpre]
    simp
  rw [Finset.sum_eq_single c]
  · rw [Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left ((measurableSet_singleton c).prod hU)]
    have hpre : (Prod.mk c) ⁻¹' ({c} ×ˢ U : Set (γ × Pos)) = U := by
      ext y
      simp
    rw [hpre]
  · intro b hb hbc
    rw [hsingle b hb hbc, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-! ## The single-particle block law -/

set_option maxHeartbeats 3200000 in
/-- **The single-particle block law.**  Pushing the kernel-marked point law through
the block encoding gives the label-dependent mixture of the block-local point laws,
with block weights the inverse of the number of blocks. -/
theorem map_markedPointLaw_blockOnePoint (q m : ℕ) [NeZero m] (hm : 0 < m)
    (K : Kernel (Fin q → ℝ) A) [IsMarkovKernel K] :
    (markedPointLaw q K).map (blockOnePoint (A := A) q m) =
      mixturePointLaw (fun _ : Fin (m ^ q) => (((m ^ q : ℕ) : ℝ≥0))⁻¹)
        (fun c : Fin (m ^ q) =>
          markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))) := by
  classical
  have hbox : ∀ (c : Fin (m ^ q)) (U : Set ((Fin q → ℝ) × A)), MeasurableSet U →
      ((markedPointLaw q K).map (blockOnePoint (A := A) q m)) ({c} ×ˢ U) =
        (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ *
          (markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))) U := by
    intro c U hU
    set b : Fin q → Fin m := finFunctionFinEquiv.symm c with hb
    have hbenc : finFunctionFinEquiv b = c := Equiv.apply_symm_apply _ c
    set B : Set (Fin q → ℝ) := {x | blockLabelCode q m x = finFunctionFinEquiv b} with hB
    have hBmeas : MeasurableSet B :=
      (measurableSet_singleton (finFunctionFinEquiv b)).preimage (measurable_blockLabelCode q m)
    set S : Set ((Fin q → ℝ) × A) :=
      blockOnePoint (A := A) q m ⁻¹' ({c} ×ˢ U) with hS
    have hSmeas : MeasurableSet S :=
      ((measurableSet_singleton c).prod hU).preimage (measurable_blockOnePoint q m)
    have hsec : ∀ x : Fin q → ℝ, (Prod.mk x) ⁻¹' S =
        (if blockLabelCode q m x = finFunctionFinEquiv b then
          (Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U else ∅) := by
      intro x
      rw [hS]
      by_cases hx : blockLabelCode q m x = finFunctionFinEquiv b
      · rw [if_pos hx]
        ext a
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, blockOnePoint,
          blockLocalMark]
        constructor
        · rintro ⟨-, h2⟩
          exact h2
        · intro h2
          exact ⟨hx.trans hbenc, h2⟩
      · rw [if_neg hx]
        ext a
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, blockOnePoint, blockLocalMark]
        rintro ⟨h1, -⟩
        exact hx (h1.trans hbenc.symm)
    have step1 : ((markedPointLaw q K).map (blockOnePoint (A := A) q m)) ({c} ×ˢ U)
        = (markedPointLaw q K) S := by
      rw [hS]
      exact Measure.map_apply (measurable_blockOnePoint q m) ((measurableSet_singleton c).prod hU)
    have step2 : (markedPointLaw q K) S =
        ∫⁻ x, (K x) ((Prod.mk x) ⁻¹' S) ∂(cubeMeasure (Fin q) 1) := by
      rw [show markedPointLaw q K = cubeMeasure (Fin q) 1 ⊗ₘ K from rfl]
      exact Measure.compProd_apply hSmeas
    have step3 : ∫⁻ x, (K x) ((Prod.mk x) ⁻¹' S) ∂(cubeMeasure (Fin q) 1) =
        ∫⁻ x, B.indicator (fun x => (K x) ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U)) x
          ∂(cubeMeasure (Fin q) 1) := by
      refine lintegral_congr fun x => ?_
      rw [hsec x]
      by_cases hx : blockLabelCode q m x = finFunctionFinEquiv b
      · rw [if_pos hx, Set.indicator_of_mem (show x ∈ B from by rw [hB]; exact hx)]
      · rw [if_neg hx]
        have hxB : x ∉ B := by rw [hB]; exact hx
        simp only [Set.indicator, hxB, if_false]
        simp
    have step4 : ∫⁻ x, B.indicator (fun x => (K x) ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U)) x
          ∂(cubeMeasure (Fin q) 1) =
        ∫⁻ x in B, (K x) ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U)
          ∂(cubeMeasure (Fin q) 1) := by
      rw [lintegral_indicator hBmeas]
    have step5 : ∫⁻ x in B, (K x) ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U)
          ∂(cubeMeasure (Fin q) 1) =
        ∫⁻ x in B, (blockLocalKernel K b (blockScaledLocalPoint q m x))
          ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U) ∂(cubeMeasure (Fin q) 1) := by
      refine lintegral_congr_ae ?_
      change ∀ᵐ x ∂((cubeMeasure (Fin q) 1).restrict B),
        (K x) ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U) =
          (blockLocalKernel K b (blockScaledLocalPoint q m x))
            ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U)
      rw [ae_restrict_iff' hBmeas]
      filter_upwards [ae_mem_unitCubeSet_cubeMeasure q] with x hxuni
      intro hxB
      have hlabel : blockLabelCode q m x = finFunctionFinEquiv b := by
        simpa [hB] using hxB
      rw [blockLocalKernel_apply, blockRescaleMap_blockScaledLocalPoint q m hm b hxuni hlabel]
    have hHmeas : Measurable (fun y : Fin q → ℝ =>
        (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)) := by
      have hemb : ∀ y : Fin q → ℝ,
          (Kernel.prod Kernel.id (blockLocalKernel K b) y) U =
            (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U) := by
        intro y
        rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
          Measure.map_apply measurable_prodMk_left hU]
      have hmeas := Kernel.measurable_coe (Kernel.prod Kernel.id (blockLocalKernel K b)) hU
      rwa [show (fun y => (Kernel.prod Kernel.id (blockLocalKernel K b) y) U) =
          (fun y => (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)) from funext hemb] at hmeas
    have step6 : ∫⁻ x in B, (blockLocalKernel K b (blockScaledLocalPoint q m x))
          ((Prod.mk (blockScaledLocalPoint q m x)) ⁻¹' U) ∂(cubeMeasure (Fin q) 1) =
        ∫⁻ y, (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)
          ∂(((cubeMeasure (Fin q) 1).restrict B).map (blockScaledLocalPoint q m)) :=
      (lintegral_map hHmeas (measurable_blockScaledLocalPoint q m)).symm
    have step7 : ∫⁻ y, (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)
          ∂(((cubeMeasure (Fin q) 1).restrict B).map (blockScaledLocalPoint q m)) =
        ∫⁻ y, (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)
          ∂(((((m ^ q : ℕ)) : ℝ≥0∞)⁻¹) • cubeMeasure (Fin q) 1) := by
      rw [hB, map_restrict_blockScaledLocalPoint q m hm b]
    have step8 : ∫⁻ y, (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)
          ∂(((((m ^ q : ℕ)) : ℝ≥0∞)⁻¹) • cubeMeasure (Fin q) 1) =
        (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ * ∫⁻ y, (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)
          ∂(cubeMeasure (Fin q) 1) := by
      rw [lintegral_smul_measure, smul_eq_mul]
    have step9 : (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ * ∫⁻ y, (blockLocalKernel K b y) ((Prod.mk y) ⁻¹' U)
          ∂(cubeMeasure (Fin q) 1) =
        (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ * (markedPointLaw q (blockLocalKernel K b)) U := by
      rw [show markedPointLaw q (blockLocalKernel K b) =
        cubeMeasure (Fin q) 1 ⊗ₘ blockLocalKernel K b from rfl, Measure.compProd_apply hU]
    exact step1.trans (step2.trans (step3.trans (step4.trans (step5.trans
      (step6.trans (step7.trans (step8.trans step9)))))))
  ext Z hZ
  set Zc : Fin (m ^ q) → Set ((Fin q → ℝ) × A) := fun c => {y | (c, y) ∈ Z} with hZc
  have hZcmeas : ∀ c, MeasurableSet (Zc c) := by
    intro c
    rw [hZc]
    exact hZ.preimage measurable_prodMk_left
  set Sc : Fin (m ^ q) → Set ((Fin q → ℝ) × A) :=
    fun c => blockOnePoint (A := A) q m ⁻¹' ({c} ×ˢ Zc c) with hSc
  have hScmeas : ∀ c, MeasurableSet (Sc c) := by
    intro c
    rw [hSc]
    exact ((measurableSet_singleton c).prod (hZcmeas c)).preimage (measurable_blockOnePoint q m)
  have hdisj : ((Finset.univ : Finset (Fin (m ^ q))) : Set (Fin (m ^ q))).PairwiseDisjoint Sc := by
    intro c _ d _ hcd
    refine Set.disjoint_left.mpr ?_
    rintro p hp hq
    rw [hSc] at hp hq
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff] at hp hq
    exact hcd (hp.1.symm.trans hq.1)
  have hcover : blockOnePoint (A := A) q m ⁻¹' Z =
      ⋃ c ∈ (Finset.univ : Finset (Fin (m ^ q))), Sc c := by
    ext p
    constructor
    · intro hp
      refine Set.mem_iUnion.mpr
        ⟨(blockOnePoint (A := A) q m p).1, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [hSc]
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, hZc]
      exact ⟨trivial, by simpa using hp⟩
    · intro hp
      simp only [Set.mem_iUnion, Finset.mem_univ] at hp
      obtain ⟨c, -, hc⟩ := hp
      rw [hSc] at hc
      have hmem : blockOnePoint (A := A) q m p ∈ ({c} : Set (Fin (m ^ q))) ×ˢ Zc c :=
        Set.mem_preimage.mp hc
      have h1 : (blockOnePoint (A := A) q m p).1 = c :=
        Set.mem_singleton_iff.mp (Set.mem_prod.mp hmem).1
      have h2 : (blockOnePoint (A := A) q m p).2 ∈ Zc c := (Set.mem_prod.mp hmem).2
      have hbp : blockOnePoint (A := A) q m p = (c, (blockOnePoint (A := A) q m p).2) :=
        Prod.ext h1 rfl
      rw [Set.mem_preimage, hbp]
      rw [hZc] at h2
      exact h2
  have hLHS : ((markedPointLaw q K).map (blockOnePoint (A := A) q m)) Z =
      ∑ c, (markedPointLaw q K) (Sc c) := by
    rw [Measure.map_apply (measurable_blockOnePoint q m) hZ, hcover,
      measure_biUnion_finset hdisj (fun c _ => hScmeas c)]
  have hRHS : mixturePointLaw (fun _ : Fin (m ^ q) => (((m ^ q : ℕ) : ℝ≥0))⁻¹)
        (fun c : Fin (m ^ q) =>
          markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))) Z =
      ∑ c, (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ *
        (markedPointLaw q (blockLocalKernel K (finFunctionFinEquiv.symm c))) (Zc c) := by
    rw [mixturePointLaw, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro c _
    have hZc' : Zc c = {y : (Fin q → ℝ) × A | (c, y) ∈ Z} := by
      rw [hZc]
    have hpre : (Prod.mk c) ⁻¹' Z = {y : (Fin q → ℝ) × A | (c, y) ∈ Z} := rfl
    have hcoe : ENNReal.ofNNReal ((((m ^ q : ℕ) : ℝ≥0))⁻¹) = (((m ^ q : ℕ)) : ℝ≥0∞)⁻¹ :=
      ENNReal.coe_inv (Nat.cast_ne_zero.mpr (pow_ne_zero q (NeZero.ne m)))
    rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hZ, hpre, hZc', hcoe]
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [hSc, ← Measure.map_apply (measurable_blockOnePoint q m)
    ((measurableSet_singleton c).prod (hZcmeas c))]
  exact hbox c (Zc c) (hZcmeas c)

/-- The leaf-block law identification of FinslerOriginalLabelDependentThinning.lean
with the single-particle block law discharged. -/
theorem kernelMarkedCloudLaw_blockLocalCloudEncoded_law_unconditional
    (q m : ℕ) [NeZero m] (hm : 0 < m) (R : ℝ≥0) (K : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel K] (b : Fin q → Fin m) :
    (kernelMarkedCloudLaw q A K R).map (blockLocalCloudEncoded (A := A) q m b) =
      blockDataLaw (markedPointLaw q (blockLocalKernel K b))
        (fun n => poissonMeasure (R / (m ^ q : ℝ≥0)) {n}) :=
  kernelMarkedCloudLaw_blockLocalCloudEncoded_law q m hm R K
    (map_markedPointLaw_blockOnePoint q m hm K) b

end OTSelector.Reconstruction