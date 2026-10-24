import OTSelector.Probability.FinslerTileBlockLawComparison
import OTSelector.Limit.TileCountBinomialLaw
import OTSelector.Limit.FinslerTileBlockMeasurability

/-!
# Discharging the count-law and integrability inputs of the tile block law

This module strengthens
`integral_frozenModelTileBlock_eq_modelBlockSum` of
`OTSelector.Probability.FinslerTileBlockLawComparison`:

* the binomial count weights `hNs`/`hNt` are proved from the label-mass
  hypotheses `μs (labS ⁻¹' {c}) = ofReal w`, `μt (labT ⁻¹' {c}) = ofReal w`
  using `pi_tileCountEqSet_toReal_eq_binomialMass` of
  `OTSelector.Limit.TileCountBinomialLaw`;
* the integrability hypotheses `hF`, `hint`, `hintG` are proved from
  measurability and uniform boundedness of the frozen cost and probe kernels.

The resulting theorem
`integral_frozenModelTileBlock_eq_modelBlockSum_of_bounds` takes only the sample
law, the atlas pushforwards, the label masses, the positivity of `w`, the
measurability of `kin`, `g` and the label/mark maps, and uniform boundedness of
the marked kernels.  The measurability of the marked kernels themselves is
proved (`measurable_markedKineticKernel`, `measurable_markedProbeKernel`), and
the block and pattern-block measurability and integrability follow from
`measurable_maxCardValue` and `abs_maxCardValue_le_of_abs_le`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Xs Yt : Type*} [MeasurableSpace Xs] [MeasurableSpace Yt]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-! ## The block value with frozen labels -/

/-- The tile-`c` block value with frozen label arrays and a frozen ambient cost
matrix. -/
noncomputable def frozenModelTileBlockOfLabels {m : ℕ} (u v : Fin m → ι)
    (D : Fin m → Fin m → ℝ) (c : ι) : ℝ :=
  PartialMatching.maxCardValue
    (fun i : Fin (patternCount u c) => fun j : Fin (patternCount v c) =>
      D (tileEmbedding u c i) (tileEmbedding v c j))

/-- The physical frozen block is the frozen-label block applied to the label
arrays and the frozen edge matrix of the sample. -/
theorem frozenModelTileBlock_eq_of_labels {m : ℕ} (labS : Xs → ι) (labT : Yt → ι)
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ) (c : ι)
    (p : (Fin m → Xs) × (Fin m → Yt)) :
    frozenModelTileBlock labS labT frozenCost modelProbe t c p =
      frozenModelTileBlockOfLabels (fun i => labS (p.1 i)) (fun j => labT (p.2 j))
        (fun i j => frozenCost (p.1 i) (p.2 j) + t * modelProbe (p.1 i) (p.2 j)) c :=
  rfl

/-- With frozen labels, the block value is measurable in the ambient matrix. -/
theorem measurable_frozenModelTileBlockOfLabels_snd {m : ℕ} (u v : Fin m → ι) (c : ι) :
    Measurable fun D : Fin m → Fin m → ℝ => frozenModelTileBlockOfLabels u v D c := by
  unfold frozenModelTileBlockOfLabels
  exact PartialMatching.measurable_maxCardValue _
    (fun i j => (measurable_pi_apply (a := tileEmbedding v c j)).comp
      (measurable_pi_apply (a := tileEmbedding u c i)))

/-- **Measurability of the physical frozen block under random labels.** -/
theorem measurable_frozenModelTileBlock {m : ℕ} (labS : Xs → ι) (hS : Measurable labS)
    (labT : Yt → ι) (hT : Measurable labT)
    (frozenCost modelProbe : Xs → Yt → ℝ)
    (hcost : Measurable fun p : Xs × Yt => frozenCost p.1 p.2)
    (hprobe : Measurable fun p : Xs × Yt => modelProbe p.1 p.2)
    (t : ℝ) (c : ι) :
    Measurable fun p : (Fin m → Xs) × (Fin m → Yt) =>
      frozenModelTileBlock labS labT frozenCost modelProbe t c p := by
  classical
  have hL : Measurable fun p : (Fin m → Xs) × (Fin m → Yt) =>
      ((fun i => labS (p.1 i)), (fun j => labT (p.2 j))) :=
    (measurable_pi_lambda _ fun i =>
      hS.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      (measurable_pi_lambda _ fun j =>
        hT.comp ((measurable_pi_apply j).comp measurable_snd))
  have hC : Measurable fun p : (Fin m → Xs) × (Fin m → Yt) =>
      fun i j => frozenCost (p.1 i) (p.2 j) + t * modelProbe (p.1 i) (p.2 j) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => by
      have hp : Measurable fun p : (Fin m → Xs) × (Fin m → Yt) => (p.1 i, p.2 j) :=
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp measurable_snd)
      have h1 : Measurable fun p : (Fin m → Xs) × (Fin m → Yt) =>
          frozenCost (p.1 i) (p.2 j) := hcost.comp hp
      have h2 : Measurable fun p : (Fin m → Xs) × (Fin m → Yt) =>
          t * modelProbe (p.1 i) (p.2 j) :=
        measurable_const.mul (hprobe.comp hp)
      exact h1.add h2
  have h := measurable_comp_uncurry_of_forall
    (f := fun p : (Fin m → Xs) × (Fin m → Yt) =>
      ((fun i => labS (p.1 i)), (fun j => labT (p.2 j))))
    (g := fun p : (Fin m → Xs) × (Fin m → Yt) =>
      fun i j => frozenCost (p.1 i) (p.2 j) + t * modelProbe (p.1 i) (p.2 j))
    (F := fun (w : (Fin m → ι) × (Fin m → ι)) (D : Fin m → Fin m → ℝ) =>
      frozenModelTileBlockOfLabels w.1 w.2 D c)
    hL hC fun w => measurable_frozenModelTileBlockOfLabels_snd w.1 w.2 c
  simpa only [frozenModelTileBlock_eq_of_labels] using h

/-! ## Boundedness of the block values -/

/-- The pattern block is bounded by the minimum tile size times the edge bound. -/
theorem abs_frozenPatternBlock_le_of_abs_le {a b : ℕ}
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ)
    (u : Fin a → Xs) (v : Fin b → Yt) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, |frozenCost (u i) (v j) + t * modelProbe (u i) (v j)| ≤ B) :
    |frozenPatternBlock frozenCost modelProbe t u v| ≤ (min a b : ℝ) * B :=
  PartialMatching.abs_maxCardValue_le_of_abs_le hB0 hB

/-- The pattern block is bounded by the minimum tile size times the kernel
bounds. -/
theorem abs_frozenPatternBlock_le_of_bounds {a b : ℕ}
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ)
    (u : Fin a → Xs) (v : Fin b → Yt) {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hC : ∀ x y, |frozenCost x y| ≤ C) (hG : ∀ x y, |modelProbe x y| ≤ G) :
    |frozenPatternBlock frozenCost modelProbe t u v| ≤
      (min a b : ℝ) * (C + |t| * G) := by
  refine abs_frozenPatternBlock_le_of_abs_le frozenCost modelProbe t u v
    (add_nonneg hC0 (mul_nonneg (abs_nonneg t) hG0)) fun i j => ?_
  calc |frozenCost (u i) (v j) + t * modelProbe (u i) (v j)|
      ≤ |frozenCost (u i) (v j)| + |t * modelProbe (u i) (v j)| := abs_add_le _ _
    _ ≤ C + |t| * G := by
        refine add_le_add (hC _ _) ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hG _ _) (abs_nonneg t)

/-- The physical block is bounded by the sample size times the edge bound. -/
theorem abs_frozenModelTileBlock_le {m : ℕ} (labS : Xs → ι) (labT : Yt → ι)
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ) (c : ι)
    (p : (Fin m → Xs) × (Fin m → Yt)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, |frozenCost (p.1 i) (p.2 j) + t * modelProbe (p.1 i) (p.2 j)| ≤ B) :
    |frozenModelTileBlock labS labT frozenCost modelProbe t c p| ≤ (m : ℝ) * B := by
  rw [frozenModelTileBlock_eq_of_labels]
  unfold frozenModelTileBlockOfLabels
  have h := PartialMatching.abs_maxCardValue_le_of_abs_le
    (D := fun i : Fin (patternCount (fun i => labS (p.1 i)) c) =>
      fun j : Fin (patternCount (fun j => labT (p.2 j)) c) =>
        frozenCost (p.1 (tileEmbedding (fun i => labS (p.1 i)) c i))
            (p.2 (tileEmbedding (fun j => labT (p.2 j)) c j)) +
          t * modelProbe (p.1 (tileEmbedding (fun i => labS (p.1 i)) c i))
            (p.2 (tileEmbedding (fun j => labT (p.2 j)) c j)))
    hB0 (fun i j => hB _ _)
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ hB0
  have h1 : patternCount (fun i => labS (p.1 i)) c ≤ m := by
    rw [← card_tileIndex]
    simpa using Fintype.card_subtype_le (fun i : Fin m => labS (p.1 i) = c)
  exact_mod_cast le_trans (min_le_left _ _) h1

/-- The physical block is bounded by the sample size times the kernel bounds. -/
theorem abs_frozenModelTileBlock_le_of_bounds {m : ℕ} (labS : Xs → ι) (labT : Yt → ι)
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ) (c : ι)
    (p : (Fin m → Xs) × (Fin m → Yt)) {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hC : ∀ x y, |frozenCost x y| ≤ C) (hG : ∀ x y, |modelProbe x y| ≤ G) :
    |frozenModelTileBlock labS labT frozenCost modelProbe t c p| ≤
      (m : ℝ) * (C + |t| * G) := by
  refine abs_frozenModelTileBlock_le labS labT frozenCost modelProbe t c p
    (add_nonneg hC0 (mul_nonneg (abs_nonneg t) hG0)) fun i j => ?_
  calc |frozenCost (p.1 i) (p.2 j) + t * modelProbe (p.1 i) (p.2 j)|
      ≤ |frozenCost (p.1 i) (p.2 j)| + |t * modelProbe (p.1 i) (p.2 j)| := abs_add_le _ _
    _ ≤ C + |t| * G := by
        refine add_le_add (hC _ _) ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hG _ _) (abs_nonneg t)

/-! ## Integrability from boundedness -/

/-- Measurability of the pattern block. -/
theorem measurable_frozenPatternBlock {a b : ℕ} (frozenCost modelProbe : Xs → Yt → ℝ)
    (hcost : Measurable fun p : Xs × Yt => frozenCost p.1 p.2)
    (hprobe : Measurable fun p : Xs × Yt => modelProbe p.1 p.2) (t : ℝ) :
    Measurable fun p : (Fin a → Xs) × (Fin b → Yt) =>
      frozenPatternBlock frozenCost modelProbe t p.1 p.2 := by
  unfold frozenPatternBlock
  exact PartialMatching.measurable_maxCardValue _
    (fun i j => by
      have hp : Measurable fun p : (Fin a → Xs) × (Fin b → Yt) => (p.1 i, p.2 j) :=
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply j).comp measurable_snd)
      have h1 : Measurable fun p : (Fin a → Xs) × (Fin b → Yt) =>
          frozenCost (p.1 i) (p.2 j) := hcost.comp hp
      have h2 : Measurable fun p : (Fin a → Xs) × (Fin b → Yt) =>
          t * modelProbe (p.1 i) (p.2 j) := measurable_const.mul (hprobe.comp hp)
      exact h1.add h2)

/-- Integrability of the physical frozen block from measurability and uniform
boundedness of the kernels. -/
theorem integrable_frozenModelTileBlock_of_bounds {m : ℕ} (labS : Xs → ι)
    (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (frozenCost modelProbe : Xs → Yt → ℝ)
    (hcost : Measurable fun p : Xs × Yt => frozenCost p.1 p.2)
    (hprobe : Measurable fun p : Xs × Yt => modelProbe p.1 p.2)
    (t : ℝ) (c : ι) {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hC : ∀ x y, |frozenCost x y| ≤ C) (hG : ∀ x y, |modelProbe x y| ≤ G)
    (P : Measure ((Fin m → Xs) × (Fin m → Yt))) [IsFiniteMeasure P] :
    Integrable (fun p => frozenModelTileBlock labS labT frozenCost modelProbe t c p) P := by
  refine Integrable.of_bound
    (measurable_frozenModelTileBlock labS hS labT hT frozenCost modelProbe
      hcost hprobe t c).aestronglyMeasurable ((m : ℝ) * (C + |t| * G)) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  exact abs_frozenModelTileBlock_le_of_bounds labS labT frozenCost modelProbe t c p
    hC0 hG0 hC hG

/-- Integrability of a pattern block composed with arbitrary index maps, over a
product of finite product measures.  This covers both the pattern-restricted
measure (full sample indices, tile coordinates selected through `tileEquiv`) and
the normalized tile measure (identity index maps). -/
theorem integrable_frozenPatternBlock_comp_of_bounds {a b ms mt : ℕ}
    (frozenCost modelProbe : Xs → Yt → ℝ)
    (hcost : Measurable fun p : Xs × Yt => frozenCost p.1 p.2)
    (hprobe : Measurable fun p : Xs × Yt => modelProbe p.1 p.2)
    (t : ℝ) {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hC : ∀ x y, |frozenCost x y| ≤ C) (hG : ∀ x y, |modelProbe x y| ≤ G)
    (eS : Fin a → Fin ms) (eT : Fin b → Fin mt)
    (νs : Fin ms → Measure Xs) [∀ i, IsFiniteMeasure (νs i)]
    (νt : Fin mt → Measure Yt) [∀ i, IsFiniteMeasure (νt i)] :
    Integrable (fun z : (Fin ms → Xs) × (Fin mt → Yt) =>
      frozenPatternBlock frozenCost modelProbe t
        (fun i => z.1 (eS i)) (fun j => z.2 (eT j)))
      ((Measure.pi νs).prod (Measure.pi νt)) := by
  haveI : IsFiniteMeasure (Measure.pi νs) := inferInstance
  haveI : IsFiniteMeasure (Measure.pi νt) := inferInstance
  haveI : IsFiniteMeasure ((Measure.pi νs).prod (Measure.pi νt)) := inferInstance
  refine Integrable.of_bound ?_ ((min a b : ℝ) * (C + |t| * G)) ?_
  · have hmap : Measurable fun z : (Fin ms → Xs) × (Fin mt → Yt) =>
        ((fun i => z.1 (eS i)), (fun j => z.2 (eT j))) :=
      (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply (eS i)).comp measurable_fst).prodMk
        (measurable_pi_lambda _ fun j =>
          (measurable_pi_apply (eT j)).comp measurable_snd)
    exact ((measurable_frozenPatternBlock frozenCost modelProbe hcost hprobe t).comp hmap).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs]
    exact abs_frozenPatternBlock_le_of_bounds frozenCost modelProbe t _ _ hC0 hG0 hC hG

section MarkedMeasurability

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Measurability of the clamped displacement in the pair of points. -/
theorem measurable_mDisplacement_pair (q : ℕ) :
    Measurable fun p : (Fin q → ℝ) × (Fin q → ℝ) => mDisplacement p.1 p.2 := by
  unfold mDisplacement
  exact measurable_pi_lambda _ fun l =>
    ((measurable_cubeTruncPoint_apply q l).comp measurable_snd).sub
      ((measurable_cubeTruncPoint_apply q l).comp measurable_fst)

/-- Measurability of the marked kinetic kernel from measurability of `kin` and of
the mark maps. -/
theorem measurable_markedKineticKernel {q : ℕ} {r : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT) :
    Measurable fun p : Xs × Yt =>
      markedKineticKernel (q := q) r kin markS markT p.1 p.2 := by
  have hmS1 : Measurable fun p : Xs × Yt => (markS p.1).1 :=
    measurable_fst.comp (hmarkS.comp measurable_fst)
  have hmS2 : Measurable fun p : Xs × Yt => (markS p.1).2 :=
    measurable_snd.comp (hmarkS.comp measurable_fst)
  have hmT1 : Measurable fun p : Xs × Yt => (markT p.2).1 :=
    measurable_fst.comp (hmarkT.comp measurable_snd)
  have hmT2 : Measurable fun p : Xs × Yt => (markT p.2).2 :=
    measurable_snd.comp (hmarkT.comp measurable_snd)
  have hdisp : Measurable fun p : Xs × Yt =>
      mDisplacement (markS p.1).1 (markT p.2).1 :=
    (measurable_mDisplacement_pair q).comp (hmS1.prodMk hmT1)
  have hpair : Measurable fun p : Xs × Yt =>
      (((markS p.1).2, (markT p.2).2),
        mDisplacement (markS p.1).1 (markT p.2).1) :=
    (hmS2.prodMk hmT2).prodMk hdisp
  exact measurable_const.mul (hkin.comp hpair)

/-- Measurability of the marked probe kernel from measurability of `g` and of the
mark maps. -/
theorem measurable_markedProbeKernel {g : A → B → ℝ}
    (hg : Measurable (Function.uncurry g))
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT) :
    Measurable fun p : Xs × Yt => markedProbeKernel g markS markT p.1 p.2 := by
  have hmS2 : Measurable fun p : Xs × Yt => (markS p.1).2 :=
    measurable_snd.comp (hmarkS.comp measurable_fst)
  have hmT2 : Measurable fun p : Xs × Yt => (markT p.2).2 :=
    measurable_snd.comp (hmarkT.comp measurable_snd)
  exact hg.comp (hmS2.prodMk hmT2)

end MarkedMeasurability

/-! ## The final theorem with the count law and integrability discharged -/

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- **`hblock` identity with all technical inputs discharged.**  Under the sample
law, the atlas pushforwards, the label-mass hypotheses and uniform boundedness of
the marked kernels, the expectation of the physical frozen tile block equals the
marked model block sum.  The binomial count weights and all integrability
hypotheses of `integral_frozenModelTileBlock_eq_modelBlockSum` are discharged. -/
theorem integral_frozenModelTileBlock_eq_modelBlockSum_of_bounds {q : ℕ} {t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (c : ι) (m : ℕ) (w : unitInterval) (hwpos : 0 < (w : ℝ))
    (hws : μs (labS ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (hwt : μt (labT ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT)
    (hα : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map markS =
      markedOnePointLaw q A α)
    (hβ : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map markT =
      markedOnePointLaw q B β)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin m → Ω → Xs) (Y : Fin m → Ω → Yt)
    (hmeas : Measurable fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ))
    (hlaw : P.map (fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ)) =
      twoColourLaw μs μt m)
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hC : ∀ x y, |markedKineticKernel (q := q)
      ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin markS markT x y| ≤ C)
    (hG : ∀ x y, |markedProbeKernel g markS markT x y| ≤ G) :
    ∫ ξ, frozenModelTileBlock labS labT
        (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ)
          kin markS markT)
        (markedProbeKernel g markS markT) t c (fun i => X i ξ, fun j => Y j ξ) ∂P
      = modelBlockSum q t kin g α β w m := by
  classical
  have hρs : μs (labS ⁻¹' {c}) ≠ 0 := by
    rw [hws]
    exact ne_of_gt ((ENNReal.ofReal_pos).mpr hwpos)
  have hρt : μt (labT ⁻¹' {c}) ≠ 0 := by
    rw [hwt]
    exact ne_of_gt ((ENNReal.ofReal_pos).mpr hwpos)
  haveI : IsFiniteMeasure ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})) :=
    Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hρs)
  haveI : IsFiniteMeasure ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})) :=
    Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hρt)
  have hcost_meas : Measurable fun p : Xs × Yt =>
      markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ)
        kin markS markT p.1 p.2 :=
    measurable_markedKineticKernel hkin markS hmarkS markT hmarkT
  have hprobe_meas : Measurable fun p : Xs × Yt =>
      markedProbeKernel g markS markT p.1 p.2 :=
    measurable_markedProbeKernel hg markS hmarkS markT hmarkT
  exact integral_frozenModelTileBlock_eq_modelBlockSum hkin hg α β μs μt labS hS labT hT
    c m w hρs hρt markS hmarkS markT hmarkT hα hβ P X Y hmeas hlaw
    (fun a => pi_tileCountEqSet_toReal_eq_binomialMass μs labS hS c w hws a)
    (fun b => pi_tileCountEqSet_toReal_eq_binomialMass μt labT hT c w hwt b)
    (integrable_frozenModelTileBlock_of_bounds labS hS labT hT _ _ hcost_meas hprobe_meas t c
      hC0 hG0 hC hG (twoColourLaw μs μt m))
    (fun a b σ τ => integrable_frozenPatternBlock_comp_of_bounds _ _
      hcost_meas hprobe_meas t hC0 hG0 hC hG
      (fun i => (tileEquiv σ.1 c (fun _ => a) σ.2 i).1)
      (fun j => (tileEquiv τ.1 c (fun _ => b) τ.2 j).1)
      (fun i => μs.restrict (labS ⁻¹' {σ.1 i}))
      (fun j => μt.restrict (labT ⁻¹' {τ.1 j})))
    (fun a b => integrable_frozenPatternBlock_comp_of_bounds _ _
      hcost_meas hprobe_meas t hC0 hG0 hC hG
      id id
      (fun _ => (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))
      (fun _ => (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})))

end OTSelector.Probability
