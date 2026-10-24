import OTSelector.Finite.MatchingTranspose
import OTSelector.Probability.TileCountBlockBridge

/-!
# Law comparison for the physical frozen tile block

This module composes the two-colour conditional-iid law of
`OTSelector.Probability.TileCountBlockBridge` with the physical frozen tile block,
toward the per-cell comparison `hblock` of `PhysicalUpperBoundAssembly`.

## Setting

The physical sample is a pair `(X · ξ, Y · ξ)` of iid tuples of common size `m`
with one-point laws `μs`, `μt`, together with measurable label maps
`labS : Xs → ι`, `labT : Yt → ι`.  The joint law hypothesis is
`P.map (fun ξ ↦ (X · ξ, Y · ξ)) = twoColourLaw μs μt m`.  A tile `c : ι` selects
the source points with `labS = c` and the target points with `labT = c`.

The frozen cost and probe are kernels `frozenCost modelProbe : Xs → Yt → ℝ` on
pairs of physical points.  The tile-`c` block value
`frozenModelTileBlock` is the maximum-cardinality matching value of the frozen
matrix restricted to the tile, enumerated by the pattern-dependent `tileEquiv`.

## Results

* `integral_comp_twoColourLaw`: the pushforward transfer from the physical
  sample law to `twoColourLaw`.
* `iUnion_twoColourPatternSet`, `pairwiseDisjoint_twoColourPatternSet`,
  `integral_twoColour_eq_sum_pattern`: the label patterns partition the sample
  space, so an integral is the sum of the pattern-restricted integrals.
* `frozenPatternBlock` and `frozenPatternBlock_perm`: the pattern-level tile
  block, invariant under re-enumeration of the tile points
  (`PartialMatching.maxCardValue_reindex`).
* `frozenModelTileBlock_eq_pattern`: on a label pattern the physical tile block
  is the pattern block applied to the tile points.
* `integral_frozenModelTileBlock_eq_countSum`: the exact random-count identity
  for the physical expectation (count weights left as the exact count-event
  probabilities).
* `markedKineticKernel`, `markedProbeKernel`, `frozenPatternBlock_markedKernel`,
  `integral_frozenPatternBlock_markedKernel_eq`: the marked-model identification
  of the pattern block and of its normalized tile integral (the latter is exactly
  `integral_tile_markedFixedBlock_eq` of `TileConditionalIIDLaw`).
* `integral_frozenModelTileBlock_eq_modelBlockSum`: the `hblock`-shaped model-sum
  identity, under the binomial count weights, the atlas pushforward hypotheses,
  and integrability (the zero-count terms vanish by
  `markedFixedBlockExpectation_eq_zero_of_left_zero`/`_right_zero`).

## Remaining gaps

The final theorem is the exact random-count identity with the marked model; the
only inputs not discharged here are the binomial count weights `hNs`, `hNt`
(another lane proves the exact binomial law) and the integrability hypotheses
`hF`, `hint`, `hintG` (which hold whenever the frozen kernels are bounded on the
tile marks).  Unlike the abstract model bridge, no permutation-invariance
hypothesis is needed: the frozen kernels act on point pairs, and the pattern
formula `frozenModelTileBlock_eq_pattern` is proved (the enumeration enters only
through the resulting tile tuples, and `frozenPatternBlock_perm` records the
invariance under re-enumeration).
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

section Transfer

/-- **Pushforward transfer to the two-colour law.**  If the joint law of the
sample `(X · ξ, Y · ξ)` is `twoColourLaw μs μt m`, then the expectation of any
function of the sample is its integral against `twoColourLaw`. -/
theorem integral_comp_twoColourLaw {m : ℕ} (μs : Measure Xs) [SigmaFinite μs]
    (μt : Measure Yt) [SigmaFinite μt] (P : Measure Ω)
    (X : Fin m → Ω → Xs) (Y : Fin m → Ω → Yt)
    (hmeas : Measurable fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ))
    (hlaw : P.map (fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ)) =
      twoColourLaw μs μt m)
    {F : (Fin m → Xs) × (Fin m → Yt) → ℝ}
    (hF : AEStronglyMeasurable F (twoColourLaw μs μt m)) :
    ∫ ξ, F (fun i => X i ξ, fun j => Y j ξ) ∂P =
      ∫ p, F p ∂(twoColourLaw μs μt m) := by
  rw [← hlaw]
  exact (integral_map hmeas.aemeasurable (hlaw.symm ▸ hF)).symm

end Transfer

section PatternPartition

/-- The label-pattern pairs cover the whole two-colour sample space. -/
theorem iUnion_twoColourPatternSet {m : ℕ} (labS : Xs → ι) (labT : Yt → ι) :
    (⋃ στ : (Fin m → ι) × (Fin m → ι),
      twoColourPatternSet labS labT στ.1 στ.2) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨(fun i => labS (p.1 i), fun j => labT (p.2 j)), ?_⟩
  simp only [twoColourPatternSet, Set.mem_prod]
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Distinct label-pattern pairs are disjoint. -/
theorem pairwiseDisjoint_twoColourPatternSet {m : ℕ} (labS : Xs → ι) (labT : Yt → ι) :
    Pairwise (Function.onFun Disjoint fun στ : (Fin m → ι) × (Fin m → ι) =>
      twoColourPatternSet labS labT στ.1 στ.2) := by
  rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ hne
  refine Set.disjoint_left.mpr fun p hp hp' => ?_
  simp only [twoColourPatternSet, Set.mem_prod] at hp hp'
  rcases eq_or_ne σ σ' with rfl | hσ
  · rcases eq_or_ne τ τ' with rfl | hτ
    · exact hne rfl
    · exact Set.disjoint_left.mp (pairwiseDisjoint_labelPatternSet labT hτ) hp.2 hp'.2
  · exact Set.disjoint_left.mp (pairwiseDisjoint_labelPatternSet labS hσ) hp.1 hp'.1

/-- **Pattern decomposition of an integral.**  An integrable function on the
two-colour sample space is the sum of its integrals over the label-pattern
pairs. -/
theorem integral_twoColour_eq_sum_pattern {m : ℕ} (μs : Measure Xs) [SigmaFinite μs]
    (μt : Measure Yt) [SigmaFinite μt] (labS : Xs → ι) (hS : Measurable labS)
    (labT : Yt → ι) (hT : Measurable labT)
    {F : (Fin m → Xs) × (Fin m → Yt) → ℝ}
    (hF : Integrable F (twoColourLaw μs μt m)) :
    ∫ p, F p ∂(twoColourLaw μs μt m) =
      ∑ στ : (Fin m → ι) × (Fin m → ι),
        ∫ p in twoColourPatternSet labS labT στ.1 στ.2, F p
          ∂(twoColourLaw μs μt m) := by
  have hms : ∀ στ : (Fin m → ι) × (Fin m → ι),
      MeasurableSet (twoColourPatternSet labS labT στ.1 στ.2) :=
    fun στ => measurableSet_twoColourPatternSet hS hT στ.1 στ.2
  have hd : Pairwise (Function.onFun Disjoint fun στ : (Fin m → ι) × (Fin m → ι) =>
      twoColourPatternSet labS labT στ.1 στ.2) :=
    pairwiseDisjoint_twoColourPatternSet labS labT
  have hfi : ∀ στ : (Fin m → ι) × (Fin m → ι),
      IntegrableOn F (twoColourPatternSet labS labT στ.1 στ.2)
        (twoColourLaw μs μt m) :=
    fun στ => hF.integrableOn
  have h := integral_iUnion_fintype (f := F) (μ := twoColourLaw μs μt m)
    (s := fun στ : (Fin m → ι) × (Fin m → ι) =>
      twoColourPatternSet labS labT στ.1 στ.2) hms hd hfi
  rw [iUnion_twoColourPatternSet, setIntegral_univ] at h
  exact h

end PatternPartition

section FrozenBlock

/-- The canonical enumeration of the tile `c` in a label array. -/
noncomputable def tileEmbedding {m : ℕ} (lab : Fin m → ι) (c : ι) :
    Fin (patternCount lab c) → Fin m :=
  fun i => (tileEquiv lab c (fun _ => patternCount lab c) rfl i).1

/-- The canonical embedding at a smaller index type agrees with the
pattern-dependent enumeration `tileEquiv`. -/
theorem tileEmbedding_cast_eq {m : ℕ} (lab : Fin m → ι) (c : ι) {a : ℕ}
    (h : patternCount lab c = a) (i : Fin a) :
    tileEmbedding lab c (Fin.cast h.symm i) =
      (tileEquiv lab c (fun _ => a) h i).1 := by
  cases h
  rfl

/-- The pattern-level tile block: the maximum-cardinality matching value of the
frozen matrix on the tile points, indexed directly by `Fin a` and `Fin b`. -/
noncomputable def frozenPatternBlock {a b : ℕ} (frozenCost modelProbe : Xs → Yt → ℝ)
    (t : ℝ) (u : Fin a → Xs) (v : Fin b → Yt) : ℝ :=
  PartialMatching.maxCardValue
    (fun i : Fin a => fun j : Fin b =>
      frozenCost (u i) (v j) + t * modelProbe (u i) (v j))

/-- **Permutation invariance of the pattern block.**  Re-enumerating the tile
points does not change the maximum-cardinality value. -/
theorem frozenPatternBlock_perm {a b : ℕ} (frozenCost modelProbe : Xs → Yt → ℝ)
    (t : ℝ) (e : Fin a ≃ Fin a) (e' : Fin b ≃ Fin b)
    (u : Fin a → Xs) (v : Fin b → Yt) :
    frozenPatternBlock frozenCost modelProbe t (fun i => u (e i)) (fun j => v (e' j)) =
      frozenPatternBlock frozenCost modelProbe t u v := by
  unfold frozenPatternBlock
  exact PartialMatching.maxCardValue_reindex
    (c := fun i j => frozenCost (u i) (v j) + t * modelProbe (u i) (v j))
    (e := e.symm) (f := e'.symm)

/-- The physical tile block of the frozen kernels: the maximum-cardinality value
of the submatrix whose rows and columns are labelled `c`, enumerated by the
canonical tile embeddings. -/
noncomputable def frozenModelTileBlock {m : ℕ} (labS : Xs → ι) (labT : Yt → ι)
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ) (c : ι)
    (p : (Fin m → Xs) × (Fin m → Yt)) : ℝ :=
  PartialMatching.maxCardValue
    (fun i : Fin (patternCount (fun k => labS (p.1 k)) c) =>
      fun j : Fin (patternCount (fun k => labT (p.2 k)) c) =>
        frozenCost (p.1 (tileEmbedding (fun k => labS (p.1 k)) c i))
            (p.2 (tileEmbedding (fun k => labT (p.2 k)) c j))
        + t * modelProbe (p.1 (tileEmbedding (fun k => labS (p.1 k)) c i))
            (p.2 (tileEmbedding (fun k => labT (p.2 k)) c j)))

/-- **Pattern formula for the physical tile block.**  On a label pattern pair
`(σ, τ)` with tile counts `(a, b)`, the physical tile block is the pattern block
applied to the tile points of the sample, read through the pattern-dependent
enumeration `tileEquiv`.

This is the precise sense in which the block is invariant under re-enumeration of
the tile points: the physical definition uses the canonical enumeration
`tileEmbedding`, and the pattern enumeration differs from it only by the
cardinality casts and proof arguments. -/
theorem frozenModelTileBlock_eq_pattern {m : ℕ} (labS : Xs → ι) (labT : Yt → ι)
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ) (c : ι)
    {σ τ : Fin m → ι} {a b : ℕ} (hσ : patternCount σ c = a) (hτ : patternCount τ c = b)
    (p : (Fin m → Xs) × (Fin m → Yt))
    (hpS : ∀ i, labS (p.1 i) = σ i) (hpT : ∀ j, labT (p.2 j) = τ j) :
    frozenModelTileBlock labS labT frozenCost modelProbe t c p =
      frozenPatternBlock frozenCost modelProbe t
        (fun i : Fin a => p.1 ((tileEquiv σ c (fun _ => a) hσ i)).1)
        (fun j : Fin b => p.2 ((tileEquiv τ c (fun _ => b) hτ j)).1) := by
  classical
  have hlabS : (fun k => labS (p.1 k)) = σ := funext hpS
  have hlabT : (fun k => labT (p.2 k)) = τ := funext hpT
  unfold frozenModelTileBlock frozenPatternBlock
  rw [hlabS, hlabT]
  rw [← PartialMatching.maxCardValue_reindex
    (c := fun i j =>
      frozenCost (p.1 (tileEmbedding σ c i)) (p.2 (tileEmbedding τ c j)) +
        t * modelProbe (p.1 (tileEmbedding σ c i)) (p.2 (tileEmbedding τ c j)))
    (e := finCongr hσ) (f := finCongr hτ)]
  congr 1
  funext i j
  simp only [finCongr_symm, finCongr_apply]
  rw [tileEmbedding_cast_eq σ c hσ i, tileEmbedding_cast_eq τ c hτ j]

end FrozenBlock

section CountRegrouping

/-- Grouping a sum over label arrays by the tile-`c` count. -/
theorem sum_by_patternCount {m : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin m → ι) → M) (c : ι) :
    (∑ σ : Fin m → ι, f σ) =
      ∑ a ∈ Finset.range (m + 1),
        ∑ σ : {σ : Fin m → ι // patternCount σ c = a}, f σ.1 := by
  classical
  have hmem : ∀ σ ∈ (Finset.univ : Finset (Fin m → ι)),
      patternCount σ c ∈ Finset.range (m + 1) := by
    intro σ _
    rw [Finset.mem_range]
    have hle : patternCount σ c ≤ m := by
      rw [← card_tileIndex]
      simpa using Fintype.card_subtype_le (fun i : Fin m => σ i = c)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmem f]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_subtype (p := fun σ : Fin m → ι => patternCount σ c = a)
    (Finset.univ.filter fun σ => patternCount σ c = a) (fun σ => by simp) f

/-- Grouping a double sum over pairs of label arrays by the source and target
tile-`c` counts. -/
theorem sum_pair_by_patternCount {m : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin m → ι) → (Fin m → ι) → M) (c : ι) :
    (∑ σ : Fin m → ι, ∑ τ : Fin m → ι, f σ τ) =
      ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
        ∑ σ : {σ : Fin m → ι // patternCount σ c = a},
          ∑ τ : {τ : Fin m → ι // patternCount τ c = b}, f σ.1 τ.1 := by
  classical
  rw [sum_by_patternCount (fun σ : Fin m → ι => ∑ τ : Fin m → ι, f σ τ) c]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hinner : (∑ σ : {σ : Fin m → ι // patternCount σ c = a},
        ∑ τ : Fin m → ι, f σ.1 τ) =
      ∑ σ : {σ : Fin m → ι // patternCount σ c = a},
        ∑ b ∈ Finset.range (m + 1),
          ∑ τ : {τ : Fin m → ι // patternCount τ c = b}, f σ.1 τ.1 :=
    Finset.sum_congr rfl fun σ _ => sum_by_patternCount (fun τ => f σ.1 τ) c
  rw [hinner, Finset.sum_comm]

end CountRegrouping

section PhysicalCountSum

/-- **Exact random-count identity for the physical frozen tile block.**  The
expectation of the physical tile-`c` block over the sample law is the double sum
over the source and target tile counts of the exact count-event probabilities
times the normalized tile integral of the pattern block. -/
theorem integral_frozenModelTileBlock_eq_countSum {m : ℕ} (μs : Measure Xs)
    [IsProbabilityMeasure μs] (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ) (c : ι)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin m → Ω → Xs) (Y : Fin m → Ω → Yt)
    (hmeas : Measurable fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ))
    (hlaw : P.map (fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ)) =
      twoColourLaw μs μt m)
    (hF : Integrable (fun p => frozenModelTileBlock labS labT frozenCost modelProbe t c p)
      (twoColourLaw μs μt m))
    (hρs : μs (labS ⁻¹' {c}) ≠ 0) (hρt : μt (labT ⁻¹' {c}) ≠ 0)
    (hint : ∀ (a b : ℕ) (σ : {σ : Fin m → ι // patternCount σ c = a})
        (τ : {τ : Fin m → ι // patternCount τ c = b}),
      Integrable (fun z : (Fin m → Xs) × (Fin m → Yt) =>
        frozenPatternBlock frozenCost modelProbe t
          (fun i : Fin a => z.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1)
          (fun j : Fin b => z.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1))
      ((Measure.pi (fun i : Fin m => μs.restrict (labS ⁻¹' {σ.1 i}))).prod
        (Measure.pi (fun j : Fin m => μt.restrict (labT ⁻¹' {τ.1 j})))))
    (hintG : ∀ (a b : ℕ),
      Integrable (fun p : (Fin a → Xs) × (Fin b → Yt) =>
        frozenPatternBlock frozenCost modelProbe t p.1 p.2)
      ((Measure.pi (fun _ : Fin a =>
          (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
        (Measure.pi (fun _ : Fin b =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) :
    ∫ ξ, frozenModelTileBlock labS labT frozenCost modelProbe t c
        (fun i => X i ξ, fun j => Y j ξ) ∂P =
      ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
        ((Measure.pi (fun _ : Fin m => μs)) (tileCountEqSet labS c a)).toReal *
          ((Measure.pi (fun _ : Fin m => μt)) (tileCountEqSet labT c b)).toReal *
          ∫ p : (Fin a → Xs) × (Fin b → Yt),
            frozenPatternBlock frozenCost modelProbe t p.1 p.2
            ∂((Measure.pi (fun _ : Fin a =>
                  (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
              (Measure.pi (fun _ : Fin b =>
                  (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})))) := by
  classical
  rw [integral_comp_twoColourLaw μs μt P X Y hmeas hlaw hF.aestronglyMeasurable]
  rw [integral_twoColour_eq_sum_pattern μs μt labS hS labT hT hF]
  have hprod : (∑ στ : (Fin m → ι) × (Fin m → ι),
        ∫ p in twoColourPatternSet labS labT στ.1 στ.2,
          frozenModelTileBlock labS labT frozenCost modelProbe t c p
          ∂(twoColourLaw μs μt m)) =
      ∑ σ : Fin m → ι, ∑ τ : Fin m → ι,
        ∫ p in twoColourPatternSet labS labT σ τ,
          frozenModelTileBlock labS labT frozenCost modelProbe t c p
          ∂(twoColourLaw μs μt m) := by
    rw [← Finset.sum_product']
    simp
  rw [hprod]
  rw [sum_pair_by_patternCount
    (fun σ τ => ∫ p in twoColourPatternSet labS labT σ τ,
      frozenModelTileBlock labS labT frozenCost modelProbe t c p
      ∂(twoColourLaw μs μt m)) c]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hstep : (∑ σ : {σ : Fin m → ι // patternCount σ c = a},
        ∑ τ : {τ : Fin m → ι // patternCount τ c = b},
          ∫ p in twoColourPatternSet labS labT σ.1 τ.1,
            frozenModelTileBlock labS labT frozenCost modelProbe t c p
            ∂(twoColourLaw μs μt m)) =
      ∑ σ : {σ : Fin m → ι // patternCount σ c = a},
        ∑ τ : {τ : Fin m → ι // patternCount τ c = b},
          ∫ p in twoColourPatternSet labS labT σ.1 τ.1,
            frozenPatternBlock frozenCost modelProbe t
              (fun i : Fin a => p.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1)
              (fun j : Fin b => p.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1)
            ∂(twoColourLaw μs μt m) := by
    refine Finset.sum_congr rfl fun σ_1 _ => Finset.sum_congr rfl fun τ _ => ?_
    exact setIntegral_congr_fun (measurableSet_twoColourPatternSet hS hT σ_1.1 τ.1)
      (fun p hp => frozenModelTileBlock_eq_pattern labS labT frozenCost modelProbe t c
        σ_1.2 τ.2 p hp.1 hp.2)
  rw [hstep]
  exact sum_integral_twoColour_pattern_tile_eq_countWeight μs μt labS hS labT hT c a b
    hρs hρt (frozenPatternBlock frozenCost modelProbe t) (hint a b) (hintG a b)

end PhysicalCountSum

section MarkedKernels

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The kinetic kernel induced by the marked points: the frozen cost of a source
point `x` and a target point `y` is the marked kinetic cost of their marks. -/
noncomputable def markedKineticKernel {q : ℕ} (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (x : Xs) (y : Yt) : ℝ :=
  r ^ (2 / (q : ℝ)) * kin (markS x).2 (markT y).2
    (mDisplacement (markS x).1 (markT y).1)

/-- The probe kernel induced by the marked points. -/
def markedProbeKernel (g : A → B → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (x : Xs) (y : Yt) : ℝ :=
  g (markS x).2 (markT y).2

/-- **The pattern block of the marked kernels is the marked fixed block value.**
Marking the tile points and computing the frozen maximum-cardinality value gives
the marked fixed-block value of the resulting marked cloud. -/
theorem frozenPatternBlock_markedKernel {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (u : Fin a → Xs) (v : Fin b → Yt) :
    frozenPatternBlock (markedKineticKernel (q := q) r kin markS markT)
        (markedProbeKernel g markS markT) t u v =
      markedFixedBlockValue q r t kin g a b
        ((0, markedExtend a ha (fun i => markS (u i))),
         (0, markedExtend b hb (fun j => markT (v j)))) := by
  unfold frozenPatternBlock markedFixedBlockValue markedEdgeCost
  congr 1
  funext i j
  unfold markedKineticKernel markedProbeKernel mKineticCost mProbe
    mSourcePoint mSourceMark mTargetPoint mTargetMark
  simp only [markedExtend, dite_eq_left i.2, dite_eq_left j.2, Fin.eta, id_eq]

/-- The empty source tile has block value zero. -/
theorem frozenPatternBlock_eq_zero_of_left_zero {b : ℕ}
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ)
    (u : Fin 0 → Xs) (v : Fin b → Yt) :
    frozenPatternBlock frozenCost modelProbe t u v = 0 := by
  unfold frozenPatternBlock
  exact PartialMatching.maxCardValue_of_empty_rows _

/-- The empty target tile has block value zero. -/
theorem frozenPatternBlock_eq_zero_of_right_zero {a : ℕ}
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ)
    (u : Fin a → Xs) (v : Fin 0 → Yt) :
    frozenPatternBlock frozenCost modelProbe t u v = 0 := by
  unfold frozenPatternBlock
  exact PartialMatching.maxCardValue_of_empty_cols _

/-- The empty source tile has marked expectation zero. -/
theorem markedFixedBlockExpectation_eq_zero_of_left_zero {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (b : ℕ) :
    markedFixedBlockExpectation q r t kin g α β R 0 b = 0 := by
  unfold markedFixedBlockExpectation
  have hfun : markedFixedBlockValue q r t kin g 0 b = fun _ => (0 : ℝ) := by
    funext ω
    unfold markedFixedBlockValue
    exact PartialMatching.maxCardValue_of_empty_rows _
  rw [hfun]
  simp

/-- The empty target tile has marked expectation zero. -/
theorem markedFixedBlockExpectation_eq_zero_of_right_zero {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (a : ℕ) :
    markedFixedBlockExpectation q r t kin g α β R a 0 = 0 := by
  unfold markedFixedBlockExpectation
  have hfun : markedFixedBlockValue q r t kin g a 0 = fun _ => (0 : ℝ) := by
    funext ω
    unfold markedFixedBlockValue
    exact PartialMatching.maxCardValue_of_empty_cols _
  rw [hfun]
  simp

/-- **Normalized marked-kernel tile integral.**  Under the atlas identifications
of the normalized physical tile laws with the marked one-point laws, the
normalized tile integral of the marked-kernel pattern block is exactly the marked
fixed-block expectation. -/
theorem integral_frozenPatternBlock_markedKernel_eq {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (νs : Measure Xs) [IsProbabilityMeasure νs]
    (νt : Measure Yt) [IsProbabilityMeasure νt]
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT)
    (hα : νs.map markS = markedOnePointLaw q A α)
    (hβ : νt.map markT = markedOnePointLaw q B β)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∫ p : (Fin a → Xs) × (Fin b → Yt),
        frozenPatternBlock (markedKineticKernel (q := q) r kin markS markT)
          (markedProbeKernel g markS markT) t p.1 p.2
        ∂((Measure.pi (fun _ : Fin a => νs)).prod (Measure.pi (fun _ : Fin b => νt)))
      = markedFixedBlockExpectation q r t kin g α β R a b := by
  have hfun : (fun p : (Fin a → Xs) × (Fin b → Yt) =>
        frozenPatternBlock (markedKineticKernel (q := q) r kin markS markT)
          (markedProbeKernel g markS markT) t p.1 p.2) =
      (fun p : (Fin a → Xs) × (Fin b → Yt) =>
        markedFixedBlockValue q r t kin g a b
          ((0, markedExtend a ha (fun i => markS (p.1 i))),
           (0, markedExtend b hb (fun j => markT (p.2 j))))) := by
    funext p
    exact frozenPatternBlock_markedKernel markS markT ha hb p.1 p.2
  rw [hfun]
  exact integral_tile_markedFixedBlock_eq hkin hg α β R νs νt markS hmarkS markT hmarkT
    hα hβ a b ha hb

/-- **`hblock`-shaped model-sum identity for the physical frozen tile block.**
For two-colour iid physical samples with joint law `twoColourLaw μs μt m`, the
expectation of the physical tile-`c` block built from the marked kernels equals
the marked model block sum `modelBlockSum q t kin g α β w m`.

The hypotheses are:

* `hmeas`, `hlaw`: the physical sample law transfer;
* `hNs`, `hNt`: the binomial count weights of the tile labels;
* `hα`, `hβ`: the atlas identifications of the normalized tile laws with the
  marked one-point laws;
* `hF`, `hint`, `hintG`: integrability of the physical block and of the pattern
  and normalized pattern blocks.

The exact count-weighted identity without the binomial weights is
`integral_frozenModelTileBlock_eq_countSum`. -/
theorem integral_frozenModelTileBlock_eq_modelBlockSum {q : ℕ} {t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (c : ι) (m : ℕ) (w : unitInterval)
    (hρs : μs (labS ⁻¹' {c}) ≠ 0) (hρt : μt (labT ⁻¹' {c}) ≠ 0)
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
    (hNs : ∀ a, ((Measure.pi (fun _ : Fin m => μs)) (tileCountEqSet labS c a)).toReal =
      binomialMass m w a)
    (hNt : ∀ b, ((Measure.pi (fun _ : Fin m => μt)) (tileCountEqSet labT c b)).toReal =
      binomialMass m w b)
    (hF : Integrable (fun p =>
        frozenModelTileBlock labS labT
          (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin markS markT)
          (markedProbeKernel g markS markT) t c p)
      (twoColourLaw μs μt m))
    (hint : ∀ (a b : ℕ) (σ : {σ : Fin m → ι // patternCount σ c = a})
        (τ : {τ : Fin m → ι // patternCount τ c = b}),
      Integrable (fun z : (Fin m → Xs) × (Fin m → Yt) =>
        frozenPatternBlock
          (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin markS markT)
          (markedProbeKernel g markS markT) t
          (fun i : Fin a => z.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1)
          (fun j : Fin b => z.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1))
      ((Measure.pi (fun i : Fin m => μs.restrict (labS ⁻¹' {σ.1 i}))).prod
        (Measure.pi (fun j : Fin m => μt.restrict (labT ⁻¹' {τ.1 j})))))
    (hintG : ∀ (a b : ℕ),
      Integrable (fun p : (Fin a → Xs) × (Fin b → Yt) =>
        frozenPatternBlock
          (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin markS markT)
          (markedProbeKernel g markS markT) t p.1 p.2)
      ((Measure.pi (fun _ : Fin a =>
          (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
        (Measure.pi (fun _ : Fin b =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) :
    ∫ ξ, frozenModelTileBlock labS labT
        (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin markS markT)
        (markedProbeKernel g markS markT) t c (fun i => X i ξ, fun j => Y j ξ) ∂P
      = modelBlockSum q t kin g α β w m := by
  classical
  haveI : IsProbabilityMeasure ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})) :=
    isProbabilityMeasure_inv_smul_restrict μs hρs
  haveI : IsProbabilityMeasure ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})) :=
    isProbabilityMeasure_inv_smul_restrict μt hρt
  rw [integral_frozenModelTileBlock_eq_countSum μs μt labS hS labT hT
    (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin markS markT)
    (markedProbeKernel g markS markT) t c P X Y hmeas hlaw hF hρs hρt hint hintG]
  rw [modelBlockSum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases ha : a = 0
  · subst ha
    have hz : (∫ p : (Fin 0 → Xs) × (Fin b → Yt),
          frozenPatternBlock
            (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin markS markT)
            (markedProbeKernel g markS markT) t p.1 p.2
          ∂((Measure.pi (fun _ : Fin 0 =>
                (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
              (Measure.pi (fun _ : Fin b =>
                (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) = 0 := by
      rw [show (fun p : (Fin 0 → Xs) × (Fin b → Yt) =>
            frozenPatternBlock
              (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ)
                kin markS markT)
              (markedProbeKernel g markS markT) t p.1 p.2)
          = fun _ => 0 from funext fun p =>
            frozenPatternBlock_eq_zero_of_left_zero _ _ t p.1 p.2]
      simp
    rw [hz, markedFixedBlockExpectation_eq_zero_of_left_zero α β _ b]
    simp
  · by_cases hb : b = 0
    · subst hb
      have hz : (∫ p : (Fin a → Xs) × (Fin 0 → Yt),
            frozenPatternBlock
              (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ)
                kin markS markT)
              (markedProbeKernel g markS markT) t p.1 p.2
            ∂((Measure.pi (fun _ : Fin a =>
                  (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
                (Measure.pi (fun _ : Fin 0 =>
                  (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) = 0 := by
        rw [show (fun p : (Fin a → Xs) × (Fin 0 → Yt) =>
              frozenPatternBlock
                (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ)
                  kin markS markT)
                (markedProbeKernel g markS markT) t p.1 p.2)
            = fun _ => 0 from funext fun p =>
              frozenPatternBlock_eq_zero_of_right_zero _ _ t p.1 p.2]
        simp
      rw [hz, markedFixedBlockExpectation_eq_zero_of_right_zero α β _ a]
      simp
    · have ha' : 0 < a := Nat.pos_of_ne_zero ha
      have hb' : 0 < b := Nat.pos_of_ne_zero hb
      rw [integral_frozenPatternBlock_markedKernel_eq hkin hg α β
        ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0)
        ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))
        ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))
        markS hmarkS markT hmarkT hα hβ ha' hb',
        hNs a, hNt b]

end MarkedKernels

end OTSelector.Probability
