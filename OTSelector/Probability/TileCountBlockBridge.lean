import OTSelector.Probability.TileConditionalIIDLaw
import OTSelector.Probability.PhysicalUpperBoundAssembly

/-!
# Two-colour count-summed tile block bridge

This module assembles the law half of the per-cell block comparison `hblock` from
`OTSelector.Probability.PhysicalUpperBoundAssembly`, using the one-colour
conditional-iid theorems of `OTSelector.Probability.TileConditionalIIDLaw`.

## Setting

Two colours of iid samples of common size `n` live on the canonical product space
`(Fin n → Xs) × (Fin n → Yt)` with law
`twoColourLaw μs μt n = (Measure.pi (fun _ : Fin n ↦ μs)).prod (Measure.pi (fun _ : Fin n ↦ μt))`.
The colour label maps are `labS : Xs → ι` and `labT : Yt → ι`; the block of a tile
`c : ι` reads the source points with `labS = c` and the target points with `labT = c`.
The source and target tile counts are the independent single-colour counts
`#{i | labS (xs i) = c}` and `#{j | labT (yt j) = c}`.

## Results

* `integral_prod_tile_factor`: two-variable block factorization of a product of
  product measures (the source-block and target-block coordinates are split off).

* `integral_twoColour_pattern_tile_eq_fin`: given the source and target label
  patterns `σ`, `τ` with tile counts `a`, `b`, the integral of a block function of
  the tile blocks is the product of the two pattern probabilities times the
  integral against the normalized product of the two tile laws.

* `tileCountEqSet` / `measure_tileCountEqSet_eq_tsum`: the single-tile count event
  is the disjoint union of the patterns with the corresponding tile count, so its
  mass is the sum of their masses.

* `sum_integral_twoColour_tile_eq_countWeight`: summing over all source and target
  patterns with tile counts `a`, `b` gives
  `P(Ns = a) · P(Nt = b) · ∫ (normalized source tile)^{⊗ a} × (normalized target tile)^{⊗ b}`.

* `integral_twoColour_tile_markedFixedBlock_eq`: under the atlas identifications
  `νs.map markS = markedOnePointLaw q A α`, `νt.map markT = markedOnePointLaw q B β`,
  the fixed-count normalized integral is `markedFixedBlockExpectation q r t kin g α β R a b`.

* `sum_integral_twoColour_tile_eq_countWeight_marked`: the combined count-summed
  marked-model identity.

* `sum_integral_twoColour_tile_eq_modelBlockSum_marked`: the `hblock` model-sum
  bridge, identifying the positive-count double sum with the actual
  `modelBlockSum q t kin g α β w n` of `PhysicalUpperBoundAssembly`, given the
  binomial count weights, the vanishing of the empty block, and integrability.

## Relation to `hblock`

`modelBlockSum q t kin g α β w n` in `PhysicalUpperBoundAssembly` is exactly
`∑ a, ∑ b, binomialMass n w a * binomialMass n w b * markedFixedBlockExpectation … a b`.
`sum_integral_twoColour_tile_eq_countWeight_marked` proves the same double sum with
the count weights left as the exact count-event probabilities
`P(Ns = a) * P(Nt = b)`; identifying those with `binomialMass` is the separate
count-law lane and enters
`sum_integral_twoColour_tile_eq_modelBlockSum_marked` as the explicit hypothesis
`hNs`/`hNt`.

The remaining gaps for the literal `hblock` statement are:

* the count law `P(N = a) = binomialMass n w a` (hypotheses `hNs`, `hNt`);
* the identification of the physical block integral with the pattern sum: the
  block integrand is read off through the pattern-dependent tile enumeration
  `tileEquiv`, so one needs permutation invariance of the block under
  re-enumeration of the tile points, together with the physical iid transfer from
  the sample law to `twoColourLaw μs μt n`;
* vanishing of the marked block expectation at zero counts (the empty block), and
  integrability of the marked block value on the pattern and normalized tile
  measures (`hint`, `hintG`).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

variable {Xs Yt : Type*} [MeasurableSpace Xs] [MeasurableSpace Yt]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

section TwoColourSetup

/-- The iid law of a two-colour sample of common size `n`. -/
noncomputable def twoColourLaw (μs : Measure Xs) [SigmaFinite μs]
    (μt : Measure Yt) [SigmaFinite μt] (n : ℕ) :
    Measure ((Fin n → Xs) × (Fin n → Yt)) :=
  (Measure.pi (fun _ : Fin n => μs)).prod (Measure.pi (fun _ : Fin n => μt))

instance twoColourLaw_isProbabilityMeasure (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt] (n : ℕ) :
    IsProbabilityMeasure (twoColourLaw μs μt n) := by
  unfold twoColourLaw
  infer_instance

/-- The event that the source pattern is `σ` and the target pattern is `τ`. -/
def twoColourPatternSet {n : ℕ} (labS : Xs → ι) (labT : Yt → ι)
    (σ τ : Fin n → ι) : Set ((Fin n → Xs) × (Fin n → Yt)) :=
  labelPatternSet labS σ ×ˢ labelPatternSet labT τ

/-- The pattern-pair event is measurable. -/
theorem measurableSet_twoColourPatternSet {n : ℕ} {labS : Xs → ι} {labT : Yt → ι}
    (hS : Measurable labS) (hT : Measurable labT) (σ τ : Fin n → ι) :
    MeasurableSet (twoColourPatternSet labS labT σ τ) :=
  (measurableSet_labelPatternSet hS σ).prod (measurableSet_labelPatternSet hT τ)

/-- The pattern-pair probability is the product of the two pattern probabilities. -/
theorem measure_twoColourPatternSet {n : ℕ} (μs : Measure Xs) [SigmaFinite μs]
    (μt : Measure Yt) [SigmaFinite μt] (labS : Xs → ι) (labT : Yt → ι)
    (σ τ : Fin n → ι) :
    twoColourLaw μs μt n (twoColourPatternSet labS labT σ τ) =
      (Measure.pi (fun _ : Fin n => μs)) (labelPatternSet labS σ) *
        (Measure.pi (fun _ : Fin n => μt)) (labelPatternSet labT τ) := by
  rw [twoColourLaw, twoColourPatternSet, Measure.prod_prod]

/-- Restricting the two-colour law to a pattern pair gives the product of the two
coordinatewise restricted laws. -/
theorem restrict_twoColourPatternSet {n : ℕ} (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt] (labS : Xs → ι) (labT : Yt → ι)
    (σ τ : Fin n → ι) :
    (twoColourLaw μs μt n).restrict (twoColourPatternSet labS labT σ τ) =
      (Measure.pi (fun i : Fin n => μs.restrict (labS ⁻¹' {σ i}))).prod
        (Measure.pi (fun j : Fin n => μt.restrict (labT ⁻¹' {τ j}))) := by
  rw [twoColourLaw, twoColourPatternSet, prod_restrict_prod, restrict_labelPatternSet,
    restrict_labelPatternSet]

/-- The event that the tile-`c` count of a single-colour sample equals `a`. -/
def tileCountEqSet {n : ℕ} (lab : Xs → ι) (c : ι) (a : ℕ) : Set (Fin n → Xs) :=
  {x | tileCount lab x c = a}

end TwoColourSetup

section CountSet

/-- The single-tile count event is the union of the patterns with the prescribed
tile count. -/
theorem tileCountEqSet_eq_iUnion_pattern {n : ℕ} (lab : Xs → ι) (c : ι) (a : ℕ) :
    tileCountEqSet lab c a =
      ⋃ σ : {σ : Fin n → ι // patternCount σ c = a}, labelPatternSet lab σ.1 := by
  ext x
  simp only [tileCountEqSet, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hx
    refine ⟨⟨fun i => lab (x i), ?_⟩, fun _ => rfl⟩
    rw [← tileCount_eq_patternCount_of_mem (σ := fun i => lab (x i)) (x := x)
      (fun _ => rfl) c]
    exact hx
  · rintro ⟨σ, hx⟩
    rw [tileCount_eq_patternCount_of_mem hx, σ.2]

/-- The single-tile count event is measurable. -/
theorem measurableSet_tileCountEqSet {n : ℕ} {lab : Xs → ι} (hlab : Measurable lab)
    (c : ι) (a : ℕ) : MeasurableSet (tileCountEqSet (n := n) lab c a) :=
  (measurable_tileCount (X := Xs) hlab c) (measurableSet_singleton a)

/-- The mass of the single-tile count event is the sum of the pattern masses. -/
theorem measure_tileCountEqSet_eq_tsum {n : ℕ} (μ : Measure Xs) [IsProbabilityMeasure μ]
    (lab : Xs → ι) (hlab : Measurable lab) (c : ι) (a : ℕ) :
    (Measure.pi (fun _ : Fin n => μ)) (tileCountEqSet lab c a) =
      ∑' σ : {σ : Fin n → ι // patternCount σ c = a},
        (Measure.pi (fun _ : Fin n => μ)) (labelPatternSet lab σ.1) := by
  rw [tileCountEqSet_eq_iUnion_pattern]
  exact measure_iUnion
    (fun σ σ' hne => pairwiseDisjoint_labelPatternSet lab (fun h => hne (Subtype.ext h)))
    (fun σ => measurableSet_labelPatternSet hlab σ.1)

end CountSet

section Scaling

/-- Scaling of a product of two scaled measures. -/
theorem integral_prod_smul_smul {κ : Measure Xs} [SFinite κ] {ρ : Measure Yt} [SFinite ρ]
    (a b : ℝ≥0∞) (F : Xs × Yt → ℝ) :
    ∫ z, F z ∂((a • κ).prod (b • ρ)) = (a * b).toReal * ∫ z, F z ∂(κ.prod ρ) := by
  have h : (a • κ).prod (b • ρ) = (a * b) • (κ.prod ρ) := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [h, integral_smul_measure, smul_eq_mul]

/-- A constant product measure is the normalized product scaled by the total mass
to the power of the index cardinality. -/
theorem pi_const_eq_smul_normalized {δ : Type*} [Fintype δ] (ρ : Measure Xs)
    [IsFiniteMeasure ρ] (hρ : ρ univ ≠ 0) :
    Measure.pi (fun _ : δ => ρ) =
      (ρ univ) ^ Fintype.card δ • Measure.pi (fun _ : δ => (ρ univ)⁻¹ • ρ) := by
  haveI : IsFiniteMeasure ((ρ univ)⁻¹ • ρ) :=
    Measure.smul_finite ρ (ENNReal.inv_ne_top.mpr hρ)
  have hρ' : (ρ univ) • ((ρ univ)⁻¹ • ρ) = ρ := by
    rw [smul_smul, ENNReal.mul_inv_cancel hρ (measure_ne_top ρ univ), one_smul]
  have h2 := pi_const_smul (δ := δ) ((ρ univ)⁻¹ • ρ) (ρ univ) (measure_ne_top ρ univ)
  rwa [hρ'] at h2

end Scaling

section TileFactorization

/-- **Two-variable block factorization.**  If a function of the source block
selected by `p` and the target block selected by `q` is integrable, its integral
against the product of the two product measures is the integral over the two
selected blocks times the masses of the two complementary blocks. -/
theorem integral_prod_tile_factor {δ κ : Type*} [Fintype δ] [Fintype κ]
    (νs : δ → Measure Xs) [∀ i, SigmaFinite (νs i)]
    (νt : κ → Measure Yt) [∀ i, SigmaFinite (νt i)]
    (p : δ → Prop) [DecidablePred p] (q : κ → Prop) [DecidablePred q]
    (G : ({i // p i} → Xs) → ({j // q j} → Yt) → ℝ)
    (hint : Integrable (fun z : (δ → Xs) × (κ → Yt) =>
        G (fun i => z.1 i.1) (fun j => z.2 j.1))
      ((Measure.pi νs).prod (Measure.pi νt))) :
    ∫ z : (δ → Xs) × (κ → Yt), G (fun i => z.1 i.1) (fun j => z.2 j.1)
        ∂((Measure.pi νs).prod (Measure.pi νt))
      = (∫ a : ({i // p i} → Xs), ∫ b : ({j // q j} → Yt), G a b
          ∂(Measure.pi fun j : {j // q j} => νt j)
          ∂(Measure.pi fun i : {i // p i} => νs i)) *
        ((Measure.pi fun i : {i // ¬p i} => νs i) Set.univ).toReal *
        ((Measure.pi fun j : {j // ¬q j} => νt j) Set.univ).toReal := by
  rw [integral_prod _ hint]
  have hinner : ∀ zs : δ → Xs,
      (∫ zt : κ → Yt, G (fun i : {i // p i} => zs i.1) (fun j : {j // q j} => zt j.1)
        ∂(Measure.pi νt))
      = (∫ b : ({j // q j} → Yt), G (fun i : {i // p i} => zs i.1) b
          ∂(Measure.pi fun j : {j // q j} => νt j)) *
        ((Measure.pi fun j : {j // ¬q j} => νt j) Set.univ).toReal :=
    fun zs => integral_pi_tile_factor νt q (fun b => G (fun i : {i // p i} => zs i.1) b)
  simp_rw [hinner]
  rw [integral_mul_const]
  rw [integral_pi_tile_factor νs p
    (fun a => ∫ b : ({j // q j} → Yt), G a b ∂(Measure.pi fun j : {j // q j} => νt j))]

end TileFactorization

section Reindex

/-- The constant product measure is invariant under a reindexing of its index type. -/
theorem map_pi_reindex_const {δ δ' : Type*} [Fintype δ] [Fintype δ']
    (e : δ' ≃ δ) (ρ : Measure Xs) [SigmaFinite ρ] :
    (Measure.pi (fun _ : δ => ρ)).map (fun z : δ → Xs => fun i : δ' => z (e i)) =
      Measure.pi (fun _ : δ' => ρ) := by
  have h := (measurePreserving_piCongrLeft (α := fun _ : δ => Xs)
    (μ := fun _ : δ => ρ) e).symm
  have hfun : (fun z : δ → Xs => (MeasurableEquiv.piCongrLeft (fun _ : δ => Xs) e).symm z)
      = fun z : δ → Xs => fun i : δ' => z (e i) := by
    funext z i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      Equiv.piCongrLeft'_apply]
  simpa only [hfun] using h.map_eq

/-- **Two-variable reindexing of constant product measures.** -/
theorem integral_prod_reindex_const {δ δ' κ κ' : Type*}
    [Fintype δ] [Fintype δ'] [Fintype κ] [Fintype κ']
    (e : δ' ≃ δ) (e' : κ' ≃ κ)
    (ρ : Measure Xs) [SigmaFinite ρ] (ρ' : Measure Yt) [SigmaFinite ρ']
    (G : (δ' → Xs) → (κ' → Yt) → ℝ) :
    ∫ p : (δ → Xs) × (κ → Yt), G (fun i => p.1 (e i)) (fun j => p.2 (e' j))
        ∂((Measure.pi (fun _ : δ => ρ)).prod (Measure.pi (fun _ : κ => ρ')))
      = ∫ p : (δ' → Xs) × (κ' → Yt), G p.1 p.2
        ∂((Measure.pi (fun _ : δ' => ρ)).prod (Measure.pi (fun _ : κ' => ρ'))) := by
  have h1 := (measurePreserving_piCongrLeft (α := fun _ : δ => Xs)
    (μ := fun _ : δ => ρ) e).symm
  have h2 := (measurePreserving_piCongrLeft (α := fun _ : κ => Yt)
    (μ := fun _ : κ => ρ') e').symm
  have hfun1 : (fun z : δ → Xs => (MeasurableEquiv.piCongrLeft (fun _ : δ => Xs) e).symm z)
      = fun z : δ → Xs => fun i : δ' => z (e i) := by
    funext z i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      Equiv.piCongrLeft'_apply]
  have hfun2 : (fun z : κ → Yt => (MeasurableEquiv.piCongrLeft (fun _ : κ => Yt) e').symm z)
      = fun z : κ → Yt => fun j : κ' => z (e' j) := by
    funext z j
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      Equiv.piCongrLeft'_apply]
  have hmp : MeasurePreserving
      ((MeasurableEquiv.piCongrLeft (fun _ : δ => Xs) e).symm.prodCongr
        (MeasurableEquiv.piCongrLeft (fun _ : κ => Yt) e').symm)
      ((Measure.pi (fun _ : δ => ρ)).prod (Measure.pi (fun _ : κ => ρ')))
      ((Measure.pi (fun _ : δ' => ρ)).prod (Measure.pi (fun _ : κ' => ρ'))) := by
    simpa [MeasurableEquiv.prodCongr] using h1.prod h2
  have h := hmp.integral_comp' (fun z : (δ' → Xs) × (κ' → Yt) => G z.1 z.2)
  simp only [MeasurableEquiv.prodCongr, Prod.map, hfun1, hfun2] at h
  exact h

end Reindex

section PatternPair

/-- **Two-colour pattern-conditional tile identity.**  On a fixed pair of label
patterns `σ`, `τ` with tile counts `a` (source) and `b` (target), the integral of a
block function of the two tile blocks is the product of the two pattern
probabilities times the integral against the product of the normalized tile laws. -/
theorem integral_twoColour_pattern_tile_eq_fin {n : ℕ} (μs : Measure Xs)
    [IsProbabilityMeasure μs] (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (labT : Yt → ι) (σ τ : Fin n → ι) (c : ι) (a b : ℕ)
    (hσ : patternCount σ c = a) (hτ : patternCount τ c = b)
    (hρs : μs (labS ⁻¹' {c}) ≠ 0) (hρt : μt (labT ⁻¹' {c}) ≠ 0)
    (G : (Fin a → Xs) → (Fin b → Yt) → ℝ)
    (hint : Integrable (fun z : (Fin n → Xs) × (Fin n → Yt) =>
        G (fun i : Fin a => z.1 ((tileEquiv σ c (fun _ => a) hσ i)).1)
          (fun j : Fin b => z.2 ((tileEquiv τ c (fun _ => b) hτ j)).1))
      ((Measure.pi (fun i : Fin n => μs.restrict (labS ⁻¹' {σ i}))).prod
        (Measure.pi (fun j : Fin n => μt.restrict (labT ⁻¹' {τ j})))))
    (hintG : Integrable (fun p : (Fin a → Xs) × (Fin b → Yt) => G p.1 p.2)
      ((Measure.pi (fun _ : Fin a =>
          (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
        (Measure.pi (fun _ : Fin b =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) :
    ∫ p in twoColourPatternSet labS labT σ τ,
        G (fun i : Fin a => p.1 ((tileEquiv σ c (fun _ => a) hσ i)).1)
          (fun j : Fin b => p.2 ((tileEquiv τ c (fun _ => b) hτ j)).1)
        ∂(twoColourLaw μs μt n)
      = ((Measure.pi (fun _ : Fin n => μs)) (labelPatternSet labS σ)).toReal *
        ((Measure.pi (fun _ : Fin n => μt)) (labelPatternSet labT τ)).toReal *
        ∫ p : (Fin a → Xs) × (Fin b → Yt), G p.1 p.2
          ∂((Measure.pi (fun _ : Fin a =>
              (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
            (Measure.pi (fun _ : Fin b =>
              (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})))) := by
  classical
  have hνs : (fun _ : tileIndex σ c => μs.restrict (labS ⁻¹' {c}))
      = (fun i : tileIndex σ c => μs.restrict (labS ⁻¹' {σ i.1})) := by
    funext i; rw [i.2]
  have hνt : (fun _ : tileIndex τ c => μt.restrict (labT ⁻¹' {c}))
      = (fun j : tileIndex τ c => μt.restrict (labT ⁻¹' {τ j.1})) := by
    funext j; rw [j.2]
  rw [restrict_twoColourPatternSet]
  have hfact := integral_prod_tile_factor
    (νs := fun i : Fin n => μs.restrict (labS ⁻¹' {σ i}))
    (νt := fun j : Fin n => μt.restrict (labT ⁻¹' {τ j}))
    (p := fun i => σ i = c) (q := fun j => τ j = c)
    (G := fun (u : tileIndex σ c → Xs) (v : tileIndex τ c → Yt) =>
      G (fun i : Fin a => u (tileEquiv σ c (fun _ => a) hσ i))
        (fun j : Fin b => v (tileEquiv τ c (fun _ => b) hτ j)))
    hint
  rw [hfact]
  have hρs' : (μs.restrict (labS ⁻¹' {c})) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]; exact hρs
  have hρt' : (μt.restrict (labT ⁻¹' {c})) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]; exact hρt
  have hps : Measure.pi (fun i : tileIndex σ c => μs.restrict (labS ⁻¹' {σ i.1}))
      = (μs (labS ⁻¹' {c})) ^ a • Measure.pi (fun _ : tileIndex σ c =>
          (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})) := by
    rw [← hνs, pi_const_eq_smul_normalized (μs.restrict (labS ⁻¹' {c})) hρs']
    simp only [Measure.restrict_apply_univ, card_tileIndex, hσ]
  have hpt : Measure.pi (fun j : tileIndex τ c => μt.restrict (labT ⁻¹' {τ j.1}))
      = (μt (labT ⁻¹' {c})) ^ b • Measure.pi (fun _ : tileIndex τ c =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})) := by
    rw [← hνt, pi_const_eq_smul_normalized (μt.restrict (labT ⁻¹' {c})) hρt']
    simp only [Measure.restrict_apply_univ, card_tileIndex, hτ]
  rw [hps, hpt]
  simp only [integral_smul_measure, smul_eq_mul]
  rw [integral_const_mul]
  haveI hSFin : SigmaFinite ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})) :=
    (Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hρs)).toSigmaFinite
  haveI hTFin : SigmaFinite ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})) :=
    (Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hρt)).toSigmaFinite
  have hinner2 : ∀ a_1 : tileIndex σ c → Xs,
      (∫ b_1 : tileIndex τ c → Yt,
        G (fun i : Fin a => a_1 (tileEquiv σ c (fun _ => a) hσ i))
          (fun j : Fin b => b_1 (tileEquiv τ c (fun _ => b) hτ j))
        ∂(Measure.pi (fun _ : tileIndex τ c =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))
      = ∫ z : (Fin b → Yt),
          G (fun i : Fin a => a_1 (tileEquiv σ c (fun _ => a) hσ i)) z
          ∂(Measure.pi (fun _ : Fin b => (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))) := by
    intro a_1
    exact integral_pi_reindex_const (e := tileEquiv τ c (fun _ => b) hτ)
      ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))
      (fun z => G (fun i : Fin a => a_1 (tileEquiv σ c (fun _ => a) hσ i)) z)
  simp_rw [hinner2]
  rw [integral_pi_reindex_const (e := tileEquiv σ c (fun _ => a) hσ)
    ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))
    (fun u => ∫ z : (Fin b → Yt), G u z
      ∂(Measure.pi (fun _ : Fin b => (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))]
  rw [← integral_prod (fun p : (Fin a → Xs) × (Fin b → Yt) => G p.1 p.2) hintG]
  rw [toReal_measure_labelPatternSet μs labS σ c,
    toReal_measure_labelPatternSet μt labT τ c, hσ, hτ]
  rw [ENNReal.toReal_pow, ENNReal.toReal_pow]
  simp only [Measure.real]
  ring

/-- **Count-summed two-colour tile identity.**  Summing the pattern-conditional
identity over all source patterns with tile count `a` and all target patterns with
tile count `b` gives the product of the two count weights times the integral
against the product of the normalized tile laws.

The left side is a sum over pattern pairs because the tile enumeration (and hence
the block integrand) depends on the pattern; on the count event the different
patterns' enumerations differ by a permutation of the tile points. -/
theorem sum_integral_twoColour_pattern_tile_eq_countWeight {n : ℕ} (μs : Measure Xs)
    [IsProbabilityMeasure μs] (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (c : ι) (a b : ℕ) (hρs : μs (labS ⁻¹' {c}) ≠ 0) (hρt : μt (labT ⁻¹' {c}) ≠ 0)
    (G : (Fin a → Xs) → (Fin b → Yt) → ℝ)
    (hint : ∀ (σ : {σ : Fin n → ι // patternCount σ c = a})
        (τ : {τ : Fin n → ι // patternCount τ c = b}),
      Integrable (fun z : (Fin n → Xs) × (Fin n → Yt) =>
        G (fun i : Fin a => z.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1)
          (fun j : Fin b => z.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1))
      ((Measure.pi (fun i : Fin n => μs.restrict (labS ⁻¹' {σ.1 i}))).prod
        (Measure.pi (fun j : Fin n => μt.restrict (labT ⁻¹' {τ.1 j})))))
    (hintG : Integrable (fun p : (Fin a → Xs) × (Fin b → Yt) => G p.1 p.2)
      ((Measure.pi (fun _ : Fin a =>
          (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
        (Measure.pi (fun _ : Fin b =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) :
    (∑ σ : {σ : Fin n → ι // patternCount σ c = a},
        ∑ τ : {τ : Fin n → ι // patternCount τ c = b},
          ∫ p in twoColourPatternSet labS labT σ.1 τ.1,
            G (fun i : Fin a => p.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1)
              (fun j : Fin b => p.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1)
            ∂(twoColourLaw μs μt n))
      = ((Measure.pi (fun _ : Fin n => μs)) (tileCountEqSet labS c a)).toReal *
        ((Measure.pi (fun _ : Fin n => μt)) (tileCountEqSet labT c b)).toReal *
        ∫ p : (Fin a → Xs) × (Fin b → Yt), G p.1 p.2
          ∂((Measure.pi (fun _ : Fin a =>
              (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
            (Measure.pi (fun _ : Fin b =>
              (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})))) := by
  classical
  have hterm : ∀ (σ : {σ : Fin n → ι // patternCount σ c = a})
      (τ : {τ : Fin n → ι // patternCount τ c = b}),
      (∫ p in twoColourPatternSet labS labT σ.1 τ.1,
          G (fun i : Fin a => p.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1)
            (fun j : Fin b => p.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1)
          ∂(twoColourLaw μs μt n)) =
        ((Measure.pi (fun _ : Fin n => μs)) (labelPatternSet labS σ.1)).toReal *
          ((Measure.pi (fun _ : Fin n => μt)) (labelPatternSet labT τ.1)).toReal *
          ∫ p : (Fin a → Xs) × (Fin b → Yt), G p.1 p.2
            ∂((Measure.pi (fun _ : Fin a =>
                (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
              (Measure.pi (fun _ : Fin b =>
                (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})))) :=
    fun σ τ => integral_twoColour_pattern_tile_eq_fin μs μt labS labT σ.1 τ.1 c a b
      σ.2 τ.2 hρs hρt G (hint σ τ) hintG
  simp_rw [hterm]
  have hstep1 : ∀ σ : {σ : Fin n → ι // patternCount σ c = a},
      (∑ τ : {τ : Fin n → ι // patternCount τ c = b},
        ((Measure.pi (fun _ : Fin n => μs)) (labelPatternSet labS σ.1)).toReal *
          ((Measure.pi (fun _ : Fin n => μt)) (labelPatternSet labT τ.1)).toReal *
          ∫ p : (Fin a → Xs) × (Fin b → Yt), G p.1 p.2
            ∂((Measure.pi (fun _ : Fin a =>
                (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
              (Measure.pi (fun _ : Fin b =>
                (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) =
      ((Measure.pi (fun _ : Fin n => μs)) (labelPatternSet labS σ.1)).toReal *
        (∑ τ : {τ : Fin n → ι // patternCount τ c = b},
          ((Measure.pi (fun _ : Fin n => μt)) (labelPatternSet labT τ.1)).toReal) *
        ∫ p : (Fin a → Xs) × (Fin b → Yt), G p.1 p.2
          ∂((Measure.pi (fun _ : Fin a =>
              (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
            (Measure.pi (fun _ : Fin b =>
              (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})))) := by
    intro σ
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [hstep1]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hs : (∑ σ : {σ : Fin n → ι // patternCount σ c = a},
      ((Measure.pi (fun _ : Fin n => μs)) (labelPatternSet labS σ.1)).toReal) =
      ((Measure.pi (fun _ : Fin n => μs)) (tileCountEqSet labS c a)).toReal := by
    rw [← ENNReal.toReal_sum (fun σ (_ : σ ∈ Finset.univ) => measure_ne_top _ _)]
    congr 1
    have h := measure_tileCountEqSet_eq_tsum (n := n) μs labS hS c a
    rw [tsum_fintype] at h
    exact h.symm
  have ht : (∑ τ : {τ : Fin n → ι // patternCount τ c = b},
      ((Measure.pi (fun _ : Fin n => μt)) (labelPatternSet labT τ.1)).toReal) =
      ((Measure.pi (fun _ : Fin n => μt)) (tileCountEqSet labT c b)).toReal := by
    rw [← ENNReal.toReal_sum (fun τ (_ : τ ∈ Finset.univ) => measure_ne_top _ _)]
    congr 1
    have h := measure_tileCountEqSet_eq_tsum (n := n) μt labT hT c b
    rw [tsum_fintype] at h
    exact h.symm
  rw [hs, ht]

end PatternPair

section MarkedBridge

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The normalized restriction of a probability measure to a positive-measure set is
a probability measure. -/
theorem isProbabilityMeasure_inv_smul_restrict (μ : Measure Xs) [IsProbabilityMeasure μ]
    {s : Set Xs} (hs : μ s ≠ 0) :
    IsProbabilityMeasure ((μ s)⁻¹ • μ.restrict s) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel hs (measure_ne_top μ s)]

/-- **Fixed-count marked-model identification.**  When the normalized source tile
law pushes forward under `markS` to the marked one-point law `(cubeMeasure (Fin q) 1).prod α`
(and likewise for the target), the normalized tile integral of the marked block value
is exactly `markedFixedBlockExpectation q r t kin g α β R a b`. -/
theorem integral_twoColour_tile_markedFixedBlock_eq {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (labT : Yt → ι) (c : ι) (a b : ℕ)
    (hρs : μs (labS ⁻¹' {c}) ≠ 0) (hρt : μt (labT ⁻¹' {c}) ≠ 0)
    (ha : 0 < a) (hb : 0 < b)
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT)
    (hα : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map markS =
      markedOnePointLaw q A α)
    (hβ : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map markT =
      markedOnePointLaw q B β) :
    ∫ p : (Fin a → Xs) × (Fin b → Yt),
        markedFixedBlockValue q r t kin g a b
          ((0, markedExtend a ha (fun i => markS (p.1 i))),
           (0, markedExtend b hb (fun j => markT (p.2 j))))
        ∂((Measure.pi (fun _ : Fin a =>
            (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
          (Measure.pi (fun _ : Fin b =>
            (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))
      = markedFixedBlockExpectation q r t kin g α β R a b := by
  haveI := isProbabilityMeasure_inv_smul_restrict μs hρs
  haveI := isProbabilityMeasure_inv_smul_restrict μt hρt
  exact integral_tile_markedFixedBlock_eq (q := q) (r := r) (t := t) hkin hg α β R
    ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))
    ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))
    markS hmarkS markT hmarkT hα hβ a b ha hb

/-- **Count-summed marked block identity.**  The double sum over source and target
label patterns of the pattern-conditional integral of the marked block value is the
product of the two count-event probabilities times the marked fixed-block
expectation at the tile counts.

This is the exact random-count form of the `hblock` comparison: the only inputs are
the atlas identifications `hα`, `hβ` and the integrability of the (bounded, in the
intended application) marked block value on the pattern and normalized tile
measures. -/
theorem sum_integral_twoColour_tile_eq_countWeight_marked {q : ℕ} {r t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (R : ℝ≥0) (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (c : ι) (a b : ℕ) (hρs : μs (labS ⁻¹' {c}) ≠ 0) (hρt : μt (labT ⁻¹' {c}) ≠ 0)
    (ha : 0 < a) (hb : 0 < b)
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT)
    (hα : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map markS =
      markedOnePointLaw q A α)
    (hβ : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map markT =
      markedOnePointLaw q B β)
    (hint : ∀ (σ : {σ : Fin n → ι // patternCount σ c = a})
        (τ : {τ : Fin n → ι // patternCount τ c = b}),
      Integrable (fun z : (Fin n → Xs) × (Fin n → Yt) =>
        markedFixedBlockValue q r t kin g a b
          ((0, markedExtend a ha (fun i =>
              markS (z.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1))),
           (0, markedExtend b hb (fun j =>
              markT (z.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1)))))
      ((Measure.pi (fun i : Fin n => μs.restrict (labS ⁻¹' {σ.1 i}))).prod
        (Measure.pi (fun j : Fin n => μt.restrict (labT ⁻¹' {τ.1 j})))))
    (hintG : Integrable (fun p : (Fin a → Xs) × (Fin b → Yt) =>
        markedFixedBlockValue q r t kin g a b
          ((0, markedExtend a ha (fun i => markS (p.1 i))),
           (0, markedExtend b hb (fun j => markT (p.2 j)))))
      ((Measure.pi (fun _ : Fin a =>
          (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
        (Measure.pi (fun _ : Fin b =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) :
    (∑ σ : {σ : Fin n → ι // patternCount σ c = a},
        ∑ τ : {τ : Fin n → ι // patternCount τ c = b},
          ∫ p in twoColourPatternSet labS labT σ.1 τ.1,
            markedFixedBlockValue q r t kin g a b
              ((0, markedExtend a ha (fun i =>
                  markS (p.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1))),
               (0, markedExtend b hb (fun j =>
                  markT (p.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1))))
            ∂(twoColourLaw μs μt n))
      = ((Measure.pi (fun _ : Fin n => μs)) (tileCountEqSet labS c a)).toReal *
        ((Measure.pi (fun _ : Fin n => μt)) (tileCountEqSet labT c b)).toReal *
        markedFixedBlockExpectation q r t kin g α β R a b := by
  haveI := isProbabilityMeasure_inv_smul_restrict μs hρs
  haveI := isProbabilityMeasure_inv_smul_restrict μt hρt
  rw [sum_integral_twoColour_pattern_tile_eq_countWeight μs μt labS hS labT hT c a b
    hρs hρt (fun u v => markedFixedBlockValue q r t kin g a b
      ((0, markedExtend a ha (fun i => markS (u i))),
       (0, markedExtend b hb (fun j => markT (v j))))) hint hintG,
    integral_twoColour_tile_markedFixedBlock_eq hkin hg α β R μs μt labS labT c a b
      hρs hρt ha hb markS hmarkS markT hmarkT hα hβ]

end MarkedBridge

section ModelBlockSum

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- **`hblock` model-sum bridge.**  The double sum over source and target label
patterns with positive tile counts `a = k + 1`, `b = l + 1` of the
pattern-conditional marked block integrals equals `modelBlockSum` at tile weight
`w`, provided

* the count-event weights are the binomial masses `binomialMass n w a`;
* the marked fixed-block expectation vanishes at zero counts (the empty block);
* the marked block value is integrable on the pattern and normalized tile
  measures.

This is the exact random-count identity behind `hblock` (the hypothesis of
`exists_physical_upper_bound_of_block_model`).  The remaining inputs are the
separate count law `P(N = a) = binomialMass n w a`, and the identification of the
physical block integral with this pattern sum (permutation invariance of the block
under re-enumeration of the tile points together with the physical iid transfer). -/
theorem sum_integral_twoColour_tile_eq_modelBlockSum_marked {q : ℕ} {t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (c : ι) (n : ℕ) (w : unitInterval)
    (hρs : μs (labS ⁻¹' {c}) ≠ 0) (hρt : μt (labT ⁻¹' {c}) ≠ 0)
    (markS : Xs → (Fin q → ℝ) × A) (hmarkS : Measurable markS)
    (markT : Yt → (Fin q → ℝ) × B) (hmarkT : Measurable markT)
    (hα : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map markS =
      markedOnePointLaw q A α)
    (hβ : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map markT =
      markedOnePointLaw q B β)
    (hNs : ∀ a, ((Measure.pi (fun _ : Fin n => μs)) (tileCountEqSet labS c a)).toReal =
      binomialMass n w a)
    (hNt : ∀ b, ((Measure.pi (fun _ : Fin n => μt)) (tileCountEqSet labT c b)).toReal =
      binomialMass n w b)
    (hzero : ∀ a b, (a = 0 ∨ b = 0) →
      markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
        ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a b = 0)
    (hint : ∀ (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
        (σ : {σ : Fin n → ι // patternCount σ c = a})
        (τ : {τ : Fin n → ι // patternCount τ c = b}),
      Integrable (fun z : (Fin n → Xs) × (Fin n → Yt) =>
        markedFixedBlockValue q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g a b
          ((0, markedExtend a ha (fun i =>
              markS (z.1 ((tileEquiv σ.1 c (fun _ => a) σ.2 i)).1))),
           (0, markedExtend b hb (fun j =>
              markT (z.2 ((tileEquiv τ.1 c (fun _ => b) τ.2 j)).1)))))
      ((Measure.pi (fun i : Fin n => μs.restrict (labS ⁻¹' {σ.1 i}))).prod
        (Measure.pi (fun j : Fin n => μt.restrict (labT ⁻¹' {τ.1 j})))))
    (hintG : ∀ (a b : ℕ) (ha : 0 < a) (hb : 0 < b),
      Integrable (fun p : (Fin a → Xs) × (Fin b → Yt) =>
        markedFixedBlockValue q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g a b
          ((0, markedExtend a ha (fun i => markS (p.1 i))),
           (0, markedExtend b hb (fun j => markT (p.2 j)))))
      ((Measure.pi (fun _ : Fin a =>
          (μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))).prod
        (Measure.pi (fun _ : Fin b =>
          (μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))))) :
    (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        ∑ σ : {σ : Fin n → ι // patternCount σ c = k + 1},
          ∑ τ : {τ : Fin n → ι // patternCount τ c = l + 1},
            ∫ p in twoColourPatternSet labS labT σ.1 τ.1,
              markedFixedBlockValue q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g
                (k + 1) (l + 1)
                ((0, markedExtend (k + 1) (Nat.succ_pos k) (fun i =>
                    markS (p.1 ((tileEquiv σ.1 c (fun _ => k + 1) σ.2 i)).1))),
                 (0, markedExtend (l + 1) (Nat.succ_pos l) (fun j =>
                    markT (p.2 ((tileEquiv τ.1 c (fun _ => l + 1) τ.2 j)).1))))
              ∂(twoColourLaw μs μt n))
      = modelBlockSum q t kin g α β w n := by
  classical
  have hrow0 : ∀ b, binomialMass n w 0 * binomialMass n w b *
      markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
        ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) 0 b = 0 := by
    intro b
    rw [hzero 0 b (Or.inl rfl), mul_zero]
  have hcol0 : ∀ a, binomialMass n w a * binomialMass n w 0 *
      markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
        ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a 0 = 0 := by
    intro a
    rw [hzero a 0 (Or.inr rfl), mul_zero]
  have hterm : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n,
      (∑ σ : {σ : Fin n → ι // patternCount σ c = k + 1},
        ∑ τ : {τ : Fin n → ι // patternCount τ c = l + 1},
          ∫ p in twoColourPatternSet labS labT σ.1 τ.1,
            markedFixedBlockValue q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g
              (k + 1) (l + 1)
              ((0, markedExtend (k + 1) (Nat.succ_pos k) (fun i =>
                  markS (p.1 ((tileEquiv σ.1 c (fun _ => k + 1) σ.2 i)).1))),
               (0, markedExtend (l + 1) (Nat.succ_pos l) (fun j =>
                  markT (p.2 ((tileEquiv τ.1 c (fun _ => l + 1) τ.2 j)).1))))
            ∂(twoColourLaw μs μt n)) =
      binomialMass n w (k + 1) * binomialMass n w (l + 1) *
        markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
          ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) (k + 1) (l + 1) := by
    intro k _ l _
    have h := sum_integral_twoColour_tile_eq_countWeight_marked hkin hg α β
      ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) μs μt labS hS
      labT hT c (k + 1) (l + 1) hρs hρt (Nat.succ_pos k) (Nat.succ_pos l)
      markS hmarkS markT hmarkT hα hβ
      (hint (k + 1) (l + 1) (Nat.succ_pos k) (Nat.succ_pos l))
      (hintG (k + 1) (l + 1) (Nat.succ_pos k) (Nat.succ_pos l))
    rw [h, hNs (k + 1), hNt (l + 1)]
  rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => hterm k hk l hl))]
  have hshift : ∀ (f : ℕ → ℝ), f 0 = 0 →
      (∑ a ∈ Finset.range (n + 1), f a) = ∑ k ∈ Finset.range n, f (k + 1) := by
    intro f hf
    have hset : Finset.range (n + 1) = insert 0 ((Finset.range n).image (· + 1)) := by
      ext m
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
      constructor
      · intro hm
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · exact Or.inl rfl
        · exact Or.inr ⟨m - 1, by omega, by omega⟩
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact Nat.succ_pos n
        · omega
    rw [hset, Finset.sum_insert (by simp), hf, zero_add,
      Finset.sum_image (fun x _ y _ hxy => Nat.succ.inj hxy)]
  have hinner : ∀ a, (∑ b ∈ Finset.range (n + 1),
        binomialMass n w a * binomialMass n w b *
          markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
            ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a b) =
      ∑ l ∈ Finset.range n, binomialMass n w a * binomialMass n w (l + 1) *
        markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
          ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a (l + 1) := by
    intro a
    exact hshift (fun b => binomialMass n w a * binomialMass n w b *
      markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
        ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a b) (hcol0 a)
  have houter : (∑ a ∈ Finset.range (n + 1),
        ∑ l ∈ Finset.range n, binomialMass n w a * binomialMass n w (l + 1) *
          markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
            ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a (l + 1)) =
      ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        binomialMass n w (k + 1) * binomialMass n w (l + 1) *
          markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
            ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) (k + 1) (l + 1) := by
    exact hshift (fun a => ∑ l ∈ Finset.range n,
      binomialMass n w a * binomialMass n w (l + 1) *
        markedFixedBlockExpectation q ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ) t kin g α β
          ((Nat.floor ((n : ℝ) * (w : ℝ)) : ℕ) : ℝ≥0) a (l + 1))
      (Finset.sum_eq_zero fun l _ => hrow0 (l + 1))
  rw [modelBlockSum]
  simp_rw [hinner]
  rw [houter]

end ModelBlockSum

end OTSelector.Probability

