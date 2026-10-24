import OTSelector.Limit.FinslerTileCountLaw
import OTSelector.Probability.TileCountBlockBridge

/-!
# The exact binomial law of a tile count

The `hblock` bridge `sum_integral_twoColour_tile_eq_modelBlockSum_marked` in
`OTSelector.Probability.TileCountBlockBridge` takes the exact count law

`P(N = a) = binomialMass n w a`

as the explicit hypotheses `hNs`/`hNt`.  This module proves it.

For an iid label law `iidLabelMeasure n p = Measure.pi (fun _ : Fin n => p)`, the
tile-`c` count `blockSizeS x c` is the number of coordinates equal to `c`.  The
count event is the disjoint union, over the `a`-element subsets `s` of `Fin n`,
of the product sets

`{x | ∀ i, (i ∈ s → x i = c) ∧ (i ∉ s → x i ≠ c)}`.

Each such product set has mass `p {c} ^ #s * p {c}ᶜ ^ (n - #s)` by
`Measure.pi_pi`; there are `n.choose a` of them, so the total mass is the
binomial mass.

The results below are:

* `iidLabelMeasure_blockSizeS_real` / `iidLabelMeasure_blockSizeS`: the exact
  marginal law, in real and `ℝ≥0∞` form.
* `iidLabelMeasure_weightedLabelLaw_blockSizeS_real` /
  `iidLabelMeasure_weightedLabelLaw_blockSizeS`: the weighted-law specialization
  requested for the tile count.
* `pi_tileCountEqSet_toReal_eq_binomialMass`: the general labelled form
  `P(tileCount lab · c = a) = binomialMass n w a` for `Measure.pi μ` with
  `μ (lab ⁻¹' {c}) = ofReal w`, which is exactly the `hNs`/`hNt` shape of the
  bridge.
* `twoColourLaw_map_tileCount_prod`: the two-colour joint law of the source and
  target counts is the product of the two binomial laws.
* `indepFun_tileCount_twoColour`: the source and target tile counts are
  independent under the two-colour product law.

No `sorry`, `admit` or added axiom occurs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-! ## The single-colour count law -/

/-- **The exact binomial marginal law of one tile count (real form).**

Under the iid label law with `p {c} = ofReal w`, the probability that exactly
`a` of the `n` coordinates equal `c` is `binomialMass n w a`. -/
theorem iidLabelMeasure_blockSizeS_real (n : ℕ) (p : Measure ι) [IsProbabilityMeasure p]
    (c : ι) (w : unitInterval) (hw : p {c} = ENNReal.ofReal (w : ℝ)) (a : ℕ) :
    (iidLabelMeasure n p).real {x : Fin n → ι | blockSizeS x c = a} = binomialMass n w a := by
  classical
  -- The two complementary atom masses.
  have hPreal : (p {c}).toReal = (w : ℝ) := by
    rw [hw, ENNReal.toReal_ofReal w.2.1]
  have hQreal : (p ({c}ᶜ)).toReal = 1 - (w : ℝ) := by
    have huniv : p.real Set.univ = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    have hsingle : p.real ({c} : Set ι) = (w : ℝ) := by
      rw [measureReal_def, hPreal]
    rw [← measureReal_def, measureReal_compl (measurableSet_singleton c), huniv, hsingle]
  -- The count event as a disjoint union of product sets.
  have hset : {x : Fin n → ι | blockSizeS x c = a} =
      ⋃ s ∈ (Finset.univ : Finset (Fin n)).powersetCard a,
        Set.pi Set.univ (fun i => if i ∈ s then ({c} : Set ι) else {c}ᶜ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Set.mem_pi, Set.mem_univ,
      true_implies, Finset.mem_powersetCard]
    constructor
    · intro hx
      refine ⟨Finset.univ.filter (fun i => x i = c), ?_, ?_⟩
      · have hcard : ((Finset.univ.filter (fun i => x i = c)) : Finset (Fin n)).card = a := by
          simpa only [blockSizeS, blockFinset] using hx
        exact ⟨Finset.subset_univ _, hcard⟩
      · intro i
        by_cases hi : x i = c
        · have himem : i ∈ Finset.univ.filter (fun i => x i = c) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
          simpa [himem] using hi
        · have himem : i ∉ Finset.univ.filter (fun i => x i = c) :=
            fun h => hi (Finset.mem_filter.mp h).2
          simpa [himem] using hi
    · rintro ⟨s, hs, hx⟩
      have hfilter : (Finset.univ.filter (fun i => x i = c)) = s := by
        apply Finset.ext
        intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          by_contra hnot
          have hnc : x i ≠ c := by simpa [hnot] using hx i
          exact hnc hi
        · intro hi
          simpa [hi] using hx i
      rw [blockSizeS, blockFinset, hfilter]
      exact hs.2
  -- Disjointness of the product sets.
  have hdisj : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard a,
      ∀ t ∈ (Finset.univ : Finset (Fin n)).powersetCard a, s ≠ t →
        Disjoint (Set.pi Set.univ (fun i => if i ∈ s then ({c} : Set ι) else {c}ᶜ))
          (Set.pi Set.univ (fun i => if i ∈ t then ({c} : Set ι) else {c}ᶜ)) := by
    intro s _ t _ hst
    rw [Set.disjoint_left]
    intro x hx hy
    apply hst
    apply Finset.ext
    intro i
    by_cases hi : i ∈ s
    · have hxc : x i = c := by simpa [hi] using hx i
      have hit : i ∈ t := by
        by_contra hnot
        have hnc : x i ≠ c := by simpa [hnot] using hy i
        exact hnc hxc
      simp only [hi, hit]
    · have hxc : x i ≠ c := by simpa [hi] using hx i
      have hit : i ∉ t := by
        intro hin
        have hc : x i = c := by simpa [hin] using hy i
        exact hxc hc
      simp only [hi, hit]
  -- Measurability of each product set.
  have hmeas : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard a,
      MeasurableSet (Set.pi Set.univ (fun i => if i ∈ s then ({c} : Set ι) else {c}ᶜ)) := by
    intro s _
    exact MeasurableSet.univ_pi fun i => by
      by_cases hi : i ∈ s
      · rw [show (if i ∈ s then ({c} : Set ι) else {c}ᶜ) = {c} from by simp [hi]]
        exact measurableSet_singleton c
      · rw [show (if i ∈ s then ({c} : Set ι) else {c}ᶜ) = {c}ᶜ from by simp [hi]]
        exact (measurableSet_singleton c).compl
  -- The mass of one product set.
  have hterm : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard a,
      ((Measure.pi (fun _ : Fin n => p))
        (Set.pi Set.univ (fun i => if i ∈ s then ({c} : Set ι) else {c}ᶜ))).toReal =
        (w : ℝ) ^ a * (1 - (w : ℝ)) ^ (n - a) := by
    intro s hs
    have hcard : s.card = a := (Finset.mem_powersetCard.mp hs).2
    rw [Measure.pi_pi]
    have hfun : (fun i : Fin n => p (if i ∈ s then ({c} : Set ι) else {c}ᶜ)) =
        (fun i => if i ∈ s then p {c} else p ({c}ᶜ)) := by
      funext i
      by_cases hi : i ∈ s <;> simp [hi]
    rw [hfun, ENNReal.toReal_prod]
    have hfun2 : (fun i : Fin n => (if i ∈ s then p {c} else p ({c}ᶜ)).toReal) =
        (fun i => if i ∈ s then (w : ℝ) else 1 - (w : ℝ)) := by
      funext i
      by_cases hi : i ∈ s <;> simp [hi, hPreal, hQreal]
    rw [hfun2, Finset.prod_ite]
    have hf1 : (Finset.univ : Finset (Fin n)).filter (fun i => i ∈ s) = s := by
      ext i
      simp
    have hf2 : (Finset.univ : Finset (Fin n)).filter (fun i => ¬ i ∈ s) =
        Finset.univ \ s := by
      ext i
      simp
    rw [hf1, hf2, Finset.prod_const, Finset.prod_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ,
      Fintype.card_fin, hcard]
  -- Evaluate the measure and sum.
  rw [measureReal_def, hset, measure_biUnion_finset hdisj hmeas, ENNReal.toReal_sum]
  · trans ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard a,
      (w : ℝ) ^ a * (1 - (w : ℝ)) ^ (n - a)
    · exact Finset.sum_congr rfl hterm
    · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      unfold binomialMass
      ring
  · intro s _
    exact measure_ne_top _ _

/-- **The exact binomial marginal law of one tile count (`ℝ≥0∞` form).** -/
theorem iidLabelMeasure_blockSizeS (n : ℕ) (p : Measure ι) [IsProbabilityMeasure p]
    (c : ι) (w : unitInterval) (hw : p {c} = ENNReal.ofReal (w : ℝ)) (a : ℕ) :
    iidLabelMeasure n p {x : Fin n → ι | blockSizeS x c = a} =
      ENNReal.ofReal (binomialMass n w a) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (iidLabelMeasure n p) _), ← measureReal_def,
    iidLabelMeasure_blockSizeS_real n p c w hw a]

/-- **The weighted-law specialization (real form).** -/
theorem iidLabelMeasure_weightedLabelLaw_blockSizeS_real (n : ℕ) (w : ι → unitInterval)
    (hwsum : ∑ c, (w c : ℝ) = 1) (c : ι) (a : ℕ) :
    (iidLabelMeasure n (weightedLabelLaw w)).real {x : Fin n → ι | blockSizeS x c = a} =
      binomialMass n (w c) a := by
  haveI : IsProbabilityMeasure (weightedLabelLaw w) := weightedLabelLaw_isProbability w hwsum
  exact iidLabelMeasure_blockSizeS_real n (weightedLabelLaw w) c (w c)
    (weightedLabelLaw_apply w c) a

/-- **The weighted-law specialization (`ℝ≥0∞` form), as stated in the task.** -/
theorem iidLabelMeasure_weightedLabelLaw_blockSizeS (n : ℕ) (w : ι → unitInterval)
    (hwsum : ∑ c, (w c : ℝ) = 1) (c : ι) (a : ℕ) :
    iidLabelMeasure n (weightedLabelLaw w) {x : Fin n → ι | blockSizeS x c = a} =
      ENNReal.ofReal (binomialMass n (w c) a) := by
  haveI : IsProbabilityMeasure (weightedLabelLaw w) := weightedLabelLaw_isProbability w hwsum
  exact iidLabelMeasure_blockSizeS n (weightedLabelLaw w) c (w c)
    (weightedLabelLaw_apply w c) a

end OTSelector.Probability

namespace OTSelector.Probability

variable {Xs : Type*} [MeasurableSpace Xs]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- Measurability of the count-event set of a label word. -/
theorem measurableSet_blockSizeS_eq {n : ℕ} (c : ι) (a : ℕ) :
    MeasurableSet {x : Fin n → ι | blockSizeS x c = a} := by
  have h : Measurable fun x : Fin n → ι => blockSizeS x c := by
    simpa only [tileCount, blockSizeS, blockFinset, id_eq] using
      measurable_tileCount (X := ι) (lab := id) measurable_id c
  exact h (measurableSet_singleton a)

/-- **The general labelled count law (`hNs`/`hNt` shape).**

For an iid sample `Measure.pi (fun _ : Fin n => μ)` on `Fin n → Xs`, the number
of coordinates whose label equals `c` has the binomial law with parameter
`w`, where `μ (lab ⁻¹' {c}) = ofReal w`.  This is the exact hypothesis
`hNs`/`hNt` of `sum_integral_twoColour_tile_eq_modelBlockSum_marked`. -/
theorem pi_tileCountEqSet_toReal_eq_binomialMass {n : ℕ} (μ : Measure Xs)
    [IsProbabilityMeasure μ] (lab : Xs → ι) (hlab : Measurable lab) (c : ι)
    (w : unitInterval) (hw : μ (lab ⁻¹' {c}) = ENNReal.ofReal (w : ℝ)) (a : ℕ) :
    ((Measure.pi (fun _ : Fin n => μ)) (tileCountEqSet lab c a)).toReal =
      binomialMass n w a := by
  classical
  -- The count only depends on the label word.
  have hcount : ∀ x : Fin n → Xs, tileCount lab x c = blockSizeS (fun i => lab (x i)) c := by
    intro x
    simp only [tileCount, blockSizeS, blockFinset]
  have hset : tileCountEqSet lab c a =
      (fun x : Fin n → Xs => fun i => lab (x i)) ⁻¹'
        {y : Fin n → ι | blockSizeS y c = a} := by
    ext x
    simp only [tileCountEqSet, Set.mem_ofPred_eq, Set.mem_preimage, hcount]
  have hmeasΦ : Measurable fun x : Fin n → Xs => fun i => lab (x i) :=
    measurable_pi_lambda _ fun i => hlab.comp (measurable_pi_apply i)
  rw [hset]
  rw [show (Measure.pi (fun _ : Fin n => μ))
        ((fun x : Fin n → Xs => fun i => lab (x i)) ⁻¹'
          {y : Fin n → ι | blockSizeS y c = a}) =
      ((Measure.pi (fun _ : Fin n => μ)).map (fun x : Fin n → Xs => fun i => lab (x i)))
        {y : Fin n → ι | blockSizeS y c = a} from
    (Measure.map_apply hmeasΦ (measurableSet_blockSizeS_eq c a)).symm]
  -- Push the product law forward to the label law.
  have hmap : (Measure.pi (fun _ : Fin n => μ)).map (fun x : Fin n → Xs => fun i => lab (x i)) =
      Measure.pi (fun _ : Fin n => μ.map lab) :=
    Measure.pi_map_pi fun _ => hlab.aemeasurable
  rw [hmap]
  have hw' : Measure.map lab μ {c} = ENNReal.ofReal (w : ℝ) := by
    rw [Measure.map_apply hlab (measurableSet_singleton c)]
    exact hw
  haveI : IsProbabilityMeasure (Measure.map lab μ) :=
    Measure.isProbabilityMeasure_map hlab.aemeasurable
  exact iidLabelMeasure_blockSizeS_real n (Measure.map lab μ) c w hw' a

end OTSelector.Probability

namespace OTSelector.Probability

variable {Xs Yt : Type*} [MeasurableSpace Xs] [MeasurableSpace Yt]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

/-- **The two-colour joint law of the source and target tile counts.**

Under the product of the two iid sample laws, the pair of tile counts has the
product of the two binomial laws. -/
theorem twoColourLaw_map_tileCount_prod {n : ℕ} (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hlabS : Measurable labS) (labT : Yt → ι) (hlabT : Measurable labT)
    (c : ι) (w : unitInterval)
    (hws : μs (labS ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (hwt : μt (labT ⁻¹' {c}) = ENNReal.ofReal (w : ℝ)) :
    (twoColourLaw μs μt n).map (fun p =>
        (tileCount labS p.1 c, tileCount labT p.2 c)) =
      (ProbabilityTheory.binomial n w).prod (ProbabilityTheory.binomial n w) := by
  classical
  -- The single-colour laws.
  have hsingleS : (Measure.pi (fun _ : Fin n => μs)).map (fun x => tileCount labS x c) =
      ProbabilityTheory.binomial n w := by
    refine Measure.ext_of_singleton fun a => ?_
    rw [Measure.map_apply (measurable_tileCount hlabS c) (measurableSet_singleton a)]
    have hreal := pi_tileCountEqSet_toReal_eq_binomialMass (n := n) μs labS hlabS c w hws a
    have hbin : ProbabilityTheory.binomial n w {a} = ENNReal.ofReal (binomialMass n w a) := by
      rw [ProbabilityTheory.binomial_singleton]
      rfl
    rw [hbin, ← hreal, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  have hsingleT : (Measure.pi (fun _ : Fin n => μt)).map (fun y => tileCount labT y c) =
      ProbabilityTheory.binomial n w := by
    refine Measure.ext_of_singleton fun a => ?_
    rw [Measure.map_apply (measurable_tileCount hlabT c) (measurableSet_singleton a)]
    have hreal := pi_tileCountEqSet_toReal_eq_binomialMass (n := n) μt labT hlabT c w hwt a
    have hbin : ProbabilityTheory.binomial n w {a} = ENNReal.ofReal (binomialMass n w a) := by
      rw [ProbabilityTheory.binomial_singleton]
      rfl
    rw [hbin, ← hreal, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  rw [twoColourLaw]
  rw [show (fun p : (Fin n → Xs) × (Fin n → Yt) =>
        (tileCount labS p.1 c, tileCount labT p.2 c)) =
      Prod.map (fun x => tileCount labS x c) (fun y => tileCount labT y c) from rfl]
  rw [← Measure.map_prod_map _ _ (measurable_tileCount hlabS c) (measurable_tileCount hlabT c),
    hsingleS, hsingleT]

/-- **Independence of the source and target tile counts** under the two-colour
product law. -/
theorem indepFun_tileCount_twoColour {n : ℕ} (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hlabS : Measurable labS) (labT : Yt → ι) (hlabT : Measurable labT)
    (c : ι) (w : unitInterval)
    (hws : μs (labS ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (hwt : μt (labT ⁻¹' {c}) = ENNReal.ofReal (w : ℝ)) :
    IndepFun (fun p : (Fin n → Xs) × (Fin n → Yt) => tileCount labS p.1 c)
      (fun p => tileCount labT p.2 c) (twoColourLaw μs μt n) := by
  rw [twoColourLaw]
  exact indepFun_prod (measurable_tileCount hlabS c) (measurable_tileCount hlabT c)

end OTSelector.Probability
