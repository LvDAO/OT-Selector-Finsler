import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# Transport.ScalarForwardFlux

## Lemma skeleton

* **Conditions:** A finite forward scalar coupling, no source atom at any tested level, and a conull set all of whose neighborhoods have positive coupling mass.

* **Objects:** CDF-difference ray flux, its crossing-mass identity and the exact positive-flux interval cover.

* **Proof detail:** Partition the two marginal half-spaces into crossed and uncrossed parts, cancel the common part, remove the forbidden backward and zero-mass equality pieces, then use openness of a crossing interval and support positivity in both directions.

## Mathematical sources

- [OTSelector project, Scalar forward ray-cut flux identity](main.tex#eq:ray-cut-flux): main.tex label eq:ray-cut-flux, line 530.
- [OTSelector project, Intrinsic active interval cover](main.tex#eq:intrinsic-active-cover): main.tex label eq:intrinsic-active-cover, line 982.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf): Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6): Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products).

Source relation (composition): The cut-flux and active-cover identities are the project paper’s own construction at the cited labels; the measure-partition and support steps are elementary foundations.
-/

/-!
# Construction of the intrinsic active-ray flux and its cover identity

This module formalizes the analytic core of the construction of the intrinsic
active-ray data of the paper's structural invariance theorem
`thm:intrinsic-active-invariance` (`main.tex`:958), continuing
`FinslerIntrinsicActiveInvariance.lean`.

For one fixed whole-ray label, the paper's ray data consist of a forward
coupling `κ` of two atomless scalar laws with continuous surplus `H_z`
(`main.tex`, "Intrinsic active ray components", around lines 915-950).  This
module constructs the surplus as the CDF difference

`rayFlux κ r = (κ {p | p.1 ≤ r}).toReal - (κ {p | p.2 ≤ r}).toReal`

and proves

* `rayFlux_eq_crossing` — the ray-cut flux identity `eq:ray-cut-flux`:
  `H(r) = κ {p | p.1 < r ∧ r < p.2}` for a forward coupling with atomless first
  marginal;
* `pos_rayFlux_iff` — positivity of the surplus is positivity of the
  crossing measure;
* `pos_rayFlux_eq_iUnion_intervals` — the cover identity
  `eq:intrinsic-active-cover`: the positive-flux set is the union of the
  crossing intervals `(p.1, p.2)` over any full-measure supporting set of the
  coupling.

These are the flux and cover fields of the active-block construction.  The
remaining part of the ray-data construction (kept explicit as the reduction
boundary) is the rational-enumeration Borel block space
(`eq:intrinsic-active-marker`), its conullness and quotient laws
(`eq:intrinsic-active-quotient`), the Borel block-label matching `T` with its
injective-image/Borel-inverse step, and the geometric two-cover containment
from `prop:general-optimal-face` (`main.tex`:422) and
`prop:ray-forward-criterion` (`main.tex`:524).
-/

open Set Function MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

/-- The surplus `H(r)` of a scalar coupling: the difference of the two
distribution functions at `r`.  This is the paper's
`H_z(r) = F_{α_z}(r) - F_{β_z}(r)` for one whole-ray label. -/
def rayFlux (κ : Measure (ℝ × ℝ)) (r : ℝ) : ℝ :=
  (κ {p : ℝ × ℝ | p.1 ≤ r}).toReal - (κ {p : ℝ × ℝ | p.2 ≤ r}).toReal

private theorem measurableSet_crossing (r : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.1 < r ∧ r < p.2} :=
  (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_snd)

private theorem measurableSet_upperLeft (r : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.1 ≤ r ∧ p.2 ≤ r} :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_const)

private theorem measurableSet_lowerRight (r : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.1 ≤ r ∧ r < p.2} :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_snd)

private theorem measurableSet_upperCrossed (r : ℝ) :
    MeasurableSet {p : ℝ × ℝ | r < p.1 ∧ p.2 ≤ r} :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_snd measurable_const)

private theorem measurableSet_equalCrossing (r : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.1 = r ∧ r < p.2} :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_snd)

/-- **Ray-cut flux identity `eq:ray-cut-flux`.**
For a coupling that is forward almost everywhere (`p.1 ≤ p.2`) with atomless
first marginal, the surplus at `r` is exactly the coupling mass of the strict
crossing event `{p.1 < r < p.2}`. -/
theorem rayFlux_eq_crossing (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ] {r : ℝ}
    (hforward : κ {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : κ {p : ℝ × ℝ | p.1 = r} = 0) :
    rayFlux κ r = (κ {p : ℝ × ℝ | p.1 < r ∧ r < p.2}).toReal := by
  have hUL := measurableSet_upperLeft r
  have hLR := measurableSet_lowerRight r
  have hUC := measurableSet_upperCrossed r
  -- partition of the first marginal event
  have hpart₁ : {p : ℝ × ℝ | p.1 ≤ r} =
      {p | p.1 ≤ r ∧ p.2 ≤ r} ∪ {p | p.1 ≤ r ∧ r < p.2} := by
    ext p
    constructor
    · rintro hp
      rcases le_or_gt p.2 r with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp
  have hdisj₁ : Disjoint {p : ℝ × ℝ | p.1 ≤ r ∧ p.2 ≤ r}
      {p : ℝ × ℝ | p.1 ≤ r ∧ r < p.2} := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    exact absurd h1 (not_le.mpr h2)
  -- partition of the second marginal event
  have hpart₂ : {p : ℝ × ℝ | p.2 ≤ r} =
      {p | p.1 ≤ r ∧ p.2 ≤ r} ∪ {p | r < p.1 ∧ p.2 ≤ r} := by
    ext p
    constructor
    · rintro hp
      by_cases h : p.1 ≤ r
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨not_le.mp h, hp⟩
    · rintro (⟨-, hp⟩ | ⟨-, hp⟩) <;> exact hp
  have hdisj₂ : Disjoint {p : ℝ × ℝ | p.1 ≤ r ∧ p.2 ≤ r}
      {p : ℝ × ℝ | r < p.1 ∧ p.2 ≤ r} := by
    rw [Set.disjoint_left]
    rintro p ⟨h1, -⟩ ⟨h2, -⟩
    exact absurd h1 (not_le.mpr h2)
  -- the upper-crossed region is forward-null
  have hnull : κ {p : ℝ × ℝ | r < p.1 ∧ p.2 ≤ r} = 0 := by
    apply measure_mono_null _ hforward
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    exact not_le.mpr (lt_of_le_of_lt hp.2 hp.1)
  have hsecond : κ {p : ℝ × ℝ | p.2 ≤ r}
      = κ {p : ℝ × ℝ | p.1 ≤ r ∧ p.2 ≤ r} := by
    rw [hpart₂, measure_union hdisj₂ hUC, hnull, add_zero]
  have hfirst : κ {p : ℝ × ℝ | p.1 ≤ r}
      = κ {p : ℝ × ℝ | p.1 ≤ r ∧ p.2 ≤ r} +
        κ {p : ℝ × ℝ | p.1 ≤ r ∧ r < p.2} := by
    rw [hpart₁, measure_union hdisj₁ hLR]
  -- all pieces are finite
  have hfin (s : Set (ℝ × ℝ)) : κ s ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top κ Set.univ) (measure_mono (subset_univ s))
  rw [rayFlux, hfirst, hsecond, ENNReal.toReal_add (hfin _) (hfin _)]
  -- replace the non-strict crossing by the strict one (atomless first marginal)
  have hdiff : {p : ℝ × ℝ | p.1 ≤ r ∧ r < p.2} =
      {p : ℝ × ℝ | p.1 < r ∧ r < p.2} ∪ {p : ℝ × ℝ | p.1 = r ∧ r < p.2} := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_eq_of_le h1 with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨le_of_lt h1, h2⟩
      · exact ⟨le_of_eq h1, h2⟩
  have hdisj₃ : Disjoint {p : ℝ × ℝ | p.1 < r ∧ r < p.2}
      {p : ℝ × ℝ | p.1 = r ∧ r < p.2} := by
    rw [Set.disjoint_left]
    rintro p ⟨h1, -⟩ ⟨h2, -⟩
    exact absurd h2 (ne_of_lt h1)
  have hnull₂ : κ {p : ℝ × ℝ | p.1 = r ∧ r < p.2} = 0 := by
    apply measure_mono_null _ hatom
    intro p hp
    exact hp.1
  have hcross : κ {p : ℝ × ℝ | p.1 ≤ r ∧ r < p.2}
      = κ {p : ℝ × ℝ | p.1 < r ∧ r < p.2} := by
    rw [hdiff, measure_union hdisj₃ (measurableSet_equalCrossing r)]
    simp only [hnull₂, add_zero]
  rw [hcross]
  ring

/-- **Positivity of the surplus is positivity of the crossing measure.** -/
theorem pos_rayFlux_iff (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ] {r : ℝ}
    (hforward : κ {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : κ {p : ℝ × ℝ | p.1 = r} = 0) :
    0 < rayFlux κ r ↔ 0 < κ {p : ℝ × ℝ | p.1 < r ∧ r < p.2} := by
  rw [rayFlux_eq_crossing κ hforward hatom, ENNReal.toReal_pos_iff]
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro hpos
    exact ⟨hpos, lt_top_iff_ne_top.mpr (measure_ne_top κ _)⟩

/-- **Cover identity `eq:intrinsic-active-cover`.**
For a forward coupling with atomless first marginal, the positive-flux set is
the union of the crossing intervals `(p.1, p.2)` over any full-measure
supporting set `G` of the coupling.  ("Supporting" means every open
neighborhood of a point of `G` has positive coupling mass; the paper takes
`G` inside the support, so that each crossing interval lies in its positive
component.) -/
theorem pos_rayFlux_eq_iUnion_intervals (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ]
    (hforward : κ {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : ∀ r : ℝ, κ {p : ℝ × ℝ | p.1 = r} = 0)
    (G : Set (ℝ × ℝ)) (hGnull : κ Gᶜ = 0)
    (hsupp : ∀ p ∈ G, ∀ U : Set (ℝ × ℝ), IsOpen U → p ∈ U → 0 < κ U) :
    {r : ℝ | 0 < rayFlux κ r} = ⋃ p ∈ G, Set.Ioo p.1 p.2 := by
  ext r
  rw [Set.mem_ofPred_eq, pos_rayFlux_iff κ hforward (hatom r)]
  constructor
  · intro hpos
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    have hsub : {p : ℝ × ℝ | p.1 < r ∧ r < p.2} ⊆ Gᶜ := by
      intro p hp
      simp only [Set.mem_compl_iff]
      exact fun hpG => (hcon p hpG) ⟨hp.1, hp.2⟩
    have hzero : κ {p : ℝ × ℝ | p.1 < r ∧ r < p.2} = 0 :=
      measure_mono_null hsub hGnull
    exact absurd hzero (ne_of_gt hpos)
  · intro hmem
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨p, hpG, hp⟩ := hmem
    have hopen : IsOpen {q : ℝ × ℝ | q.1 < r ∧ r < q.2} :=
      (isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_const continuous_snd)
    exact hsupp p hpG {q : ℝ × ℝ | q.1 < r ∧ r < q.2} hopen ⟨hp.1, hp.2⟩

end OTSelector.Reconstruction