import OTSelector.Topology.Real.Components
import OTSelector.Transport.ScalarForwardFlux
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerIntrinsicActiveMarker.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerIntrinsicActiveMarker`; the selected original proof blocks follow. -/
section

/-!
# Topology.Real.PositiveComponentSegmentMinimum

Conditions: Pure segment statements use real sets/continuous functions and the displayed endpoint membership hypotheses; ray-flux statements separately require the actual finite forward coupling, atomless first marginal and full supporting set.
Objects: Real connected components, compact-segment minima, the positive crossing-flux set and its rationally coded component cover.
Proof detail: Use the interval characterization of connected real sets and extreme-value attainment for the pure segment tests; use the crossing-interval cover of the forward coupling to obtain an open active set and its rational component coding.

## Mathematical sources

- Jiří Lebl, *Basic Analysis I, version 6.3 (15 May 2026)*: Section 7.2.2, Definition 7.2.13 and Proposition 7.2.16, pp. 268–269 (connected real sets are intervals or singletons). https://www.jirka.org/ra/realanal.pdf#page=268
- Jiří Lebl, *Basic Analysis I, version 6.3 (15 May 2026)*: Section 3.3, Theorem 3.3.2, pp. 130–131 (extreme values on a compact interval). https://www.jirka.org/ra/realanal.pdf#page=130
- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Subsection subsec:intrinsic-active-components; equations eq:intrinsic-active-marker and eq:intrinsic-active-cover; proof of thm:intrinsic-active-invariance. ../main.tex#L933

Source relation: This is a mixed topic: classical one-dimensional topology/compact minima plus generic transport crossing-flux adapters motivated by the manuscript. The whole file should not be presented as pure Topology.Real, and continuity is only used by the segment-minimum equivalence.
-/

/-!
# Segment-positivity criterion and the active-marker cover

This module addresses gap (b) of FinslerIntrinsicActiveComponentCover.lean for
the structural invariance theorem (main.tex:958): the segment-positivity
criterion of the Borel block space (`eq:intrinsic-active-marker`) and the
regularity (semicontinuity/continuity) of the ray surplus that the paper uses
to identify the infimum over rational segment parameters with the minimum on
the compact segment.

## Results

* `isOpen_pos_rayFlux`: the positive-flux set of a ray surplus is *open*,
  unconditionally from the already-needed ray hypotheses (forward coupling and
  atomless first marginal): by the cover identity
  `pos_rayFlux_eq_iUnion_intervals` it is a union of the open crossing
  intervals `(p.1, p.2)`.  Hence no continuity or semicontinuity of the
  surplus is needed for the block space.
* `rayFlux_nonneg`: pointwise nonnegativity of the surplus (the crossing
  measure cannot be negative), so the active set is exactly the strict
  positivity set and its components are the open active arcs.
* `segment_subset_iff_connectedComponentIn_eq`: the **segment-positivity
  criterion** in its exact topological form: for points `x, y` of a set `U`,
  the whole segment `{(1-t)x + ty : t ∈ [0,1]}` lies in `U` iff `x` and `y`
  lie in the same connected component of `U`.  This is the criterion that the
  paper's strict infimum `inf_{u∈ℚ∩[0,1]} H((1-u)r + u r_j) > 0` encodes:
  strict positivity of the infimum is equivalent to positivity on the whole
  segment once the surplus is continuous (the paper's standing hypothesis).
  Note that *pointwise* positivity on the rational segment parameters alone is
  weaker: a continuous surplus with an irrational zero on the segment can be
  positive on every rational parameter, so the strict infimum/containment form
  is the correct one; we formalize the containment form, which is what the
  least-index marker `j_φ(z,r)` actually needs.
* `rayFlux_segment_pos_iff_component_eq`: the criterion specialized to the ray
  surplus: `H > 0` on the whole segment between two active parameters iff they
  are in the same active component.
* `exists_rat_rayFlux_component`: every active point has a rational point of
  its component with positive surplus (the rational curve code of the
  minimal-arc transport; well-definedness of the least-index marker).
* `exists_component_cover_of_rayFlux` and its family version
  `exists_component_cover_family_of_rayFlux`: the rational-code cover identity
  of the active set, unconditionally from the ray hypotheses, blocks indexed by
  the rationals.

## Remaining sub-gap

Continuity (`semicontinuity`) of the surplus is *not* derived here and is not
needed: the positivity set is open by the crossing-interval identity, so the
component criterion is purely topological.  The paper's continuity statement
for `H_z^φ` follows from atomlessness of both scalar marginals; the second
marginal's atomlessness is not used by the present cover, and the paper's
infimum-over-rationals form is equivalent to segment containment only under
continuity.  What remains for the full marker is Borel measurability of the
segment test in the label variable and of the least-index function, together
with the bijective enumeration of the active components needed by the
`IntrinsicActiveRayData` interface (see FinslerIntrinsicActiveComponentCover).
-/

open Set Function MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Regularity of the ray surplus -/

/-- The ray surplus is pointwise nonnegative: it is the coupling mass of the
strict crossing event, hence cannot be negative. -/
theorem rayFlux_nonneg (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ] {r : ℝ}
    (hforward : κ {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : κ {p : ℝ × ℝ | p.1 = r} = 0) :
    0 ≤ rayFlux κ r := by
  rw [rayFlux_eq_crossing κ hforward hatom]
  exact ENNReal.toReal_nonneg

/-- **The active set is open.**  The positive-flux set of a ray surplus is a
union of the open crossing intervals of the coupling, hence open.  In
particular no continuity or semicontinuity of the surplus is needed for the
active blocks to be open arcs. -/
theorem isOpen_pos_rayFlux (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ]
    (hforward : κ {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : ∀ r : ℝ, κ {p : ℝ × ℝ | p.1 = r} = 0)
    (G : Set (ℝ × ℝ)) (hGnull : κ Gᶜ = 0)
    (hsupp : ∀ p ∈ G, ∀ U : Set (ℝ × ℝ), IsOpen U → p ∈ U → 0 < κ U) :
    IsOpen {r : ℝ | 0 < rayFlux κ r} := by
  rw [pos_rayFlux_eq_iUnion_intervals κ hforward hatom G hGnull hsupp]
  exact isOpen_iUnion fun p => isOpen_iUnion fun _ => isOpen_Ioo

/-! ## Segment-positivity criterion -/

/-- **Segment criterion for active components.**  For points `x, y` of a set
`U`, the segment between them lies in `U` iff they lie in the same connected
component of `U`.  This is the topological content of the paper's
segment-positivity test `eq:intrinsic-active-marker` (with the strict
infimum/minimum taken on the compact segment). -/
theorem segment_subset_iff_connectedComponentIn_eq {U : Set ℝ} {x y : ℝ}
    (hx : x ∈ U) (hy : y ∈ U) :
    (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (1 - t) * x + t * y ∈ U) ↔
      connectedComponentIn U x = connectedComponentIn U y := by
  constructor
  · intro hseg
    have himg : IsPreconnected ((fun t : ℝ => (1 - t) * x + t * y) '' Icc (0 : ℝ) 1) := by
      have hcont : ContinuousOn (fun t : ℝ => (1 - t) * x + t * y) (Icc (0 : ℝ) 1) :=
        (by fun_prop : Continuous fun t : ℝ => (1 - t) * x + t * y).continuousOn
      exact isPreconnected_Icc.image _ hcont
    have hsub : ((fun t : ℝ => (1 - t) * x + t * y) '' Icc (0 : ℝ) 1) ⊆ U := by
      rintro z ⟨t, ht, rfl⟩
      exact hseg t ht
    have hxmem : x ∈ ((fun t : ℝ => (1 - t) * x + t * y) '' Icc (0 : ℝ) 1) := by
      refine ⟨0, by norm_num, by ring⟩
    have hymem : y ∈ ((fun t : ℝ => (1 - t) * x + t * y) '' Icc (0 : ℝ) 1) := by
      refine ⟨1, by norm_num, by ring⟩
    exact connectedComponentIn_eq (himg.subset_connectedComponentIn hxmem hsub hymem)
  · intro hcc t ht
    have hpre : IsPreconnected (connectedComponentIn U x) := isPreconnected_connectedComponentIn
    have hy' : y ∈ connectedComponentIn U x := by
      rw [hcc]
      exact mem_connectedComponentIn hy
    have hx' : x ∈ connectedComponentIn U x := mem_connectedComponentIn hx
    rcases le_total x y with hxy | hyx
    · have hzI : (1 - t) * x + t * y ∈ Icc x y := by
        refine ⟨?_, ?_⟩ <;> nlinarith [ht.1, ht.2]
      exact connectedComponentIn_subset U x (hpre.Icc_subset hx' hy' hzI)
    · have hzI : (1 - t) * x + t * y ∈ Icc y x := by
        refine ⟨?_, ?_⟩ <;> nlinarith [ht.1, ht.2]
      exact connectedComponentIn_subset U x (hpre.Icc_subset hy' hx' hzI)

/-- **The segment-positivity criterion for the ray surplus.**  Two active ray
parameters lie in the same active component iff the surplus is positive on the
whole segment between them. -/
theorem rayFlux_segment_pos_iff_component_eq (κ : Measure (ℝ × ℝ)) {x y : ℝ}
    (hx : 0 < rayFlux κ x) (hy : 0 < rayFlux κ y) :
    (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < rayFlux κ ((1 - t) * x + t * y)) ↔
      connectedComponentIn {r : ℝ | 0 < rayFlux κ r} x =
        connectedComponentIn {r : ℝ | 0 < rayFlux κ r} y :=
  segment_subset_iff_connectedComponentIn_eq (U := {r : ℝ | 0 < rayFlux κ r}) hx hy

/-! ## The rational active marker and the rational-code cover -/

/-- Every active ray parameter has a rational point of its component at which
the surplus is positive: the rational curve code of the minimal-arc transport
makes the least-index marker well defined. -/
theorem exists_rat_rayFlux_component (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ]
    (hforward : κ {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : ∀ r : ℝ, κ {p : ℝ × ℝ | p.1 = r} = 0)
    (G : Set (ℝ × ℝ)) (hGnull : κ Gᶜ = 0)
    (hsupp : ∀ p ∈ G, ∀ U : Set (ℝ × ℝ), IsOpen U → p ∈ U → 0 < κ U)
    {r : ℝ} (hr : 0 < rayFlux κ r) :
    ∃ q : ℚ, ((q : ℝ) ∈ connectedComponentIn {r : ℝ | 0 < rayFlux κ r} r) ∧
      0 < rayFlux κ (q : ℝ) := by
  have hU : IsOpen {r : ℝ | 0 < rayFlux κ r} :=
    isOpen_pos_rayFlux κ hforward hatom G hGnull hsupp
  obtain ⟨q, hqmem, -⟩ := exists_rat_connectedComponentIn_eq hU hr
  have hmem : (q : ℝ) ∈ {r : ℝ | 0 < rayFlux κ r} :=
    connectedComponentIn_subset {r : ℝ | 0 < rayFlux κ r} r hqmem
  exact ⟨q, hqmem, hmem⟩

/-- **Rational-code cover of the active set.**  Unconditionally from the ray
hypotheses (forward coupling, atomless first marginal, a full-measure supporting
set), the active set of the ray is covered by the components of the rational
curve codes: these are the paper's active blocks `C_φ(z,I)` indexed by
rationals. -/
theorem exists_component_cover_of_rayFlux (κ : Measure (ℝ × ℝ)) [IsFiniteMeasure κ]
    (hforward : κ {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : ∀ r : ℝ, κ {p : ℝ × ℝ | p.1 = r} = 0)
    (G : Set (ℝ × ℝ)) (hGnull : κ Gᶜ = 0)
    (hsupp : ∀ p ∈ G, ∀ U : Set (ℝ × ℝ), IsOpen U → p ∈ U → 0 < κ U) :
    ∃ comp : ℚ → Set ℝ,
      (∀ q : ℚ, comp q = ∅ ∨ ∃ x : ℝ, 0 < rayFlux κ x ∧
        comp q = connectedComponentIn {r : ℝ | 0 < rayFlux κ r} x) ∧
      (∀ r : ℝ, 0 < rayFlux κ r → ∃ q : ℚ, r ∈ comp q) := by
  classical
  have hU : IsOpen {r : ℝ | 0 < rayFlux κ r} :=
    isOpen_pos_rayFlux κ hforward hatom G hGnull hsupp
  let c : ℝ → ℚ := fun r =>
    if hr : 0 < rayFlux κ r then
      Classical.choose (exists_rat_rayFlux_component κ hforward hatom G hGnull hsupp hr)
    else 0
  have hc : ∀ r : ℝ, 0 < rayFlux κ r →
      (c r : ℝ) ∈ connectedComponentIn {r : ℝ | 0 < rayFlux κ r} r := by
    intro r hr
    have hspec := Classical.choose_spec
      (exists_rat_rayFlux_component κ hforward hatom G hGnull hsupp hr)
    have h0 : c r = Classical.choose
        (exists_rat_rayFlux_component κ hforward hatom G hGnull hsupp hr) := by
      simp only [c]
      exact dif_pos hr
    have hmem : ((Classical.choose
        (exists_rat_rayFlux_component κ hforward hatom G hGnull hsupp hr) : ℚ) : ℝ) ∈
        connectedComponentIn {r : ℝ | 0 < rayFlux κ r} r := hspec.1
    rwa [← h0] at hmem
  exact exists_component_cover_of_rational_codes hU c hc

/-- **Rational-code cover of a whole family of rays.**  The active sets of all
rays of a family are covered by the components of their rational curve codes,
unconditionally from the ray hypotheses. -/
theorem exists_component_cover_family_of_rayFlux {Z : Type*}
    (κ : Z → Measure (ℝ × ℝ)) (hfin : ∀ z : Z, IsFiniteMeasure (κ z))
    (hforward : ∀ z : Z, κ z {p : ℝ × ℝ | ¬ p.1 ≤ p.2} = 0)
    (hatom : ∀ (z : Z) (r : ℝ), κ z {p : ℝ × ℝ | p.1 = r} = 0)
    (G : Z → Set (ℝ × ℝ)) (hGnull : ∀ z : Z, κ z (G z)ᶜ = 0)
    (hsupp : ∀ (z : Z) (p : ℝ × ℝ), p ∈ G z →
      ∀ U : Set (ℝ × ℝ), IsOpen U → p ∈ U → 0 < κ z U) :
    ∃ comp : Z → ℚ → Set ℝ,
      (∀ (z : Z) (q : ℚ), comp z q = ∅ ∨ ∃ x : ℝ, 0 < rayFlux (κ z) x ∧
        comp z q = connectedComponentIn {r : ℝ | 0 < rayFlux (κ z) r} x) ∧
      (∀ (z : Z) (r : ℝ), 0 < rayFlux (κ z) r → ∃ q : ℚ, r ∈ comp z q) := by
  classical
  have hex : ∀ z : Z, ∃ comp : ℚ → Set ℝ,
      (∀ q : ℚ, comp q = ∅ ∨ ∃ x : ℝ, 0 < rayFlux (κ z) x ∧
        comp q = connectedComponentIn {r : ℝ | 0 < rayFlux (κ z) r} x) ∧
      (∀ r : ℝ, 0 < rayFlux (κ z) r → ∃ q : ℚ, r ∈ comp q) := by
    intro z
    letI : IsFiniteMeasure (κ z) := hfin z
    exact exists_component_cover_of_rayFlux (κ z) (hforward z) (hatom z) (G z)
      (hGnull z) (fun p hp => hsupp z p hp)
  choose comp hcomp using hex
  exact ⟨comp, fun z => (hcomp z).1, fun z => (hcomp z).2⟩


/-! ## The infimum (minimum) form of the segment test -/

/-- The paper's segment test value: the infimum of the surplus over the
compact segment between two ray parameters.  Under continuity of the surplus
this infimum is attained, so strict positivity of this infimum is equivalent to
the segment containment form of `segment_subset_iff_connectedComponentIn_eq`
(the paper's `eq:intrinsic-active-marker`). -/
def segmentMin (H : ℝ → ℝ) (x y : ℝ) : ℝ :=
  sInf ((fun t : ℝ => H ((1 - t) * x + t * y)) '' Icc (0 : ℝ) 1)

/-- **The infimum form of the segment-positivity criterion.**  For a continuous
surplus, the infimum over the segment is positive iff the surplus is positive at
every point of the segment.  (Strictly stronger than pointwise positivity on the
rational segment parameters: the infimum detects an irrational zero on the
segment.) -/
theorem segmentMin_pos_iff {H : ℝ → ℝ} (hH : Continuous H) {x y : ℝ} :
    0 < segmentMin H x y ↔
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < H ((1 - t) * x + t * y) := by
  have hcont : Continuous fun t : ℝ => H ((1 - t) * x + t * y) :=
    hH.comp (by fun_prop)
  have hS : IsCompact ((fun t : ℝ => H ((1 - t) * x + t * y)) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image hcont
  have hSne : ((fun t : ℝ => H ((1 - t) * x + t * y)) '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨H ((1 - 0) * x + 0 * y), ⟨0, by norm_num, rfl⟩⟩
  constructor
  · intro hmin t ht
    have hmem : H ((1 - t) * x + t * y) ∈
        (fun t : ℝ => H ((1 - t) * x + t * y)) '' Icc (0 : ℝ) 1 :=
      ⟨t, ht, rfl⟩
    exact lt_of_lt_of_le hmin (csInf_le hS.bddBelow hmem)
  · intro hpos
    have hmem : sInf ((fun t : ℝ => H ((1 - t) * x + t * y)) '' Icc (0 : ℝ) 1) ∈
        (fun t : ℝ => H ((1 - t) * x + t * y)) '' Icc (0 : ℝ) 1 :=
      hS.sInf_mem hSne
    obtain ⟨t, ht, hft⟩ := hmem
    rw [segmentMin, ← hft]
    exact hpos t ht

/-- **The marker criterion for a continuous surplus.**  Two active parameters
of a continuous surplus satisfy the paper's strict segment test
`inf_{u∈[0,1]} H((1-u)x + uy) > 0` iff they lie in the same component of the
active set: exactly the criterion used to define the least-index block space of
`eq:intrinsic-active-marker`. -/
theorem segmentMin_pos_iff_connectedComponentIn_eq {H : ℝ → ℝ} (hH : Continuous H)
    {x y : ℝ} (hx : 0 < H x) (hy : 0 < H y) :
    0 < segmentMin H x y ↔
      connectedComponentIn {r : ℝ | 0 < H r} x =
        connectedComponentIn {r : ℝ | 0 < H r} y := by
  rw [segmentMin_pos_iff hH]
  exact segment_subset_iff_connectedComponentIn_eq (U := {r : ℝ | 0 < H r}) hx hy

end OTSelector.Reconstruction
end
end
