import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Intrinsic active-block invariance of optimal potentials (paper reduction)

This module formalizes the order-theoretic and algebraic core of the paper's
structural theorem `thm:intrinsic-active-invariance` (`main.tex`:958), the
statement that the active-ray block decomposition of the optimal face and its
ray quotient do not depend on the chosen optimal potential.  The paper's deeper
geometric input is the cover identity `eq:intrinsic-active-cover` and the
two-cover + connectedness argument of its proof (`main.tex`:990-1035), built on
`prop:general-optimal-face` (`main.tex`:422) and
`prop:ray-forward-criterion` (`main.tex`:524).

We record the paper's active-block objects for one potential as
`IntrinsicActiveRayData`: a whole-ray label space `Z`, a flux
`flux z r = H_z(r)` on each ray parameter, and the active blocks
`block z j` indexed by the rational-enumeration label of
`eq:intrinsic-active-marker`.  The structure keeps exactly the order
properties used by the structural argument:

* blocks are nonempty;
* distinct blocks on the same ray are disjoint;
* blocks lie in the positive-flux set;
* the positive-flux set is the union of the blocks (`eq:intrinsic-active-cover`).

The main theorem `intrinsic_active_block_invariance` takes the paper's
two-cover containment input (every block of one potential is contained in a
block of the other and conversely, the geometric content established in the
paper's proof) and concludes, on the same whole-ray label:

* a block-label matching `T` with `block_phi z j = block_psi z (T z j)`,
  injective in the block label (this is the paper's block bijection at the
  order-set level);
* `psi - phi` is constant on every identified calibrated arc, since both
  potentials increase by arclength on it.

`quotientLaw_eq_pushforward` records the paper's final quotient-law step
`eta_psi = T_# eta_phi`: once the block maps satisfy `b_psi = T ∘ b_phi`,
the quotient law of `phi` pushes forward to the quotient law of `psi`.

The exact reduction boundary: the construction of the intrinsic ray data
(flux functions `H_z^phi`, transported arcs, the Borel block space and its
conullness, the conull block maps and quotient laws of
`eq:intrinsic-active-quotient`), the measurability of `T`, and the geometric
two-cover containment are the remaining analytic/geometric inputs; they are
kept as explicit structure fields and hypotheses here rather than re-proved.
This is the strongest order-theoretic form of the paper's structural statement
that does not depend on those still-unformalized constructions.
-/

open Set Function MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option linter.unusedVariables false

/-! ## Active-ray block data for one optimal potential -/

/-- The active-ray block decomposition of the optimal face for one fixed
optimal potential, in the abstract order form used by the two-cover /
connectedness argument of the paper's structural invariance theorem.

`flux z r` is `H_z(r)`; `block z j` is the active block selected by the
first rational index of the positive-flux component containing `r`
(`eq:intrinsic-active-marker`). -/
structure IntrinsicActiveRayData (Z : Type*) where
  /-- The positive-flux function `H_z` on the ray parameter. -/
  flux : Z → ℝ → ℝ
  /-- The active block selected by the rational-enumeration block label. -/
  block : Z → ℕ → Set ℝ
  /-- Active blocks are nonempty. -/
  nonempty : ∀ z j, (block z j).Nonempty
  /-- Distinct active blocks on the same ray are disjoint. -/
  disjoint : ∀ z j k, j ≠ k → Disjoint (block z j) (block z k)
  /-- Active blocks lie in the positive-flux set. -/
  block_pos : ∀ z j ⦃r : ℝ⦄, r ∈ block z j → 0 < flux z r
  /-- Cover identity `eq:intrinsic-active-cover`: every positive-flux ray
  parameter lies in an active block. -/
  cover_pos : ∀ z r, 0 < flux z r → ∃ j, r ∈ block z j

/-- **Cover identity `eq:intrinsic-active-cover`.**
The positive-flux set of every whole ray is exactly the union of the active
blocks of that ray. -/
theorem positiveFlux_eq_iUnion_blocks {Z : Type*} (D : IntrinsicActiveRayData Z)
    (z : Z) :
    {r : ℝ | 0 < D.flux z r} = ⋃ j, D.block z j := by
  ext r
  constructor
  · intro hr
    obtain ⟨j, hj⟩ := D.cover_pos z r hr
    exact mem_iUnion.mpr ⟨j, hj⟩
  · intro hr
    obtain ⟨j, hj⟩ := mem_iUnion.mp hr
    exact D.block_pos z j hj

/-! ## The two-cover / connectedness block matching -/

/-- **Two-cover + connectedness block matching.**
If every active block of one optimal potential is contained in an active block
of another and conversely (the geometric containment established by the
paper's two-cover argument), then the block families agree up to an injective
block-label matching `T`:
`block_phi z j = block_psi z (T z j)`.

The proof is the paper's final disjointness/connectedness step: from
`C ⊆ D ⊆ C'` with `C, C'` disjoint blocks of the same potential and `C`
nonempty, one gets `C = C'`, hence `C = D`. -/
theorem block_matching_of_cross_cover {Z : Type*}
    (A B : IntrinsicActiveRayData Z)
    (hAB : ∀ z j, ∃ k, A.block z j ⊆ B.block z k)
    (hBA : ∀ z k, ∃ j, B.block z k ⊆ A.block z j) :
    ∃ T : Z → ℕ → ℕ,
      (∀ z j, A.block z j = B.block z (T z j)) ∧
      (∀ z j k, T z j = T z k → j = k) := by
  classical
  have hkey : ∀ z j, ∃ k, A.block z j = B.block z k := by
    intro z j
    obtain ⟨k, hk⟩ := hAB z j
    obtain ⟨j', hj'⟩ := hBA z k
    have hsub : A.block z j ⊆ A.block z j' := hk.trans hj'
    have hjeq : j = j' := by
      by_contra hne
      have hdisj : Disjoint (A.block z j) (A.block z j') := A.disjoint z j j' hne
      have hbot : A.block z j = ∅ := by
        have hsub_empty : A.block z j ⊆ (∅ : Set ℝ) := by
          intro r hr
          exact (Set.disjoint_left.mp hdisj hr) (hsub hr)
        simpa using hsub_empty
      exact (A.nonempty z j).ne_empty hbot
    subst hjeq
    exact ⟨k, Subset.antisymm hk hj'⟩
  let T : Z → ℕ → ℕ := fun z j ↦ Classical.choose (hkey z j)
  have hT : ∀ z j, A.block z j = B.block z (T z j) :=
    fun z j ↦ Classical.choose_spec (hkey z j)
  refine ⟨T, hT, ?_⟩
  intro z j k hjk
  by_contra hne
  have hsubset : A.block z j ⊆ A.block z k := by
    rw [hT z j, hT z k, hjk]
  have hdisj : Disjoint (A.block z j) (A.block z k) := A.disjoint z j k hne
  have hbot : A.block z j = ∅ := by
    have hsub_empty : A.block z j ⊆ (∅ : Set ℝ) := by
      intro r hr
      exact (Set.disjoint_left.mp hdisj hr) (hsubset hr)
    simpa using hsub_empty
  exact (A.nonempty z j).ne_empty hbot

/-! ## `psi - phi` is constant on identified calibrated arcs -/

/-- **Algebraic arc-constant step.**
If two optimal potentials calibrate every ordered pair of a transported set
(both satisfy `u y - u x = dist x y` on it), then their difference is constant
on that set.  In the paper this is applied to the identified minimal arcs,
on which both potentials increase by arclength. -/
theorem potentialDifference_const_of_double_calibration
    {M : Type*} [MetricSpace M] (φ ψ : M → ℝ) {S : Set M}
    (hφ : ∀ x ∈ S, ∀ y ∈ S, φ y - φ x = dist x y)
    (hψ : ∀ x ∈ S, ∀ y ∈ S, ψ y - ψ x = dist x y) :
    ∀ x ∈ S, ∀ y ∈ S, ψ y - φ y = ψ x - φ x := by
  intro x hx y hy
  have h1 := hφ x hx y hy
  have h2 := hψ x hx y hy
  linarith

/-- **Arclength form of the arc-constant step.**
If both potentials increase by arclength along a parametrized calibrated arc,
then their difference is constant along the arc endpoints. -/
theorem potentialDifference_const_of_arclength
    {M Z : Type*} (φ ψ : M → ℝ) (arc : Z → ℝ → M × M) (z : Z)
    (hφ : ∀ r s : ℝ, r ≤ s → φ ((arc z s).2) - φ ((arc z r).2) = s - r)
    (hψ : ∀ r s : ℝ, r ≤ s → ψ ((arc z s).2) - ψ ((arc z r).2) = s - r)
    {r s : ℝ} (hrs : r ≤ s) :
    ψ ((arc z s).2) - φ ((arc z s).2) = ψ ((arc z r).2) - φ ((arc z r).2) := by
  have h1 := hφ r s hrs
  have h2 := hψ r s hrs
  linarith

/-! ## Structural active-block invariance (paper reduction) -/

/-- **Structural active-block invariance of two optimal potentials**
(`thm:intrinsic-active-invariance`, order-set and arc part).

Given the two-cover containment input between the active blocks of two optimal
potentials (the geometric content of the paper's proof) and the fact that both
potentials increase by arclength on every active block, the active blocks agree
up to an injective block-label matching `T`, and `psi - phi` is constant on
every identified calibrated arc.

The construction of the intrinsic ray data, the Borel structure of the block
space and of `T`, the conullness statements, and the geometric two-cover
containment are the remaining paper inputs (see the module documentation). -/
theorem intrinsic_active_block_invariance
    {M Z : Type*} (φ ψ : M → ℝ) (arc : Z → ℝ → M × M)
    (A B : IntrinsicActiveRayData Z)
    (hAB : ∀ (z : Z) (j : ℕ), ∃ k : ℕ, A.block z j ⊆ B.block z k)
    (hBA : ∀ (z : Z) (k : ℕ), ∃ j : ℕ, B.block z k ⊆ A.block z j)
    (hφarc : ∀ (z : Z) (j : ℕ) (r s : ℝ), r ∈ A.block z j → s ∈ A.block z j →
      φ ((arc z s).2) - φ ((arc z r).2) = s - r)
    (hψarc : ∀ (z : Z) (k : ℕ) (r s : ℝ), r ∈ B.block z k → s ∈ B.block z k →
      ψ ((arc z s).2) - ψ ((arc z r).2) = s - r) :
    ∃ T : Z → ℕ → ℕ,
      (∀ (z : Z) (j : ℕ), A.block z j = B.block z (T z j)) ∧
      (∀ (z : Z) (j k : ℕ), T z j = T z k → j = k) ∧
      (∀ (z : Z) (j : ℕ) (r s : ℝ), r ∈ A.block z j → s ∈ A.block z j →
        ψ ((arc z s).2) - φ ((arc z s).2) =
          ψ ((arc z r).2) - φ ((arc z r).2)) := by
  obtain ⟨T, hT, hinj⟩ := block_matching_of_cross_cover A B hAB hBA
  refine ⟨T, hT, hinj, ?_⟩
  intro z j r s hr hs
  have hrB : r ∈ B.block z (T z j) := by
    rw [← hT z j]
    exact hr
  have hsB : s ∈ B.block z (T z j) := by
    rw [← hT z j]
    exact hs
  have h1 := hφarc z j r s hr hs
  have h2 := hψarc z (T z j) r s hrB hsB
  linarith

/-- **Quotient-law invariance `eq:intrinsic-active-quotient`.**
Once the block maps of the two potentials satisfy `b_psi = T ∘ b_phi`, the
quotient law `eta_phi = (b_phi)_# law` pushes forward to the quotient law
`eta_psi = (b_psi)_# law`: `eta_psi = T_# eta_phi`. -/
theorem quotientLaw_eq_pushforward
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (law : Measure Ω) (bφ bψ : Ω → Z) (T : Z → Z)
    (hbφ : Measurable bφ) (hbψ : Measurable bψ) (hT : Measurable T)
    (hcomp : bψ = T ∘ bφ) :
    law.map bψ = (law.map bφ).map T := by
  rw [hcomp, Measure.map_map hT hbφ]

end OTSelector.Reconstruction