import OTSelector.MeasureTheory.IteratedWeakSourceDomination
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.ProjectedDominationDiscard
import OTSelector.Topology.ENNRealVanishingThresholds
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedProjectedSourceAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedProjectedSourceAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ProjectedSourceAbsoluteContinuity

## Lemma skeleton

* **Conditions:** The same projected full scene law at every accuracy, continuous locally finite full plan, retained open-source domination, vanishing retained/reference error and discard tail bounds.
* **Objects:** Almost-everywhere absolute continuity of the original localized source marginal.
* **Proof detail:** Extend open-set defects to all sets by outer regularity, form closed measurable simultaneous good carriers, choose positive thresholds with loss/threshold tending to zero and use projected approximate domination.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=59): Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).

Source relation (composition): Original-law absolute-continuity assembly; thresholds and good carriers are constructed rather than independently assumed.
-/

/-!
# Absolute continuity from the same projected full scene

Closed simultaneous source-window bounds provide the measurable good carriers.
Only the original retained reference error and original discard loss tend to
zero; positive thresholds and their failure-probability decay are constructed
internally, keeping the full scene law fixed throughout accuracy refinement.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [T2Space Y] [LocallyCompactSpace Y] [PseudoMetrizableSpace Y]
  [SigmaCompactSpace Y] [SecondCountableTopology Y]

/-- For each fixed outer-regular reference, the closed all-open carrier is
exactly the simultaneous setwise bound on the same source restriction. -/
theorem sourceOpenDominationDefectOn_iff_all_sets
    (π : Measure (X × Y)) (U : Set X) (hU : MeasurableSet U)
    (ν : Measure X) [ν.OuterRegular] (δ : ℝ≥0∞) :
    sourceOpenDominationDefectOn π U ν δ ↔
      ∀ B : Set X, π.fst.restrict U B ≤ ν B + δ := by
  constructor
  · intro h B
    rw [Measure.restrict_apply' hU]
    exact sourceOpenDominationDefectOn_fst_inter_apply_le π U hU ν δ h B
  · intro h O hO
    have hh := h O
    rw [Measure.restrict_apply' hU, Measure.fst,
      Measure.map_apply measurable_fst (hO.measurableSet.inter hU)] at hh
    have heq : (Prod.fst : X × Y → X) ⁻¹' (O ∩ U) = (O ∩ U) ×ˢ univ := by
      ext e
      simp
    rwa [heq] at hh

/-- The actual closed source carrier removes the measurable-good-event oracle
from the exact projected retained/discard AC theorem. All auxiliary laws retain
the same full scene law, and all targets are included in the source readout. -/
theorem ae_absolutelyContinuous_source_restrict_of_projected_retained_discard
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)]
    (R : Measure S) (P : ∀ n, Measure (A n))
    (projection : ∀ n, A n → S)
    (hprojection : ∀ n, Measurable (projection n))
    (hmap : ∀ n, (P n).map (projection n) = R)
    (full : S → LocalFiniteMeasure (X × Y)) (hfull : Continuous full)
    (retained : ∀ n, A n → Measure (X × Y))
    (U : Set X) (hU : IsOpen U) (reference : Measure X)
    (approximant : ℕ → Measure X) [∀ n, (approximant n).OuterRegular]
    (hac : ∀ n, approximant n ≪ reference)
    (discard : ∀ n, A n → ℝ≥0∞) (error loss : ℕ → ℝ≥0∞)
    (herror : Tendsto error atTop (𝓝 0))
    (hloss : Tendsto loss atTop (𝓝 0))
    (hsplit : ∀ n, ∀ᵐ a ∂P n, ∀ B : Set X,
      (full (projection n a) : Measure (X × Y)).fst (B ∩ U) ≤
        (retained n a).fst (B ∩ U) + discard n a)
    (hretained : ∀ n, ∀ᵐ a ∂P n,
      sourceOpenDominationDefectOn (retained n a) U (approximant n) (error n))
    (htail : ∀ n (threshold : ℝ≥0∞), 0 < threshold → threshold ≠ ⊤ →
      P n {a | threshold < discard n a} ≤ loss n / threshold) :
    ∀ᵐ s ∂R, (full s : Measure (X × Y)).fst.restrict U ≪ reference := by
  obtain ⟨threshold, hthresholdBounds, hthreshold, hratio⟩ :=
    exists_vanishing_discard_thresholds loss hloss
  let G : ℕ → Set S := fun n ↦
    {s | sourceOpenDominationDefectOn (full s : Measure (X × Y)) U
      (approximant n) (error n + threshold n)}
  have hGmeas (n : ℕ) : MeasurableSet (G n) :=
    ((isClosed_sourceOpenDominationDefectOn U hU (approximant n)
      (error n + threshold n)).preimage hfull).measurableSet
  apply ae_absolutelyContinuous_of_projected_domination_discard_bounds R P projection
    hprojection hmap
    (fun s ↦ (full s : Measure (X × Y)).fst.restrict U) reference approximant hac
    (fun n a ↦ (retained n a).fst.restrict U) discard error threshold loss
    herror hthreshold hratio ?_ ?_
    (fun n ↦ htail n (threshold n) (hthresholdBounds n).1 (hthresholdBounds n).2) G hGmeas ?_
  · intro n
    filter_upwards [hsplit n] with a ha B
    simpa only [Measure.restrict_apply' hU.measurableSet] using ha B
  · intro n
    filter_upwards [hretained n] with a ha
    exact (sourceOpenDominationDefectOn_iff_all_sets (retained n a) U hU.measurableSet
      (approximant n) (error n)).mp ha
  · intro n s
    exact sourceOpenDominationDefectOn_iff_all_sets
      (full s : Measure (X × Y)) U hU.measurableSet (approximant n) (error n + threshold n)

end OTSelector.Reconstruction

end
end
