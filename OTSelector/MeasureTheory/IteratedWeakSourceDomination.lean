import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.MeasureTheory.LocalFiniteMeasure
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceDominationCarrier.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceDominationCarrier`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakSourceDomination

## Lemma skeleton

* **Conditions:** Outer-regular reference measures and full or localized open-source-set bounds with nonnegative error; scene-valued plans are continuous and weak limits are supplied.
* **Objects:** Closed domination-defect carriers, bounds on all source sets and absolute continuity after errors vanish, locally and globally on a countable source cover.
* **Proof detail:** Use outer regularity to extend open bounds to arbitrary sets. Open-rectangle lower semicontinuity makes the carrier closed, so weak carrying passes through each limit; apply the vanishing-error bound to null sets and assemble the countable localization.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).

Source relation (composition): Quantitative open-set domination framework with actual nonproper projections; no source marginal finiteness or density bound is presumed.
-/

/-!
# Closed approximate domination of the full nonproper source marginal

For one fixed reference measure and scalar defect, simultaneous bounds on ALL
open source windows form a closed carrier of actual vague plans. The same
carrier survives both original weak stages. References may then vary with a
separate accuracy index: outer regularity and vanishing scalar defects yield
pathwise source absolute continuity with respect to their common reference.
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

/-- Simultaneous ALL-target open source-window domination by one deterministic
reference, up to a scalar additive defect. No source-marginal finiteness is used. -/
def sourceOpenDominationDefect (π : Measure (X × Y)) (ν : Measure X) (δ : ℝ≥0∞) : Prop :=
  ∀ O : Set X, IsOpen O → π (O ×ˢ univ) ≤ ν O + δ

/-- Enlarging the scalar defect preserves all original source-window bounds. -/
theorem sourceOpenDominationDefect_mono (π : Measure (X × Y)) (ν : Measure X)
    {δ ε : ℝ≥0∞} (hδε : δ ≤ ε) (h : sourceOpenDominationDefect π ν δ) :
    sourceOpenDominationDefect π ν ε :=
  fun O hO ↦ (h O hO).trans (add_le_add le_rfl hδε)

/-- Outer regularity of each fixed reference extends its open-window defect
bound to EVERY source set, including nonmeasurable null subsets. -/
theorem sourceOpenDominationDefect_fst_apply_le
    (π : Measure (X × Y)) (ν : Measure X) [ν.OuterRegular] (δ : ℝ≥0∞)
    (h : sourceOpenDominationDefect π ν δ) (B : Set X) : π.fst B ≤ ν B + δ := by
  calc
    π.fst B ≤ ⨅ (O : Set X) (_ : B ⊆ O) (_ : IsOpen O), ν O + δ := by
      refine le_iInf fun O ↦ le_iInf fun hBO ↦ le_iInf fun hO ↦ ?_
      calc
        π.fst B ≤ π.fst O := measure_mono hBO
        _ = π (O ×ˢ univ) := by
          rw [Measure.fst, Measure.map_apply measurable_fst hO.measurableSet]
          congr 1
          ext e
          simp
        _ ≤ ν O + δ := h O hO
    _ = (⨅ (O : Set X) (_ : B ⊆ O) (_ : IsOpen O), ν O) + δ := by
      simp only [ENNReal.iInf_add]
    _ = ν B + δ := by rw [← B.measure_eq_iInf_isOpen ν]

/-- Arbitrary outer-regular approximate references may change with accuracy.
If each is absolutely continuous with respect to the SAME measure and scalar
defects vanish, the full nonproper source marginal is absolutely continuous. -/
theorem absolutelyContinuous_fst_of_vanishing_sourceOpenDominationDefects
    (π : Measure (X × Y)) (m : Measure X) (ν : ℕ → Measure X)
    [∀ k, (ν k).OuterRegular]
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (hν : ∀ k, ν k ≪ m)
    (h : ∀ k, sourceOpenDominationDefect π (ν k) (δ k)) : π.fst ≪ m := by
  intro B hB
  have hb (k : ℕ) : π.fst B ≤ δ k := by
    simpa only [hν k hB, zero_add] using
      sourceOpenDominationDefect_fst_apply_le π (ν k) (δ k) (h k) B
  exact le_antisymm (ge_of_tendsto hδ (Eventually.of_forall hb)) bot_le

/-- The simultaneous ALL-open-source-window defect bound is closed on the
actual vague carrier. No countable intersection of test-wise AE claims is used. -/
theorem isClosed_sourceOpenDominationDefect (ν : Measure X) (δ : ℝ≥0∞) :
    IsClosed {π : LocalFiniteMeasure (X × Y) |
      sourceOpenDominationDefect (π : Measure (X × Y)) ν δ} := by
  change IsClosed {π : LocalFiniteMeasure (X × Y) |
    ∀ O : Set X, ∀ _ : IsOpen O, (π : Measure (X × Y)) (O ×ˢ univ) ≤ ν O + δ}
  simp only [ofPred_forall]
  exact isClosed_iInter fun O ↦ isClosed_iInter fun hO ↦
    (LocalFiniteMeasure.lowerSemicontinuous_measure_open (hO.prod isOpen_univ)).isClosed_preimage
      (ν O + δ)

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- One closed simultaneous source-domination carrier survives an actual
weak limit of the SAME laws, with its fixed original reference and defect. -/
theorem ae_sourceOpenDominationDefect_of_weak_tendsto
    (R : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (ν : Measure X) (δ : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn n : Measure S),
      sourceOpenDominationDefect (plan s : Measure (X × Y)) ν δ) :
    ∀ᵐ s ∂(R : Measure S), sourceOpenDominationDefect (plan s : Measure (X × Y)) ν δ := by
  let K : Set S := {s | sourceOpenDominationDefect (plan s : Measure (X × Y)) ν δ}
  have hK : IsClosed K := (isClosed_sourceOpenDominationDefect ν δ).preimage hplan
  have hn : ∀ᶠ n in atTop, (Pn n : Measure S) Kᶜ = 0 := hbound
  have hlim : atTop.liminf (fun n ↦ (Pn n : Measure S) Kᶜ) = 0 :=
    (liminf_congr hn).trans (liminf_const 0)
  change (R : Measure S) Kᶜ = 0
  exact le_antisymm
    ((ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl).trans_eq hlim)
    bot_le

/-- The SAME simultaneous source-domination carrier survives the fixed-tilt
sample limit and then the outer tilt-index limit, with no new scene law. -/
theorem ae_sourceOpenDominationDefect_of_iterated_weak
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (ν : Measure X) (δ : ℝ≥0∞)
    (hbound : ∀ ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn ℓ n : Measure S),
      sourceOpenDominationDefect (plan s : Measure (X × Y)) ν δ) :
    ∀ᵐ s ∂(R : Measure S), sourceOpenDominationDefect (plan s : Measure (X × Y)) ν δ := by
  have hQ (ℓ : ℕ) : ∀ᵐ s ∂(Q ℓ : Measure S),
      sourceOpenDominationDefect (plan s : Measure (X × Y)) ν δ :=
    ae_sourceOpenDominationDefect_of_weak_tendsto (Q ℓ) (fun n ↦ Pn ℓ (φ ℓ n))
      (hinner ℓ) plan hplan ν δ ((hφ ℓ).eventually (hbound ℓ))
  exact ae_sourceOpenDominationDefect_of_weak_tendsto R (fun ℓ ↦ Q (ψ ℓ)) houter
    plan hplan ν δ (Eventually.of_forall fun ℓ ↦ hQ (ψ ℓ))

/-- For each accuracy the fixed closed carrier keeps its reference and scalar
defect through the SAME laws and SAME two weak limits. Only afterward does
accuracy tend to infinity, producing pathwise full source absolute continuity. -/
theorem ae_absolutelyContinuous_fst_of_iterated_weak_sourceOpenDominationDefects
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (m : Measure X) (ν : ℕ → Measure X) [∀ k, (ν k).OuterRegular]
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (hν : ∀ k, ν k ≪ m)
    (hbound : ∀ k ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn ℓ n : Measure S),
      sourceOpenDominationDefect (plan s : Measure (X × Y)) (ν k) (δ k)) :
    ∀ᵐ s ∂(R : Measure S), (plan s : Measure (X × Y)).fst ≪ m := by
  have hall : ∀ᵐ s ∂(R : Measure S), ∀ k,
      sourceOpenDominationDefect (plan s : Measure (X × Y)) (ν k) (δ k) := by
    apply ae_all_iff.mpr
    intro k
    exact ae_sourceOpenDominationDefect_of_iterated_weak Pn Q R φ hφ ψ hinner houter
      plan hplan (ν k) (δ k) (hbound k)
  filter_upwards [hall] with s hs
  exact absolutelyContinuous_fst_of_vanishing_sourceOpenDominationDefects
    (plan s : Measure (X × Y)) m ν δ hδ hν hs


/-- Simultaneous source-window defect bounds localized INSIDE one fixed source
endpoint set. The actual plan remains unchanged and all targets are included. -/
def sourceOpenDominationDefectOn (π : Measure (X × Y)) (U : Set X)
    (ν : Measure X) (δ : ℝ≥0∞) : Prop :=
  ∀ O : Set X, IsOpen O → π ((O ∩ U) ×ˢ univ) ≤ ν O + δ

/-- Localizing only the source endpoint has the literal original restricted
measure interpretation, without any continuity claim for restriction itself. -/
theorem sourceOpenDominationDefectOn_iff_restrict
    (π : Measure (X × Y)) (U : Set X) (ν : Measure X) (δ : ℝ≥0∞) :
    sourceOpenDominationDefectOn π U ν δ ↔
      sourceOpenDominationDefect (π.restrict (U ×ˢ univ)) ν δ := by
  constructor
  · intro h O hO
    simpa only [Measure.restrict_apply (hO.measurableSet.prod MeasurableSet.univ),
      Set.prod_inter_prod, Set.inter_self] using h O hO
  · intro h O hO
    simpa only [Measure.restrict_apply (hO.measurableSet.prod MeasurableSet.univ),
      Set.prod_inter_prod, Set.inter_self] using h O hO

/-- The original source-restricted product plan has exactly the restriction of
its original full source marginal, for every measurable source window. -/
theorem fst_restrict_sourceProduct_eq_restrict_fst
    (π : Measure (X × Y)) (U : Set X) (hU : MeasurableSet U) :
    (π.restrict (U ×ˢ univ)).fst = π.fst.restrict U := by
  symm
  change (π.map Prod.fst).restrict U = (π.restrict (U ×ˢ univ)).map Prod.fst
  have hpre : (Prod.fst : X × Y → X) ⁻¹' U = U ×ˢ univ := by ext e; simp
  rw [Measure.restrict_map measurable_fst hU, hpre]

/-- Outer regularity upgrades localized ALL-open tests to a defect bound on
EVERY source set of the original source-restricted plan. -/
theorem sourceOpenDominationDefectOn_fst_restrict_apply_le
    (π : Measure (X × Y)) (U : Set X) (ν : Measure X) [ν.OuterRegular]
    (δ : ℝ≥0∞) (h : sourceOpenDominationDefectOn π U ν δ) (B : Set X) :
    (π.restrict (U ×ˢ univ)).fst B ≤ ν B + δ :=
  sourceOpenDominationDefect_fst_apply_le (π.restrict (U ×ˢ univ)) ν δ
    ((sourceOpenDominationDefectOn_iff_restrict π U ν δ).mp h) B

/-- The localized open carrier bounds the original full source measure on
B ∩ U for EVERY B, exactly the universal setwise defect interface. -/
theorem sourceOpenDominationDefectOn_fst_inter_apply_le
    (π : Measure (X × Y)) (U : Set X) (hU : MeasurableSet U)
    (ν : Measure X) [ν.OuterRegular] (δ : ℝ≥0∞)
    (h : sourceOpenDominationDefectOn π U ν δ) (B : Set X) :
    π.fst (B ∩ U) ≤ ν B + δ := by
  have hh := sourceOpenDominationDefectOn_fst_restrict_apply_le π U ν δ h B
  rwa [fst_restrict_sourceProduct_eq_restrict_fst π U hU, Measure.restrict_apply' hU] at hh

/-- Vanishing localized defects yield AC of the SAME plan's source restriction,
using outer regularity of each varying reference, with no proper projection. -/
theorem absolutelyContinuous_fst_restrict_of_vanishing_sourceOpenDominationDefectsOn
    (π : Measure (X × Y)) (U : Set X) (m : Measure X) (ν : ℕ → Measure X)
    [∀ k, (ν k).OuterRegular]
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0))
    (hν : ∀ k, ν k ≪ m)
    (h : ∀ k, sourceOpenDominationDefectOn π U (ν k) (δ k)) :
    (π.restrict (U ×ˢ univ)).fst ≪ m :=
  absolutelyContinuous_fst_of_vanishing_sourceOpenDominationDefects
    (π.restrict (U ×ˢ univ)) m ν δ hδ hν
    (fun k ↦ (sourceOpenDominationDefectOn_iff_restrict π U (ν k) (δ k)).mp (h k))

/-- Fixed OPEN source localization preserves the closed simultaneous carrier:
all readouts are masses on the open edge sets (O ∩ U) × ALL targets. -/
theorem isClosed_sourceOpenDominationDefectOn
    (U : Set X) (hU : IsOpen U) (ν : Measure X) (δ : ℝ≥0∞) :
    IsClosed {π : LocalFiniteMeasure (X × Y) |
      sourceOpenDominationDefectOn (π : Measure (X × Y)) U ν δ} := by
  change IsClosed {π : LocalFiniteMeasure (X × Y) |
    ∀ O : Set X, ∀ _ : IsOpen O, (π : Measure (X × Y)) ((O ∩ U) ×ˢ univ) ≤ ν O + δ}
  simp only [ofPred_forall]
  exact isClosed_iInter fun O ↦ isClosed_iInter fun hO ↦
    (LocalFiniteMeasure.lowerSemicontinuous_measure_open
      ((hO.inter hU).prod isOpen_univ)).isClosed_preimage (ν O + δ)

/-- The SAME actual plan's localized all-open-source defect carrier survives
one weak limit; restriction of the vague plan is never required continuous. -/
theorem ae_sourceOpenDominationDefectOn_of_weak_tendsto
    (R : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (U : Set X) (hU : IsOpen U) (ν : Measure X) (δ : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn n : Measure S),
      sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U ν δ) :
    ∀ᵐ s ∂(R : Measure S), sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U ν δ := by
  let K : Set S := {s | sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U ν δ}
  have hK : IsClosed K := (isClosed_sourceOpenDominationDefectOn U hU ν δ).preimage hplan
  have hn : ∀ᶠ n in atTop, (Pn n : Measure S) Kᶜ = 0 := hbound
  have hlim : atTop.liminf (fun n ↦ (Pn n : Measure S) Kᶜ) = 0 :=
    (liminf_congr hn).trans (liminf_const 0)
  change (R : Measure S) Kᶜ = 0
  exact le_antisymm
    ((ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl).trans_eq hlim)
    bot_le

/-- The SAME fixed open source-localized carrier survives the prescribed sample
subsequence at each fixed tilt, then the prescribed outer tilt subsequence. -/
theorem ae_sourceOpenDominationDefectOn_of_iterated_weak
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (U : Set X) (hU : IsOpen U) (ν : Measure X) (δ : ℝ≥0∞)
    (hbound : ∀ ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn ℓ n : Measure S),
      sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U ν δ) :
    ∀ᵐ s ∂(R : Measure S), sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U ν δ := by
  have hQ (ℓ : ℕ) : ∀ᵐ s ∂(Q ℓ : Measure S),
      sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U ν δ :=
    ae_sourceOpenDominationDefectOn_of_weak_tendsto (Q ℓ) (fun n ↦ Pn ℓ (φ ℓ n))
      (hinner ℓ) plan hplan U hU ν δ ((hφ ℓ).eventually (hbound ℓ))
  exact ae_sourceOpenDominationDefectOn_of_weak_tendsto R (fun ℓ ↦ Q (ψ ℓ)) houter
    plan hplan U hU ν δ (Eventually.of_forall fun ℓ ↦ hQ (ψ ℓ))

/-- Localized AC follows on the SAME final law after sample, tilt and independent
reference accuracy, in that order. The source restriction is the original one. -/
theorem ae_absolutelyContinuous_fst_restrict_of_iterated_weak_sourceOpenDominationDefectsOn
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (U : Set X) (hU : IsOpen U) (m : Measure X)
    (ν : ℕ → Measure X) [∀ k, (ν k).OuterRegular]
    (δ : ℕ → ℝ≥0∞) (hδ : Tendsto δ atTop (𝓝 0)) (hν : ∀ k, ν k ≪ m)
    (hbound : ∀ k ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn ℓ n : Measure S),
      sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U (ν k) (δ k)) :
    ∀ᵐ s ∂(R : Measure S), ((plan s : Measure (X × Y)).restrict (U ×ˢ univ)).fst ≪ m := by
  have hall : ∀ᵐ s ∂(R : Measure S), ∀ k,
      sourceOpenDominationDefectOn (plan s : Measure (X × Y)) U (ν k) (δ k) := by
    apply ae_all_iff.mpr
    intro k
    exact ae_sourceOpenDominationDefectOn_of_iterated_weak Pn Q R φ hφ ψ hinner houter
      plan hplan U hU (ν k) (δ k) (hbound k)
  filter_upwards [hall] with s hs
  exact absolutelyContinuous_fst_restrict_of_vanishing_sourceOpenDominationDefectsOn
    (plan s : Measure (X × Y)) U m ν δ hδ hν hs

/-- AC of source restrictions on any countable measurable cover implies AC of
the full nonproper source marginal. No marginal local finiteness is assumed. -/
theorem absolutelyContinuous_fst_of_countable_source_restrictions
    (π : Measure (X × Y)) (m : Measure X) (U : ℕ → Set X)
    (hU : ∀ k, MeasurableSet (U k)) (hcover : ⋃ k, U k = univ)
    (hAC : ∀ k, (π.restrict (U k ×ˢ univ)).fst ≪ m) : π.fst ≪ m := by
  intro B hB
  have heq (k : ℕ) : π.fst.restrict (U k) = (π.restrict (U k ×ˢ univ)).fst :=
    (fst_restrict_sourceProduct_eq_restrict_fst π (U k) (hU k)).symm
  have hb (k : ℕ) : π.fst (B ∩ U k) = 0 := by
    have hz := hAC k hB
    rw [← heq k, Measure.restrict_apply' (hU k)] at hz
    exact hz
  rw [show B = ⋃ k, B ∩ U k by rw [← inter_iUnion, hcover, inter_univ]]
  exact measure_iUnion_null hb

/-- One common AE event for a countable source cover promotes localized actual
source AC to the full source marginal of the SAME original scene law. -/
theorem ae_absolutelyContinuous_fst_of_countable_source_restrictions
    (R : Measure S) (plan : S → LocalFiniteMeasure (X × Y))
    (m : Measure X) (U : ℕ → Set X)
    (hU : ∀ k, MeasurableSet (U k)) (hcover : ⋃ k, U k = univ)
    (hAC : ∀ k, ∀ᵐ s ∂R, ((plan s : Measure (X × Y)).restrict (U k ×ˢ univ)).fst ≪ m) :
    ∀ᵐ s ∂R, (plan s : Measure (X × Y)).fst ≪ m := by
  have hall : ∀ᵐ s ∂R, ∀ k,
      ((plan s : Measure (X × Y)).restrict (U k ×ˢ univ)).fst ≪ m := ae_all_iff.mpr hAC
  filter_upwards [hall] with s hs
  exact absolutelyContinuous_fst_of_countable_source_restrictions
    (plan s : Measure (X × Y)) m U hU hcover hs

/-- Fixed open source windows may each use their OWN outer-regular approximate
references and scalar accuracy defects. Every window addresses the SAME laws,
inner subsequences and final outer law, which then has full source AC almost surely. -/
theorem ae_absolutelyContinuous_fst_of_iterated_weak_localized_source_cover
    (Pn : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S)
    (φ : ℕ → ℕ → ℕ) (hφ : ∀ ℓ, Tendsto (φ ℓ) atTop atTop)
    (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ Pn ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (plan : S → LocalFiniteMeasure (X × Y)) (hplan : Continuous plan)
    (m : Measure X) (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k))
    (hcover : ⋃ k, U k = univ)
    (ν : ℕ → ℕ → Measure X) [∀ k q, (ν k q).OuterRegular]
    (δ : ℕ → ℕ → ℝ≥0∞) (hδ : ∀ k, Tendsto (δ k) atTop (𝓝 0))
    (hν : ∀ k q, ν k q ≪ m)
    (hbound : ∀ k q ℓ, ∀ᶠ n in atTop, ∀ᵐ s ∂(Pn ℓ n : Measure S),
      sourceOpenDominationDefectOn (plan s : Measure (X × Y)) (U k) (ν k q) (δ k q)) :
    ∀ᵐ s ∂(R : Measure S), (plan s : Measure (X × Y)).fst ≪ m := by
  apply ae_absolutelyContinuous_fst_of_countable_source_restrictions
    (R : Measure S) plan m U (fun k ↦ (hU k).measurableSet) hcover
  intro k
  exact ae_absolutelyContinuous_fst_restrict_of_iterated_weak_sourceOpenDominationDefectsOn
    Pn Q R φ hφ ψ hinner houter plan hplan (U k) (hU k) m (ν k) (δ k) (hδ k) (hν k)
    (hbound k)

end OTSelector.Reconstruction

end
end
