import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCountingMatching
import OTSelector.Reconstruction.FinslerOriginalWindowCardinalityIdentification

/-!
# Measure-theoretic count identification of the full matching

This module records the a.e. inputs of the full-matching count identification
needed by FinslerOriginalWindowCardinalityIdentification.

For the concrete candidate structure the library already supplies the two
almost-sure fields:
- LegalWeightedStationaryPoissonMatching.forward: every support edge of the
  scene is forward (e.1.2 < e.2.2), hence belongs to the concrete forward-edge
  legal graph;
- LegalWeightedStationaryPoissonMatching.full_matching: the scene is a full
  original input matching (every source and target atom is matched).

We restate them as a.e. properties, record their conjunction, and prove the
a.e. missing-cardinality vanishing criterion: when the color counts are equal
a.e. and the legal maximum cardinality equals the smaller count a.e., the
integer missing-cardinality defects of FinslerOriginalWindowCardinality
Identification vanish almost surely.  This is the a.e. form of the full
saturation hypothesis that feeds the two-defect squeeze of
FinslerOriginalCandidateWindowLowerBound.

## Exact remaining sub-gap

The remaining step is the conversion of the scene counting measure support
cardinality into the cloud color counts mSourceCount/mTargetCount: the library
has no count-cardinality API for LocalFiniteMeasure support, so the integer
identification of the support edge count with the color counts (and hence the
a.e. equality of the legal maximum cardinality with the smaller count) is not
yet derived from IsFullOriginalInputMatching.  All the a.e. inputs (forward
legality and full matching) and the missing-cardinality vanishing criterion are
proved here.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **A.e. forward legality of the candidate scene edges.**  Almost every scene
of a genuine weighted stationary matching has all its support edges forward, so
the actual matching's edges lie in the concrete forward-edge legal graph. -/
theorem candidate_ae_forward_support_edges
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 :=
  M.forward

/-- **A.e. full original matching of the candidate scene.**  Almost every scene
of a genuine weighted stationary matching is a full original input matching. -/
theorem candidate_ae_full_original_matching
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s :=
  M.full_matching

/-- **A.e. forward legality together with the full matching.**  The two
structural a.e. properties of the candidate scene hold simultaneously. -/
theorem candidate_ae_full_and_forward
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s ∧
        ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 :=
  M.full_matching.and M.forward

/-- **A.e. missing-cardinality vanishing criterion.**  If the source and target
counts agree a.e. and the legal maximum cardinality equals the smaller count
a.e. (full saturation), then the integer missing-cardinality defects vanish
almost surely.  This is the a.e. form consumed by the two-defect squeeze. -/
theorem ae_missingCardinality_eq_zero_of_ae_fullSaturation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m n allowedCard : Ω → ℕ)
    (hmn : ∀ᵐ ω ∂P, m ω = n ω)
    (hfull : ∀ᵐ ω ∂P, allowedCard ω = min (m ω) (n ω)) :
    ∀ᵐ ω ∂P,
      ((n ω - allowedCard ω : ℕ) : ℝ) = 0 ∧ ((m ω - allowedCard ω : ℕ) : ℝ) = 0 := by
  filter_upwards [hmn, hfull] with ω hmnω hfullω
  have hmin : min (m ω) (n ω) = n ω := by
    rw [hmnω, min_self]
  constructor
  · rw [hfullω, hmin]
    norm_num
  · rw [hfullω, hmin, hmnω]
    norm_num

/-- **Zero lower defect a.e.**  Under the a.e. full saturation criterion the
missing-cardinality defect multiplied by a finite edge bound is zero almost
surely, which is the lower defect of the candidate window squeeze. -/
theorem ae_windowLowerDefect_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m n allowedCard : Ω → ℕ) (B : ℝ)
    (hmn : ∀ᵐ ω ∂P, m ω = n ω)
    (hfull : ∀ᵐ ω ∂P, allowedCard ω = min (m ω) (n ω)) :
    ∀ᵐ ω ∂P, (((n ω - allowedCard ω : ℕ) : ℝ) * B) = 0 := by
  filter_upwards [ae_missingCardinality_eq_zero_of_ae_fullSaturation P m n allowedCard hmn hfull]
    with ω hω
  rw [hω.1]
  simp

end OTSelector.Reconstruction
