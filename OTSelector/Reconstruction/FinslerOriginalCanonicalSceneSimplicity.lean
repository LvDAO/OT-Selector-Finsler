import OTSelector.Reconstruction.FinslerOriginalCubeSingletonNullity
import OTSelector.Reconstruction.FinslerOriginalHaarPositionAESimplicity

/-!
# A.e. canonical scene plan simplicity

This module closes the index bookkeeping of the canonical-scene simplicity gap.
The cloud-level a.e. distinctness is proved unconditionally in
FinslerOriginalCubeSingletonNullity; here it is pushed to the matched index set.

1. **canonicalPlanEdges_row_inj / canonicalPlanEdges_col_inj**: the matched index
   pairs of firstLegalMarkedOptimalMatching form a partial matching, so distinct
   edges have distinct source rows and distinct target columns.
2. **canonicalScenePlanSimplicity_of_marks**: pointwise, if the source marked
   cloud points at distinct indices are different and the same holds on the
   target side, and the spatial scale L is nonzero, then the canonical plan's
   matched physical source points (and target points) are pairwise distinct,
   i.e. CanonicalScenePlanSimplicity holds.  The physical source point is
   (L * source position, source mark); equality of two such points gives equality
   of the marked points (divide the position by L and compare marks), and the
   marked points at distinct indices are different.
3. **twoMarkedCloudLaw_ae_all_source_marks_ne / ..._target_...**: the a.e.
   pairwise distinctness of marked cloud points, upgraded from fixed pairs to the
   countable all-pairs statement (countable intersection).
4. **ae_canonicalScenePlanSimplicity**: CanonicalScenePlanSimplicity holds a.e.
   under twoMarkedCloudLaw q R R alpha beta rho, for q >= 1 and L != 0, with NO
   remaining probabilistic hypothesis.

## Exact remaining inputs for CanonicalSceneFullMatching

Given a.e. plan simplicity (this file), the remaining fields of the canonical
scene full matching are:

* hs - IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
  (canonicalInputMeasure ...): the canonical input measure is the atom sum over
  the matched pairs of the source atoms (colour 0) and target atoms (colour 1).
  Cross-colour atoms never collide (different colour coordinate), and same-colour
  atoms are pairwise distinct by (4), so simplicity reduces to the multiplicity
  bookkeeping of the LocalConfiguration representing that finite atom sum
  (exists_configuration_finset_dirac exists for LegalColoredInputPoint q; the
  pointwise multiplicity <= 1 step is not wired here).
* hm - the two colour marginal identities
  (canonicalScene ...).1.1.fst = legalInputColorMeasure q (.2) 0 and the same
  for colour 1: pure measure algebra (both sides are explicit atom sums over the
  same matched pairs), not wired here because it needs the atom-sum/marginal
  manipulation for legalInputColorMeasure.

hc is unconditional (canonicalPlanConfig_spec).  No atomlessness or simplicity
probabilistic hypothesis remains.
No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.Probability OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

local instance canonicalSceneSimplicityColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {q : ℕ} {L r : ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {t : ℝ}

/-- **Rows of the canonical plan are injective**: distinct matched index pairs of
the optimal matching have distinct source indices. -/
theorem canonicalPlanEdges_row_inj (m n : ℕ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ∀ e ∈ canonicalPlanEdges q m n L r kin g t ω,
      ∀ e' ∈ canonicalPlanEdges q m n L r kin g t ω, e.1 = e'.1 → e = e' :=
  (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).row_inj

/-- **Columns of the canonical plan are injective**: distinct matched index pairs
of the optimal matching have distinct target indices. -/
theorem canonicalPlanEdges_col_inj (m n : ℕ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    ∀ e ∈ canonicalPlanEdges q m n L r kin g t ω,
      ∀ e' ∈ canonicalPlanEdges q m n L r kin g t ω, e.2 = e'.2 → e = e' :=
  (firstLegalMarkedOptimalMatching q m n id id r kin g t ω).col_inj

/-- **Pointwise canonical plan simplicity** from a.e.-style marked distinctness of
the source and target cloud points and nontrivial spatial scale. -/
theorem canonicalScenePlanSimplicity_of_marks (hL : L ≠ 0)
    (ω : TwoMarkedCloudSpace q ℝ ℝ)
    (hsrc : ∀ i j : ℕ, i ≠ j → ω.1.2 i ≠ ω.1.2 j)
    (htgt : ∀ i j : ℕ, i ≠ j → ω.2.2 i ≠ ω.2.2 j) :
    CanonicalScenePlanSimplicity q L r kin g t ω := by
  constructor
  · rintro ⟨e, he⟩ ⟨e', he'⟩ hphys
    have hpos : mSourcePoint ω (e.1 : ℕ) = mSourcePoint ω (e'.1 : ℕ) := by
      funext l
      have hfun : (fun l => L * mSourcePoint ω (e.1 : ℕ) l) =
          (fun l => L * mSourcePoint ω (e'.1 : ℕ) l) := congrArg Prod.fst hphys
      have hpt : L * mSourcePoint ω (e.1 : ℕ) l = L * mSourcePoint ω (e'.1 : ℕ) l :=
        congrFun hfun l
      exact mul_left_cancel₀ hL hpt
    have hmark : mSourceMark ω (e.1 : ℕ) = mSourceMark ω (e'.1 : ℕ) := by
      have := congrArg Prod.snd hphys
      simpa [canonicalPlanPoints, legalMarkedPhysicalEdge] using this
    have hidx : e.1 = e'.1 := by
      by_contra hne
      exact hsrc (e.1 : ℕ) (e'.1 : ℕ) (fun h => hne (Fin.ext h))
        (by simpa [mSourcePoint, mSourceMark] using Prod.ext hpos hmark)
    exact Subtype.ext (canonicalPlanEdges_row_inj (mSourceCount ω) (mTargetCount ω) ω
      e he e' he' hidx)
  · rintro ⟨e, he⟩ ⟨e', he'⟩ hphys
    have hpos : mTargetPoint ω (e.2 : ℕ) = mTargetPoint ω (e'.2 : ℕ) := by
      funext l
      have hfun : (fun l => L * mTargetPoint ω (e.2 : ℕ) l) =
          (fun l => L * mTargetPoint ω (e'.2 : ℕ) l) := congrArg Prod.fst hphys
      have hpt : L * mTargetPoint ω (e.2 : ℕ) l = L * mTargetPoint ω (e'.2 : ℕ) l :=
        congrFun hfun l
      exact mul_left_cancel₀ hL hpt
    have hmark : mTargetMark ω (e.2 : ℕ) = mTargetMark ω (e'.2 : ℕ) := by
      have := congrArg Prod.snd hphys
      simpa [canonicalPlanPoints, legalMarkedPhysicalEdge] using this
    have hidx : e.2 = e'.2 := by
      by_contra hne
      exact htgt (e.2 : ℕ) (e'.2 : ℕ) (fun h => hne (Fin.ext h))
        (by simpa [mTargetPoint, mTargetMark] using Prod.ext hpos hmark)
    exact Subtype.ext (canonicalPlanEdges_col_inj (mSourceCount ω) (mTargetCount ω) ω
      e he e' he' hidx)

/-- **A.e. all-pairs distinctness of source marked cloud points.** -/
theorem twoMarkedCloudLaw_ae_all_source_marks_ne (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∀ i j : ℕ, i ≠ j → ω.1.2 i ≠ ω.1.2 j := by
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_all_iff]
  intro j
  by_cases hij : i = j
  · subst hij
    simp
  · filter_upwards [twoMarkedCloudLaw_ae_source_marks_ne (q := q) hq α β ρ hij] with ω hω
    exact fun _ => hω

/-- **A.e. all-pairs distinctness of target marked cloud points.** -/
theorem twoMarkedCloudLaw_ae_all_target_marks_ne (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      ∀ i j : ℕ, i ≠ j → ω.2.2 i ≠ ω.2.2 j := by
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_all_iff]
  intro j
  by_cases hij : i = j
  · subst hij
    simp
  · filter_upwards [twoMarkedCloudLaw_ae_target_marks_ne (q := q) hq α β ρ hij] with ω hω
    exact fun _ => hω

/-- **A.e. canonical scene plan simplicity** under the two-cloud law, for q >= 1
and nonzero spatial scale.  This is the complete probabilistic content of
CanonicalScenePlanSimplicity; no further a.e. hypothesis remains. -/
theorem ae_canonicalScenePlanSimplicity (hq : 0 < q) (hL : L ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (ρ : ℝ≥0) :
    ∀ᵐ ω ∂twoMarkedCloudLaw q ℝ ℝ α β ρ,
      CanonicalScenePlanSimplicity q L r kin g t ω := by
  filter_upwards [twoMarkedCloudLaw_ae_all_source_marks_ne (q := q) hq α β ρ,
    twoMarkedCloudLaw_ae_all_target_marks_ne (q := q) hq α β ρ] with ω hsrc htgt
  exact canonicalScenePlanSimplicity_of_marks hL ω hsrc htgt

end OTSelector.Reconstruction
