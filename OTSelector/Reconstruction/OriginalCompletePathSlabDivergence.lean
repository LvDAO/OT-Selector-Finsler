import OTSelector.Reconstruction.FinslerOriginalCompletePathEndpointIdentity

/-!
# Exact finite-edge weak balance with actual nonnegative cut occupations

An active cut contains only edges whose original clocks strictly straddle the cut.
Started sources and finished targets keep their original positions, including
endpoints outside a chosen spatial cube. Prefix/slab fluxes use the same complete
original path and its unchanged pair momentum throughout every clock interval.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

section FiniteAtoms
variable {I X : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSingletonClass X]

private theorem finite_indicator_dirac (active : I → Prop) [DecidablePred active]
    (point : I → X) : IsFiniteMeasure (∑ i, if active i then Measure.dirac (point i) else 0) := by
  classical
  let (i : I) : IsFiniteMeasure (if active i then Measure.dirac (point i) else 0) := by
    split_ifs <;> infer_instance
  infer_instance

private theorem integral_finite_indicator_dirac (active : I → Prop) [DecidablePred active]
    (point : I → X) (φ : X → ℝ) :
    (∫ x, φ x ∂(∑ i, if active i then Measure.dirac (point i) else 0)) =
      ∑ i, if active i then φ (point i) else 0 := by
  classical
  have hi (i : I) : Integrable φ (if active i then Measure.dirac (point i) else 0) := by
    split_ifs
    · exact integrable_dirac (by simp)
    · simp
  rw [integral_finsetSum_measure (fun i _ ↦ hi i)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end FiniteAtoms

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {I : Type*} [Fintype I]

/-- The actual positive cut measure contains only edges with sourceClock<t<targetClock.
It does not include unborn/finished edges at their clamped endpoints. -/
def originalCompletePathActiveCut (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (t : ℝ) :
    Measure (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  ∑ i, if (edges i).1.2 < t ∧ t < (edges i).2.2 then
    Measure.dirac (originalSeedCompletePath S w (edges i).1.1 (physicalPairAnchor (edges i)).2 t)
  else 0

/-- Every source that has started strictly before the cut is retained at its original position. -/
def originalCompletePathStartedSources {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (t : ℝ) : Measure (Fin q → ℝ) :=
  ∑ i, if (edges i).1.2 < t then Measure.dirac (edges i).1.1 else 0

/-- Every target reached by the cut is retained at its original position. -/
def originalCompletePathFinishedTargets {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (t : ℝ) : Measure (Fin q → ℝ) :=
  ∑ i, if (edges i).2.2 ≤ t then Measure.dirac (edges i).2.1 else 0

/-- The true source charge of the slab: s<=sourceClock<t, at unchanged source positions. -/
def originalCompletePathSlabSources {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (s t : ℝ) : Measure (Fin q → ℝ) :=
  ∑ i, if s ≤ (edges i).1.2 ∧ (edges i).1.2 < t then
    Measure.dirac (edges i).1.1 else 0

/-- The true target charge of the slab: s<targetClock<=t, at unchanged target positions. -/
def originalCompletePathSlabTargets {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (s t : ℝ) : Measure (Fin q → ℝ) :=
  ∑ i, if s < (edges i).2.2 ∧ (edges i).2.2 ≤ t then
    Measure.dirac (edges i).2.1 else 0

instance originalCompletePathSlabSourcesIsFinite {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (s t : ℝ) :
    IsFiniteMeasure (originalCompletePathSlabSources edges s t) := by
  unfold originalCompletePathSlabSources
  exact finite_indicator_dirac _ _

instance originalCompletePathSlabTargetsIsFinite {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (s t : ℝ) :
    IsFiniteMeasure (originalCompletePathSlabTargets edges s t) := by
  unfold originalCompletePathSlabTargets
  exact finite_indicator_dirac _ _

/-- Slab sources are the exact increase of the strictly-started source prefix. -/
theorem integral_originalCompletePathSlabSources {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) {s t : ℝ} (hst : s ≤ t)
    (φ : (Fin q → ℝ) → ℝ) :
    (∫ x, φ x ∂originalCompletePathSlabSources edges s t) =
      (∫ x, φ x ∂originalCompletePathStartedSources edges t) -
        ∫ x, φ x ∂originalCompletePathStartedSources edges s := by
  unfold originalCompletePathSlabSources originalCompletePathStartedSources
  rw [integral_finite_indicator_dirac,integral_finite_indicator_dirac,
    integral_finite_indicator_dirac,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases has : (edges i).1.2 < s
  · have hat := has.trans_le hst
    simp [has,hat,not_le.mpr has]
  · have hsa := le_of_not_gt has
    by_cases hat : (edges i).1.2 < t <;> simp [has,hsa,hat]

/-- Slab targets are the exact increase of the finished target prefix. -/
theorem integral_originalCompletePathSlabTargets {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) {s t : ℝ} (hst : s ≤ t)
    (φ : (Fin q → ℝ) → ℝ) :
    (∫ x, φ x ∂originalCompletePathSlabTargets edges s t) =
      (∫ x, φ x ∂originalCompletePathFinishedTargets edges t) -
        ∫ x, φ x ∂originalCompletePathFinishedTargets edges s := by
  unfold originalCompletePathSlabTargets originalCompletePathFinishedTargets
  rw [integral_finite_indicator_dirac,integral_finite_indicator_dirac,
    integral_finite_indicator_dirac,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hbs : (edges i).2.2 ≤ s
  · have hbt := hbs.trans hst
    simp [hbs,hbt,not_lt.mpr hbs]
  · have hsb := lt_of_not_ge hbs
    by_cases hbt : (edges i).2.2 ≤ t <;> simp [hbs,hsb,hbt]

instance originalCompletePathActiveCutIsFinite
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (t : ℝ) :
    IsFiniteMeasure (originalCompletePathActiveCut S w edges t) := by
  unfold originalCompletePathActiveCut
  exact finite_indicator_dirac _ _

instance originalCompletePathStartedSourcesIsFinite {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (t : ℝ) :
    IsFiniteMeasure (originalCompletePathStartedSources edges t) := by
  unfold originalCompletePathStartedSources
  exact finite_indicator_dirac _ _

instance originalCompletePathFinishedTargetsIsFinite {q : ℕ}
    (edges : I → LegalMarkedPhysicalEdge q) (t : ℝ) :
    IsFiniteMeasure (originalCompletePathFinishedTargets edges t) := by
  unfold originalCompletePathFinishedTargets
  exact finite_indicator_dirac _ _

/-- The finite prefix flux pairs the original derivative with the same path on
its true source-to-cut interval. Only the interval endpoints are clamped. -/
def originalCompletePathPrefixFlux (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∫ r in (edges i).1.2..max (edges i).1.2 (min t (edges i).2.2),
    fderiv ℝ φ (originalSeedCompletePath S w (edges i).1.1 (physicalPairAnchor (edges i)).2 r)
      (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor (edges i)).2)

/-- The slab flux keeps the full original pair momentum between its two cuts. -/
def originalCompletePathSlabFlux (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ) (s t : ℝ) : ℝ :=
  ∑ i, ∫ r in max (edges i).1.2 (min s (edges i).2.2)..
      max (edges i).1.2 (min t (edges i).2.2),
    fderiv ℝ φ (originalSeedCompletePath S w (edges i).1.1 (physicalPairAnchor (edges i)).2 r)
      (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ
        originalSeedPairMomentum S w (physicalPairAnchor (edges i)).2)

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- One original edge has the exact active-cut/finished-target/started-source
prefix balance, including t=sourceClock and t=targetClock. -/
theorem original_complete_path_prefix_active_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (edge : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : edge.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : edge.2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hab : edge.1.2 < edge.2.2)
    (t : ℝ) {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    (∫ r in edge.1.2..max edge.1.2 (min t edge.2.2),
      fderiv ℝ φ (originalSeedCompletePath S w edge.1.1 (physicalPairAnchor edge).2 r)
        (originalSeedKernel S w (r - (S.level : ℝ)) *ᵥ
          originalSeedPairMomentum S w (physicalPairAnchor edge).2)) =
    (if edge.1.2 < t ∧ t < edge.2.2 then
      φ (originalSeedCompletePath S w edge.1.1 (physicalPairAnchor edge).2 t) else 0) +
      (if edge.2.2 ≤ t then φ edge.2.1 else 0) -
        (if edge.1.2 < t then φ edge.1.1 else 0) := by
  have hftc := D.integral_originalSeedCompletePath_prefix_eq_endpoints hF hw
    edge.1.1 (physicalPairAnchor edge).2 ha hb hab t hφ
  have htarget : edge.1.1 + (physicalPairAnchor edge).2.2 = edge.2.1 := by
    change edge.1.1 + (edge.2.1-edge.1.1) = edge.2.1
    abel
  rw [htarget] at hftc
  simp only [physicalPairAnchor] at hftc ⊢
  rw [hftc]
  by_cases hta : t ≤ edge.1.2
  · have hat : ¬edge.1.2 < t := not_lt.mpr hta
    have hbt : ¬edge.2.2 ≤ t := by linarith
    simp [hta,hat,hbt]
  · have hat : edge.1.2 < t := lt_of_not_ge hta
    by_cases hbt : edge.2.2 ≤ t
    · simp [hta,hat,hbt,not_lt.mpr hbt]
    · simp [hta,hat,hbt,lt_of_not_ge hbt]

/-- Finite original edges obey the exact weak prefix balance against the
actual nonnegative cut occupation and their unchanged physical endpoints. -/
theorem original_complete_path_prefix_weak_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : ∀ i, (edges i).1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : ∀ i, (edges i).2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hab : ∀ i, (edges i).1.2 < (edges i).2.2)
    (t : ℝ) {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    originalCompletePathPrefixFlux S w edges φ t =
      (∫ x, φ x ∂originalCompletePathActiveCut S w edges t) +
        (∫ x, φ x ∂originalCompletePathFinishedTargets edges t) -
          ∫ x, φ x ∂originalCompletePathStartedSources edges t := by
  unfold originalCompletePathPrefixFlux originalCompletePathActiveCut
    originalCompletePathFinishedTargets originalCompletePathStartedSources
  rw [integral_finite_indicator_dirac,integral_finite_indicator_dirac,
    integral_finite_indicator_dirac]
  rw [←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact D.original_complete_path_prefix_active_balance hF hw (edges i)
    (ha i) (hb i) (hab i) t hφ

/-- Each slab is the difference of two genuine prefixes on the SAME path.
The pair momentum is fixed; it is never recomputed between the two cut clocks. -/
theorem original_complete_path_slab_eq_prefix_sub
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : ∀ i, (edges i).1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : ∀ i, (edges i).2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hab : ∀ i, (edges i).1.2 < (edges i).2.2)
    {s t : ℝ} (hst : s ≤ t) {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    originalCompletePathSlabFlux S w edges φ s t =
      originalCompletePathPrefixFlux S w edges φ t -
        originalCompletePathPrefixFlux S w edges φ s := by
  unfold originalCompletePathSlabFlux originalCompletePathPrefixFlux
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hpref (r : ℝ) := D.integral_originalSeedCompletePath_testDerivative_eq_sub hF hw
    (edges i).1.1 (physicalPairAnchor (edges i)).2 (ha i) (hb i)
    (c := (edges i).1.2) (d := max (edges i).1.2 (min r (edges i).2.2))
    le_rfl (le_max_left _ _) (max_le (hab i).le (min_le_right _ _)) hφ
  have hslab := D.integral_originalSeedCompletePath_slab_eq_endpoints hF hw
    (edges i).1.1 (physicalPairAnchor (edges i)).2 (ha i) (hb i) (hab i).le hst hφ
  simp only [physicalPairAnchor] at hpref hslab ⊢
  rw [hslab,hpref t,hpref s]
  ring

/-- The exact slab endpoint balance uses two actual nonnegative active cuts
and the original started-source/finished-target prefixes. -/
theorem original_complete_path_slab_weak_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : ∀ i, (edges i).1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : ∀ i, (edges i).2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hab : ∀ i, (edges i).1.2 < (edges i).2.2)
    {s t : ℝ} (hst : s ≤ t) {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    originalCompletePathSlabFlux S w edges φ s t =
      ((∫ x, φ x ∂originalCompletePathActiveCut S w edges t) -
        ∫ x, φ x ∂originalCompletePathActiveCut S w edges s) +
      ((∫ x, φ x ∂originalCompletePathFinishedTargets edges t) -
        ∫ x, φ x ∂originalCompletePathFinishedTargets edges s) -
      ((∫ x, φ x ∂originalCompletePathStartedSources edges t) -
        ∫ x, φ x ∂originalCompletePathStartedSources edges s) := by
  rw [D.original_complete_path_slab_eq_prefix_sub hF hw edges ha hb hab hst hφ,
    D.original_complete_path_prefix_weak_balance hF hw edges ha hb hab t hφ,
    D.original_complete_path_prefix_weak_balance hF hw edges ha hb hab s hφ]
  ring

/-- With the distributional divergence sign, the slab current has precisely
the true original source/target slab charges plus its incoming/outgoing cuts.
No spatial endpoint restriction or divergence conclusion is an assumption. -/
theorem original_complete_path_slab_divergence_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (edges : I → LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
    (ha : ∀ i, (edges i).1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : ∀ i, (edges i).2.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hab : ∀ i, (edges i).1.2 < (edges i).2.2)
    {s t : ℝ} (hst : s ≤ t) {φ : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) :
    -originalCompletePathSlabFlux S w edges φ s t =
      (∫ x, φ x ∂originalCompletePathSlabSources edges s t) -
      (∫ x, φ x ∂originalCompletePathSlabTargets edges s t) +
      (∫ x, φ x ∂originalCompletePathActiveCut S w edges s) -
        ∫ x, φ x ∂originalCompletePathActiveCut S w edges t := by
  rw [D.original_complete_path_slab_weak_balance hF hw edges ha hb hab hst hφ,
    integral_originalCompletePathSlabSources edges hst φ,
    integral_originalCompletePathSlabTargets edges hst φ]
  ring

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
