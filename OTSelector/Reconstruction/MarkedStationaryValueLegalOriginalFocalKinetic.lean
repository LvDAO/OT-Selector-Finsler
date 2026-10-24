import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalClockCollars
import OTSelector.Reconstruction.OriginalSeedCoefficientBound
import OTSelector.Reconstruction.FinslerConcreteUpperModel

/-!
# The bounded actual original focal kinetic kernel

The literal inverse-compliance coefficient is used at all original interior
forward pairs with the original support separation. Its measurable definition
is zero elsewhere. Original short-compliance comparison gives a global upper
quadratic bound even when the true coefficient degenerates at support endpoints;
no continuity of this extension outside the actual domain is asserted.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual common interior clock span with its original physical gap. -/
def originalFocalClockRegion (gap : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
    p.2 - S.level ∈ Ioo D.lo D.hi ∧ gap ≤ p.2 - p.1}

/-- A measurable matrix carrier for the original coefficient; the legal graph
itself remains the strict original clock relation. -/
def originalFocalMatrix (gap : ℝ) (p : ℝ × ℝ) :
    Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ :=
  if p ∈ D.originalFocalClockRegion gap then originalSeedPairCoefficient S w p else 0

/-- Actual original inverse-compliance cost on retained clock pairs. -/
def originalFocalKinetic (gap a b : ℝ) (v : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  matrixQuadratic (D.originalFocalMatrix gap (a, b)) v

theorem measurableSet_originalFocalClockRegion (gap : ℝ) :
    MeasurableSet (D.originalFocalClockRegion gap) :=
  (measurableSet_Ioo.preimage (measurable_fst.sub_const (S.level : ℝ))).inter
    ((measurableSet_Ioo.preimage (measurable_snd.sub_const (S.level : ℝ))).inter
      (measurableSet_le measurable_const (measurable_snd.sub measurable_fst)))

theorem measurable_originalFocalMatrix (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (gap : ℝ) : Measurable (D.originalFocalMatrix gap) := by
  classical
  exact (measurable_originalSeedPairCoefficient S hF hw).ite
    (D.measurableSet_originalFocalClockRegion gap) measurable_const

theorem measurable_originalFocalKinetic (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (gap : ℝ) : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ D.originalFocalKinetic gap p.1 p.2)) :=
  continuous_matrixQuadratic.measurable.comp
    (((D.measurable_originalFocalMatrix hF hw gap).comp measurable_fst).prodMk measurable_snd)

theorem originalFocalKinetic_nonneg (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) (a b : ℝ) (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
    0 ≤ D.originalFocalKinetic gap a b v := by
  classical
  by_cases hp : (a, b) ∈ D.originalFocalClockRegion gap
  · have hab : a < b := by have := hp.2.2; dsimp at this; linarith
    have hpd := (D.pair_compliance_posDef hF hw hp.1 hp.2.1 hab).2
    change 0 ≤ matrixQuadratic (if (a, b) ∈ D.originalFocalClockRegion gap then _ else _) v
    rw [ite_eq_left hp]
    by_cases hv : v = 0
    · simp [hv]
    · exact (matrixQuadratic_pos hpd hv).le
  · simp [originalFocalKinetic, originalFocalMatrix, hp, matrixQuadratic]

theorem originalFocalKinetic_homogeneous (gap a b c : ℝ)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
    D.originalFocalKinetic gap a b (fun i ↦ c * v i) = c ^ 2 * D.originalFocalKinetic gap a b v := by
  have hv : (fun i ↦ c * v i) = c • v := by ext i; rfl
  unfold originalFocalKinetic
  rw [hv]
  exact matrixQuadratic_smul _ c v

/-- Original positive separation bounds the true coefficient from above on
all interior legal pairs, including pairs approaching focal endpoints. -/
theorem exists_originalFocalKinetic_quadratic_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ C ≥ 0, ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      |D.originalFocalKinetic gap a b v| ≤ C * ∑ i, v i ^ 2 := by
  classical
  have hK := D.original_kernel_regular hF hw
  obtain ⟨R, _, hbound⟩ := exists_uniform_inverse_compliance_bound hgap
    (hbounds.span_length_bounds D.support).1 hK.1 hK.2
  obtain ⟨C, hC, hquad⟩ := exists_compact_matrixQuadratic_sum_bound
    (ι := Fin (finrank ℝ S.covector.ker)) (K := Metric.closedBall 0 R)
    (isCompact_closedBall 0 R) continuous_id.continuousOn
  refine ⟨C, hC, fun a b v ↦ ?_⟩
  by_cases hp : (a, b) ∈ D.originalFocalClockRegion gap
  · change |matrixQuadratic (if (a, b) ∈ D.originalFocalClockRegion gap then _ else _) v| ≤ _
    rw [ite_eq_left hp]
    apply hquad (originalSeedPairCoefficient S w (a, b))
    simpa only [Metric.mem_closedBall, dist_zero_right, originalSeedPairCoefficient] using
      hbound (a - S.level) hp.1 (b - S.level) hp.2.1 (by simpa using hp.2.2)
  · simp only [originalFocalKinetic, originalFocalMatrix, ite_eq_right hp, matrixQuadratic,
      Matrix.zero_mulVec, dotProduct_zero, mul_zero, abs_zero]
    exact mul_nonneg hC (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

/-- Every actual original legal support pair inside the common open span is
charged its literal original coefficient. Absolute support separation supplies
the gap used in the measurable carrier; no ordering of all supports is added. -/
theorem originalFocalKinetic_eq_of_original_support
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {a b : ℝ} (ha : a - S.level ∈ Ioo D.lo D.hi ∧ a ∈ μ.support)
    (hb : b - S.level ∈ Ioo D.lo D.hi ∧ b ∈ ν.support) (hab : a < b)
    (v : Fin (finrank ℝ S.covector.ker) → ℝ) :
    D.originalFocalKinetic gap a b v = matrixQuadratic (originalSeedPairCoefficient S w (a, b)) v := by
  have hsep := hbounds.separated a ha.2 b hb.2
  have hgap : gap ≤ b - a := by
    simpa only [Real.dist_eq, abs_of_neg (sub_neg.mpr hab), neg_sub] using hsep
  simp only [originalFocalKinetic, originalFocalMatrix, ite_eq_left (show (a, b) ∈
    D.originalFocalClockRegion gap from ⟨ha.1, hb.1, hgap⟩)]

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
