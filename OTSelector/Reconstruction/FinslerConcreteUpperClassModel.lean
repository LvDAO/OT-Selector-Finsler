import OTSelector.Reconstruction.FinslerConcreteUpperClassBins
import OTSelector.Reconstruction.FinslerConcreteUpperModel

/-!
Finite legal clock models use actual original representative pairs in each
allowed bin rectangle. Matrix positivity, homogeneous degree two, compact
quadratic bounds and the physical probe bound come from the same reference.
The produced bins give relative comparison for every raw clock in the bins.
-/

open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BoundedContinuousFunction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
  {width : ℝ} {range : Set ℝ} (Q : FiniteScalarBins range width)

/-- A class edge is allowed exactly when its bin rectangle contains an original
pair in the retained legal coefficient region. -/
def clockClassAllowed (i j : Fin Q.count) : Prop :=
  ∃ p ∈ C.window.region, p.1 ∈ Q.cell i ∧ p.2 ∈ Q.cell j

/-- A representative is chosen from the actual legal region on every allowed
class edge. Off-graph values do not enter legal matching. -/
def clockClassReference (i j : Fin Q.count) : ℝ × ℝ := by
  classical
  exact if h : C.clockClassAllowed Q i j then h.choose else (0, 0)

theorem clockClassReference_mem {i j : Fin Q.count} (h : C.clockClassAllowed Q i j) :
    C.clockClassReference Q i j ∈ C.window.region ∧
      (C.clockClassReference Q i j).1 ∈ Q.cell i ∧
      (C.clockClassReference Q i j).2 ∈ Q.cell j := by
  classical
  simpa only [clockClassReference, dite_eq_left h] using h.choose_spec

/-- The actual finite reference matrix, zero-extended off its explicit legal graph. -/
def clockClassMatrix (z₀ : Z) (i j : Fin Q.count) :
    Matrix (Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ := by
  classical
  exact if C.clockClassAllowed Q i j then C.matrix z₀ (C.clockClassReference Q i j) else 0

/-- The finite class quadratic kernel keeps the original transverse coordinates. -/
def clockClassKinetic (z₀ : Z) (i j : Fin Q.count)
    (v : Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) : ℝ :=
  matrixQuadratic (C.clockClassMatrix Q z₀ i j) v

/-- The finite class probe is the original physical reference probe. -/
def clockClassProbe (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ)
    (i j : Fin Q.count) : ℝ := by
  classical
  exact if C.clockClassAllowed Q i j then
    originalReferenceClockProbe C z₀ hz₀ f (C.clockClassReference Q i j) else 0

/-- The actual reference matrix is positive definite on every allowed class edge. -/
theorem clockClassMatrix_posDef (z₀ : Z) (hz₀ : z₀ ∈ C.roots)
    {i j : Fin Q.count} (h : C.clockClassAllowed Q i j) :
    (C.clockClassMatrix Q z₀ i j).PosDef := by
  classical
  rw [clockClassMatrix, ite_eq_left h]
  exact C.coefficient_posDef z₀ hz₀ _ (C.clockClassReference_mem Q h).1

/-- The global finite-class kinetic kernel is nonnegative. -/
theorem clockClassKinetic_nonneg (z₀ : Z) (hz₀ : z₀ ∈ C.roots)
    (i j : Fin Q.count) (v : Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) :
    0 ≤ C.clockClassKinetic Q z₀ i j v := by
  classical
  by_cases h : C.clockClassAllowed Q i j
  · by_cases hv : v = 0
    · simp [clockClassKinetic, hv]
    · exact (matrixQuadratic_pos (C.clockClassMatrix_posDef Q z₀ hz₀ h) hv).le
  · simp [clockClassKinetic, clockClassMatrix, h, matrixQuadratic]

/-- Every model class kernel is genuinely quadratic at all displacement scales. -/
theorem clockClassKinetic_homogeneous (z₀ : Z) (i j : Fin Q.count) (r : ℝ)
    (v : Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) :
    C.clockClassKinetic Q z₀ i j (r • v) = r ^ 2 * C.clockClassKinetic Q z₀ i j v :=
  matrixQuadratic_smul _ _ _

/-- Finite class labels and the original quadratic readout give joint measurability. -/
theorem measurable_clockClassKinetic (z₀ : Z) :
    Measurable (fun p : (Fin Q.count × Fin Q.count) ×
      (Fin (Module.finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) ↦
        C.clockClassKinetic Q z₀ p.1.1 p.1.2 p.2) := by
  exact continuous_matrixQuadratic.measurable.comp
    (((measurable_of_countable (fun ij : Fin Q.count × Fin Q.count ↦
      C.clockClassMatrix Q z₀ ij.1 ij.2)).comp measurable_fst).prodMk measurable_snd)

/-- A uniform quadratic constant is produced from the actual compact coefficient
field, independently of bin count and any empirical population size. -/
theorem exists_clockClassKinetic_bound (z₀ : Z) (hz₀ : z₀ ∈ C.roots) :
    ∃ K ≥ 0, ∀ i j v, |C.clockClassKinetic Q z₀ i j v| ≤ K * ∑ l, v l ^ 2 := by
  classical
  have hc : ContinuousOn (C.matrix z₀) C.window.region :=
    C.coefficient_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp ↦ ⟨hz₀, hp⟩)
  obtain ⟨K, hK, hbound⟩ := exists_compact_matrixQuadratic_sum_bound C.window.isCompact_region hc
  refine ⟨K, hK, fun i j v ↦ ?_⟩
  by_cases h : C.clockClassAllowed Q i j
  · simpa only [clockClassKinetic, clockClassMatrix, ite_eq_left h] using
      hbound _ (C.clockClassReference_mem Q h).1 v
  · simp only [clockClassKinetic, clockClassMatrix, ite_eq_right h, matrixQuadratic,
      Matrix.zero_mulVec, dotProduct_zero, mul_zero, abs_zero]
    exact mul_nonneg hK (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The same actual compact coefficient core supplies uniform ellipticity on
all allowed finite class edges. -/
theorem exists_clockClassKinetic_lower_bound (z₀ : Z) (hz₀ : z₀ ∈ C.roots) :
    ∃ m > 0, ∀ i j, C.clockClassAllowed Q i j → ∀ v,
      m * ‖v‖ ^ 2 ≤ C.clockClassKinetic Q z₀ i j v := by
  classical
  obtain ⟨m, hm, hlower⟩ := C.exists_quadratic_lower_bound
  refine ⟨m, hm, fun i j hij v ↦ ?_⟩
  simpa only [clockClassKinetic, clockClassMatrix, ite_eq_left hij] using
    hlower z₀ hz₀ _ (C.clockClassReference_mem Q hij).1 v

/-- The finite physical probe is measurable in both class coordinates. -/
theorem measurable_clockClassProbe (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ) :
    Measurable (fun ij : Fin Q.count × Fin Q.count ↦ C.clockClassProbe Q z₀ hz₀ f ij.1 ij.2) :=
  measurable_of_countable _

/-- The finite reference probe keeps the original bounded physical probe norm. -/
theorem clockClassProbe_abs_le (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (i j : Fin Q.count) : |C.clockClassProbe Q z₀ hz₀ f i j| ≤ ‖f‖ := by
  classical
  by_cases h : C.clockClassAllowed Q i j
  · simp only [clockClassProbe, ite_eq_left h, originalReferenceClockProbe]
    exact f.norm_coe_le_norm _
  · simp only [clockClassProbe, ite_eq_right h, abs_zero]
    exact norm_nonneg _

end OriginalPopulationCoefficientCore

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]

/-- The actual reference constructs a finite legal model whose entrywise errors
control every raw clock pair in its allowed class rectangles. -/
theorem OriginalPopulationCoefficientCore.exists_finite_legal_clockClass_model
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instClassModelMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ) (hf : Continuous f)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ width : ℝ, 0 < width ∧
      ∃ Q : FiniteScalarBins (Icc (C.window.val.1 : ℝ) C.window.val.2.1) width,
        ∀ i j, C.clockClassAllowed Q i j → ∀ x ∈ Q.cell i, ∀ y ∈ Q.cell j,
          (C.window.val.2.2 : ℝ) / 2 ≤ y - x ∧ x < y ∧
          (∀ v, |matrixQuadratic (C.matrix z₀ (x, y)) v - C.clockClassKinetic Q z₀ i j v| ≤
            ε * C.clockClassKinetic Q z₀ i j v) ∧
          |originalReferenceClockProbe C z₀ hz₀ f (x, y) -
            C.clockClassProbe Q z₀ hz₀ f i j| ≤ B := by
  classical
  obtain ⟨width, hwidth, Q, hcompare⟩ :=
    C.exists_legal_clock_resampling_bins hF hcomplete hu ha hinj z₀ hz₀ f hf hε hB
  refine ⟨width, hwidth, Q, fun i j hij x hx y hy ↦ ?_⟩
  have hp := C.clockClassReference_mem Q hij
  have h := hcompare i j _ hp.1 hp.2.1 hp.2.2 x hx y hy
  simpa only [clockClassKinetic, clockClassMatrix, clockClassProbe, ite_eq_left hij] using h


/-- The overflow class complements the entire original local scalar range. -/
def FiniteScalarBins.overflowCell {J : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins J width) (i : Option (Fin Q.count)) : Set ℝ :=
  match i with
  | none => Jᶜ
  | some j => Q.cell j

/-- Original local bins plus their overflow form an exact measurable partition
of all clock values, including empty bins. -/
theorem FiniteScalarBins.overflow_partition {J : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins J width) (hJ : MeasurableSet J) :
    (∀ i, MeasurableSet (Q.overflowCell i)) ∧
      Pairwise (fun i j ↦ Disjoint (Q.overflowCell i) (Q.overflowCell j)) ∧
      (⋃ i, Q.overflowCell i) = univ := by
  constructor
  · intro i
    cases i with
    | none => exact hJ.compl
    | some j => exact Q.measurable_cell j
  constructor
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        exact Set.disjoint_left.mpr (fun x hx hy ↦ hx (Q.subset j hy))
    | some i =>
      cases j with
      | none =>
        exact Set.disjoint_left.mpr (fun x hx hy ↦ hy (Q.subset i hx))
      | some j => exact Q.disjoint (fun heq ↦ hij (congrArg some heq))
  · apply Subset.antisymm (subset_univ _)
    intro x _
    by_cases hx : x ∈ J
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (Q.union_eq.symm ▸ hx)
      exact mem_iUnion.mpr ⟨some j, hj⟩
    · exact mem_iUnion.mpr ⟨none, hx⟩

/-- A full original compact scalar range admits arbitrarily fine finite bins
subordinate to local model bins plus overflow. The local interval need not carry
the full original conditional clock law. -/
theorem exists_finiteScalarBins_refining_with_overflow
    {I J : Set ℝ} (hI : IsCompact I) (hJ : MeasurableSet J)
    {localWidth : ℝ} (Q : FiniteScalarBins J localWidth)
    {gap : ℝ} (hgap : 0 < gap) :
    ∃ full : FiniteScalarBins I gap,
      ∃ localClass : Fin full.count → Option (Fin Q.count),
        ∀ j, full.cell j ⊆ Q.overflowCell (localClass j) := by
  classical
  obtain ⟨F⟩ := exists_finiteScalarBins hI hgap
  obtain ⟨hHm, hHdisj, hHcover⟩ := Q.overflow_partition hJ
  let Index := Fin F.count × Option (Fin Q.count)
  let e : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  let piece := fun k : Index ↦ F.cell k.1 ∩ Q.overflowCell k.2
  have hpm : ∀ k, MeasurableSet (piece k) := fun k ↦ (F.measurable_cell k.1).inter (hHm k.2)
  have hpdisj : Pairwise (fun k l ↦ Disjoint (piece k) (piece l)) := by
    intro k l hkl
    by_cases hfirst : k.1 = l.1
    · have hsecond : k.2 ≠ l.2 := fun h ↦ hkl (Prod.ext hfirst h)
      exact (hHdisj hsecond).mono inter_subset_right inter_subset_right
    · exact (F.disjoint hfirst).mono inter_subset_left inter_subset_left
  have hpcover : (⋃ k : Index, piece k) = I := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact F.subset k.1 hk.1
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp (F.union_eq.symm ▸ hx)
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hHcover.symm ▸ mem_univ x)
      exact mem_iUnion.mpr ⟨(j, k), hj, hk⟩
  let full : FiniteScalarBins I gap := {
    count := Fintype.card Index
    cell := fun j ↦ piece (e j)
    measurable_cell := fun j ↦ hpm (e j)
    subset := fun j x hx ↦ F.subset (e j).1 hx.1
    disjoint := fun j k hjk ↦ hpdisj (e.injective.ne hjk)
    union_eq := by rw [e.surjective.iUnion_comp, hpcover]
    diameter := fun j x hx y hy ↦ F.diameter (e j).1 x hx.1 y hy.1 }
  exact ⟨full, fun j ↦ (e j).2, fun j ↦ inter_subset_right⟩


/-- A full original compact clock range receives finite legal model classes.
Overflow classes remain available for the original residual population, while
every main rectangle retains the actual reference cost/probe comparison. -/
theorem OriginalPopulationCoefficientCore.exists_full_finite_legal_clockClass_model
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFullClassModelMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M → ℝ) (hf : Continuous f)
    {I : Set ℝ} (hI : IsCompact I) {globalGap : ℝ} (hglobalGap : 0 < globalGap)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ Q : FiniteScalarBins I globalGap,
      ∀ i j, C.clockClassAllowed Q i j → ∀ x ∈ Q.cell i, ∀ y ∈ Q.cell j,
        (C.window.val.2.2 : ℝ) / 2 ≤ y - x ∧ x < y ∧
        (∀ v, |matrixQuadratic (C.matrix z₀ (x, y)) v - C.clockClassKinetic Q z₀ i j v| ≤
          ε * C.clockClassKinetic Q z₀ i j v) ∧
        |originalReferenceClockProbe C z₀ hz₀ f (x, y) -
          C.clockClassProbe Q z₀ hz₀ f i j| ≤ B := by
  classical
  obtain ⟨width, hwidth, localBins, hlocal⟩ :=
    C.exists_legal_clock_resampling_bins hF hcomplete hu ha hinj z₀ hz₀ f hf hε hB
  obtain ⟨full, tag, htag⟩ :=
    exists_finiteScalarBins_refining_with_overflow hI measurableSet_Icc localBins hglobalGap
  refine ⟨full, fun i j hij x hx y hy ↦ ?_⟩
  have hp := C.clockClassReference_mem full hij
  let p₀ := C.clockClassReference full i j
  have hi : ∃ k, tag i = some k := by
    cases heq : tag i with
    | none =>
      have hn := htag i hp.2.1
      rw [heq] at hn
      exact False.elim (hn hp.1.1.1)
    | some k => exact ⟨k, rfl⟩
  have hj : ∃ k, tag j = some k := by
    cases heq : tag j with
    | none =>
      have hn := htag j hp.2.2
      rw [heq] at hn
      exact False.elim (hn hp.1.1.2)
    | some k => exact ⟨k, rfl⟩
  obtain ⟨ki, hki⟩ := hi
  obtain ⟨kj, hkj⟩ := hj
  have hisub : full.cell i ⊆ localBins.cell ki := by
    simpa only [hki, FiniteScalarBins.overflowCell] using htag i
  have hjsub : full.cell j ⊆ localBins.cell kj := by
    simpa only [hkj, FiniteScalarBins.overflowCell] using htag j
  have h := hlocal ki kj p₀ hp.1 (hisub hp.2.1) (hjsub hp.2.2) x (hisub hx) y (hjsub hy)
  simpa only [clockClassKinetic, clockClassMatrix, clockClassProbe, ite_eq_left hij] using h

end OTSelector.Reconstruction
