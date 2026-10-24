import OTSelector.Reconstruction.FinslerCellModelData
import OTSelector.Probability.MarkedRelativeLawMatching

/-!
# Concrete frozen kernels on the original Taylor cells

The clocks are the original conditional laws at the actual reference root.
The matrix is the original coefficient in the seed basis, and the weight is
the unchanged population cell mass.  All marked-kernel bounds are produced
from compact continuity of that matrix.

The legal clock region is retained explicitly.  It is the compact triangle
with a positive clock gap, so it cannot be replaced by a product of marginal
clock supports.  The zero extension used to define a global kernel below has
an unrestricted marked pressure limit.  No theorem here identifies its
optimizers with legal optimizers of the physical problem.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators NNReal

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

/-- The fixed coordinate norm is dominated by the squared-coordinate sum. -/
theorem pi_norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  classical
  have hsum : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hn : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply (Real.le_sqrt (abs_nonneg _) hsum).mpr
    rw [sq_abs]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i)
  nlinarith [Real.sq_sqrt hsum, norm_nonneg v, Real.sqrt_nonneg (∑ i, v i ^ 2)]

/-- A compact continuous matrix field has a uniform quadratic bound in the
squared-coordinate sum.  This bound is produced from the actual field. -/
theorem exists_compact_matrixQuadratic_sum_bound
    {ι Θ : Type*} [Fintype ι] [TopologicalSpace Θ]
    {K : Set Θ} (hK : IsCompact K) {A : Θ → Matrix ι ι ℝ}
    (hA : ContinuousOn A K) :
    ∃ C ≥ 0, ∀ p ∈ K, ∀ v : ι → ℝ,
      |matrixQuadratic (A p) v| ≤ C * ∑ i, v i ^ 2 := by
  have hcompact := hK.prod (isCompact_sphere (0 : ι → ℝ) 1)
  have hc := continuousOn_matrixQuadratic_field hA (Metric.sphere (0 : ι → ℝ) 1)
  obtain ⟨H, hH⟩ := (hcompact.image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨max H 0, le_max_right _ _, fun p hp v ↦ ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let y : ι → ℝ := ‖v‖⁻¹ • v
  have hy : y ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [y, norm_smul, hn.ne']
  have hscale : ‖v‖ • y = v := by simp [y, smul_smul, hn.ne']
  have hunit : |matrixQuadratic (A p) y| ≤ max H 0 := by
    have h := hH _ (mem_image_of_mem _ (show (p, y) ∈ K ×ˢ Metric.sphere 0 1 from ⟨hp, hy⟩))
    have h' : |matrixQuadratic (A p) y| ≤ H := by
      simpa only [Real.norm_eq_abs] using h
    exact h'.trans (le_max_left _ _)
  calc |matrixQuadratic (A p) v|
      = |matrixQuadratic (A p) (‖v‖ • y)| := by rw [hscale]
    _ = ‖v‖ ^ 2 * |matrixQuadratic (A p) y| := by
      rw [matrixQuadratic_smul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖v‖ ^ 2 * max H 0 := mul_le_mul_of_nonneg_left hunit (sq_nonneg _)
    _ ≤ (∑ i, v i ^ 2) * max H 0 :=
      mul_le_mul_of_nonneg_right (pi_norm_sq_le_sum_sq v) (le_max_right _ _)
    _ = max H 0 * ∑ i, v i ^ 2 := mul_comm _ _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}

namespace PopulationLocalPressureCore.TaylorTiles

variable {ε : ℝ} (T : D.TaylorTiles ε)

/-- The retained reference is an original root of its actual coefficient core. -/
theorem reference_mem_core (k : T.Index) : T.reference k ∈ (T.core k).roots :=
  (T.cover k.1).subset ((T.partition k.1).center_mem k.2)

/-- The legal pair region of this tile. -/
def tileAllowed (k : T.Index) : Set (ℝ × ℝ) := (T.core k).window.region

theorem measurableSet_tileAllowed (k : T.Index) : MeasurableSet (T.tileAllowed k) :=
  (T.core k).window.isCompact_region.measurableSet

/-- Membership forces a strictly forward clock pair. -/
theorem tileAllowed_forward (k : T.Index) {s t : ℝ} (h : (s, t) ∈ T.tileAllowed k) :
    s < t := ((T.core k).window.region_subset h).2.2

/-- The original conditional clock law at the actual frozen root. -/
def tileClockLaw (k : T.Index) (color : Fin 2) : Measure ℝ :=
  populationTwoColorClockKernel u a η₀ η₁ color (T.reference k)

instance tileClockLaw_isProbabilityMeasure (k : T.Index) (color : Fin 2) :
    IsProbabilityMeasure (T.tileClockLaw k color) := by
  unfold tileClockLaw
  infer_instance

/-- The actual coefficient, extended by zero outside the retained legal region. -/
def tileFrozenMatrix (k : T.Index) (p : ℝ × ℝ) :
    Matrix (Fin (T.tileDim k)) (Fin (T.tileDim k)) ℝ := by
  classical
  exact if p ∈ T.tileAllowed k then (T.core k).matrix (T.reference k) p else 0

theorem tileFrozenMatrix_eq (k : T.Index) {p : ℝ × ℝ} (hp : p ∈ T.tileAllowed k) :
    T.tileFrozenMatrix k p = (T.core k).matrix (T.reference k) p := by
  classical
  simp only [tileFrozenMatrix, if_pos hp]

theorem measurable_tileFrozenMatrix (k : T.Index) : Measurable (T.tileFrozenMatrix k) := by
  classical
  have hc : ContinuousOn ((T.core k).matrix (T.reference k)) (T.tileAllowed k) :=
    (T.core k).coefficient_continuous.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp ↦ ⟨T.reference_mem_core k, hp⟩)
  exact hc.measurable_piecewise continuousOn_const (T.measurableSet_tileAllowed k)

theorem tileFrozenMatrix_quadratic_nonneg (k : T.Index) (p : ℝ × ℝ)
    (v : Fin (T.tileDim k) → ℝ) : 0 ≤ matrixQuadratic (T.tileFrozenMatrix k p) v := by
  classical
  by_cases hp : p ∈ T.tileAllowed k
  · rw [T.tileFrozenMatrix_eq k hp]
    by_cases hv : v = 0
    · simp [hv]
    · exact (matrixQuadratic_pos
        ((T.core k).coefficient_posDef (T.reference k) (T.reference_mem_core k) p hp) hv).le
  · simp [tileFrozenMatrix, hp, matrixQuadratic]

theorem exists_tileFrozenMatrix_bound (k : T.Index) :
    ∃ C ≥ 0, ∀ p v, |matrixQuadratic (T.tileFrozenMatrix k p) v| ≤
      C * ∑ l, v l ^ 2 := by
  classical
  have hc : ContinuousOn ((T.core k).matrix (T.reference k)) (T.tileAllowed k) :=
    (T.core k).coefficient_continuous.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp ↦ ⟨T.reference_mem_core k, hp⟩)
  obtain ⟨C, hC, hbound⟩ := exists_compact_matrixQuadratic_sum_bound
    (T.core k).window.isCompact_region hc
  refine ⟨C, hC, fun p v ↦ ?_⟩
  by_cases hp : p ∈ T.tileAllowed k
  · rw [T.tileFrozenMatrix_eq k hp]
    exact hbound p hp v
  · simp only [tileFrozenMatrix, if_neg hp, matrixQuadratic, Matrix.zero_mulVec,
      dotProduct_zero, mul_zero, abs_zero]
    exact mul_nonneg hC (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

variable [IsProbabilityMeasure lambda]

/-- The physical tile mass supplies exactly the inverse-density scaling. -/
def tileScaledKinetic (k : T.Index) (s t : ℝ) (v : Fin (T.tileDim k) → ℝ) : ℝ :=
  (T.tileWeight k : ℝ) ^ (-(2 / (T.tileDim k : ℝ))) *
    matrixQuadratic (T.tileFrozenMatrix k (s, t)) v

theorem measurable_tileScaledKinetic (k : T.Index) :
    Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ T.tileScaledKinetic k p.1 p.2)) := by
  exact measurable_const.mul (continuous_matrixQuadratic.measurable.comp
    (((T.measurable_tileFrozenMatrix k).comp measurable_fst).prodMk measurable_snd))

theorem tileScaledKinetic_nonneg (k : T.Index) (s t : ℝ) (v : Fin (T.tileDim k) → ℝ) :
    0 ≤ T.tileScaledKinetic k s t v :=
  mul_nonneg (Real.rpow_nonneg (T.tileWeight_nonneg k) _)
    (T.tileFrozenMatrix_quadratic_nonneg k (s, t) v)

theorem tileScaledKinetic_homogeneous (k : T.Index) (s t c : ℝ)
    (v : Fin (T.tileDim k) → ℝ) :
    T.tileScaledKinetic k s t (fun l ↦ c * v l) = c ^ 2 * T.tileScaledKinetic k s t v := by
  dsimp only [tileScaledKinetic]
  change _ * matrixQuadratic _ (c • v) = _
  rw [matrixQuadratic_smul]
  ring

theorem exists_tileScaledKinetic_bound (k : T.Index) :
    ∃ C ≥ 0, ∀ s t v, |T.tileScaledKinetic k s t v| ≤ C * ∑ l, v l ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := T.exists_tileFrozenMatrix_bound k
  refine ⟨(T.tileWeight k : ℝ) ^ (-(2 / (T.tileDim k : ℝ))) * C,
    mul_nonneg (Real.rpow_nonneg (T.tileWeight_nonneg k) _) hC, fun s t v ↦ ?_⟩
  rw [tileScaledKinetic, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (T.tileWeight_nonneg k) _)]
  calc _ ≤ (T.tileWeight k : ℝ) ^ (-(2 / (T.tileDim k : ℝ))) *
        (C * ∑ l, v l ^ 2) :=
      mul_le_mul_of_nonneg_left (hbound (s, t) v)
        (Real.rpow_nonneg (T.tileWeight_nonneg k) _)
    _ = _ := by ring

/-- The actual frozen coefficient has an unrestricted marked pressure limit.
The separate legal-pair recovery obligation is kept visible in the module
contract and the definition `tileAllowed`. -/
theorem exists_tileScaledKinetic_pressure_limit (k : T.Index) (hq : 4 < T.tileDim k)
    {g : ℝ → ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ s t, |g s t| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ OTSelector.Probability.markedScalePressure
        (T.tileDim k) ℝ ℝ (T.tileClockLaw k 0) (T.tileClockLaw k 1)
          (T.tileScaledKinetic k) g R t) Filter.atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p := by
  obtain ⟨C, hC, hbound⟩ := T.exists_tileScaledKinetic_bound k
  exact OTSelector.Probability.exists_markedScalePressure_limit (T.tileDim k) hq
    (T.tileClockLaw k 0) (T.tileClockLaw k 1) hC hG
    (T.measurable_tileScaledKinetic k) (T.tileScaledKinetic_nonneg k) hbound
    (fun s t c _ v ↦ T.tileScaledKinetic_homogeneous k s t c v) hg hgb

end PopulationLocalPressureCore.TaylorTiles
end OTSelector.Reconstruction
