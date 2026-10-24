import OTSelector.Reconstruction.OriginalLegalScreeningComparatorRetainedCostMean
import OTSelector.Reconstruction.NormalizedHaarCubeCount
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual path-retained signed cost recovers its unchanged original value. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A genuine finite path-length cutoff recovers every original integrable
Palm observable when the collar diverges. No path moment is required. -/
theorem tendsto_original_truncated_Palm_integral
    {X : Type*} [MeasurableSpace X] {P : Measure X}
    {L f : X → ℝ} (hL : Measurable L) (hf : Measurable f) (hi : Integrable f P)
    {ell : ℝ → ℝ} (hlarge : Tendsto ell atTop atTop) :
    Tendsto (fun R ↦ ∫ m in {m | L m ≤ ell R}, f m ∂P) atTop (𝓝 (∫ m, f m ∂P)) := by
  classical
  have hmeas R : MeasurableSet {m | L m ≤ ell R} := measurableSet_le hL measurable_const
  have h := tendsto_integral_filter_of_dominated_convergence (fun m ↦ ‖f m‖)
    (F := fun R ↦ {m | L m ≤ ell R}.indicator f)
    (f := f)
    (.of_forall (fun R ↦ (hf.indicator (hmeas R)).aestronglyMeasurable))
    (.of_forall (fun R ↦ .of_forall (fun m ↦ by
      by_cases hm : L m ≤ ell R <;> simp [Set.indicator, hm]))) hi.norm
    (.of_forall (fun m ↦ by
      apply tendsto_const_nhds.congr'
      filter_upwards [hlarge.eventually (eventually_ge_atTop (L m))] with R hR
      simp [Set.indicator, hR]))
  simpa only [integral_indicator (hmeas _)] using h

/-- The true inner-cube volume has asymptotically the same normalization,
for any fixed collar factor and every finite dimension, including zero. -/
theorem tendsto_original_innerCube_volume_ratio
    (ι : Type*) [Fintype ι] {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    {k : ℝ} (_hk : 0 ≤ k) (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R ↦ volume.real (haarRootCube ι (R - k * ell R)) /
      volume.real (haarRootCube ι R)) atTop (𝓝 1) := by
  have hmodel : Tendsto (fun R ↦ (1 - k * (ell R / R)) ^ Fintype.card ι)
      atTop (𝓝 1) := by
    have hkell : Tendsto (fun R ↦ k * (ell R / R)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hsmall
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hkell).pow (Fintype.card ι)
  apply hmodel.congr'
  filter_upwards [hell, eventually_gt_atTop (0 : ℝ),
    eventually_collar_mul_le_radius (k := k) hsmall] with R he hR hke
  rw [volume_real_haarRootCube ι (sub_nonneg.mpr hke), volume_real_haarRootCube ι hR.le,
    ← div_pow]
  congr 1
  field_simp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Actual path retention, normalized by the original whole-cube volume,
recovers the same candidate's signed weighted value. This is the cost of the
actual retained edges, before any reserve repair or finite-index extraction. -/
theorem tendsto_originalPathRetainedPlan_normalized_weightedCost
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R ↦
      (∫ scene, ∫ e, originalWeightedEdgeCost kin g t e
        ∂(originalPathRetainedPlan S w R (ell R) scene : Measure
          (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)))
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) /
      volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R))
      atTop (𝓝 (Q.value t)) := by
  have htail := tendsto_original_truncated_Palm_integral
    (f := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
    (measurable_originalSeedPairPathLength S hF hw)
    (hk.add ((hg.comp measurable_fst).const_mul t))
    (Q.kinetic_integrable.add (Q.probe_integrable.const_mul t)) hlarge
  have hv := tendsto_original_innerCube_volume_ratio
    (Fin (finrank ℝ S.covector.ker)) hell (by norm_num : (0 : ℝ) ≤ 2) hsmall
  have hvalue : (∫ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 ∂legalMarkedJointPalm _ Q.law) = Q.value t := by
    rw [integral_add Q.kinetic_integrable (Q.probe_integrable.const_mul t), integral_const_mul]
    rfl
  rw [hvalue] at htail
  have h := hv.mul htail
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [] with R
  rw [(originalPathRetainedPlan_weightedCost_integrable_and_integral hF hw Q hk hg R (ell R) t).2]
  ring

end OTSelector.Reconstruction
