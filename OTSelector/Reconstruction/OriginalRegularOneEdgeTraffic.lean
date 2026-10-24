import OTSelector.Reconstruction.OriginalMaskedOneEdgeTraffic

/-!
# Original regular-clock physical one-edge traffic

At every actual interior clock the original positive kernel is invertible and
continuous. It therefore produces a physical quarter-cone neighborhood and the
same universal one-edge traffic estimate. This covers the compact regular
portion between the two actual focal collars.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Continuity and actual invertibility supply a physical cone near any regular clock. -/
theorem exists_regular_mobility_velocity_cone {W : ℝ → Matrix ι ι ℝ} {c : ℝ}
    (hW : ContinuousAt W c) (hc : IsUnit (W c).det) :
    ∃ δ > 0, ∀ r : ℝ, |r - c| ≤ δ → ∀ p : ι → ℝ,
      ‖W r *ᵥ p - W c *ᵥ p‖ ≤ ‖W c *ᵥ p‖ / 4 := by
  let _ := Matrix.invertibleOfIsUnitDet (W c) hc
  have hrel : ContinuousAt (fun r ↦ ‖W r * (W c)⁻¹ - 1‖) c :=
    ((hW.mul continuousAt_const).sub continuousAt_const).norm
  have hzero : ‖W c * (W c)⁻¹ - 1‖ < (1 / 4 : ℝ) := by
    rw [Matrix.mul_inv_of_invertible, sub_self, norm_zero]
    norm_num
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp
    (hrel.eventually_lt continuousAt_const hzero)
  refine ⟨δ / 2,half_pos hδ,?_⟩
  intro r hr p
  have hh : ‖W r * (W c)⁻¹ - 1‖ ≤ (1 / 4 : ℝ) :=
    (hbound (by rw [Real.dist_eq]; linarith)).le
  have h := norm_mobility_velocity_sub_le (W r) (W c) hc p hh
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Every actual regular physical clock supplies its own true cone neighborhood. -/
theorem exists_original_regular_physicalVelocityCone
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) {c : ℝ}
    (hc : c - S.level ∈ Ioo D.lo D.hi) :
    ∃ δ > 0, ∀ r : ℝ, |r - c| ≤ δ →
      r - S.level ∈ Ioo D.lo D.hi ∧
      ∀ p : Fin (finrank ℝ S.covector.ker) → ℝ,
        ‖originalSeedKernel S w (r - S.level) *ᵥ p -
          originalSeedKernel S w (c - S.level) *ᵥ p‖ ≤
            ‖originalSeedKernel S w (c - S.level) *ᵥ p‖ / 4 := by
  have hkernel := (D.original_kernel_regular hF hw).1.continuousAt (isOpen_Ioo.mem_nhds hc)
  have hshift : ContinuousAt (fun r : ℝ ↦ r - (S.level : ℝ)) c :=
    continuousAt_id.sub continuousAt_const
  have hcont : ContinuousAt (fun r ↦ originalSeedKernel S w (r - S.level)) c :=
    ContinuousAt.comp (f := fun r : ℝ ↦ r - (S.level : ℝ)) (x := c) hkernel hshift
  have hunit := ((D.original_kernel_regular hF hw).2 (c - S.level) hc).isUnit
  obtain ⟨δ,hδ,hcone⟩ := exists_regular_mobility_velocity_cone hcont
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  let d := min δ (min ((c - S.level - D.lo) / 2) ((D.hi - (c - S.level)) / 2))
  have hd : 0 < d := lt_min hδ (lt_min (by linarith [hc.1]) (by linarith [hc.2]))
  refine ⟨d,hd,?_⟩
  intro r hr
  have hrd : |r - c| ≤ δ := hr.trans (min_le_left _ _)
  refine ⟨?_,hcone r hrd⟩
  have hl : d ≤ (c - S.level - D.lo) / 2 :=
    (min_le_right δ _).trans (min_le_left _ _)
  have hh : d ≤ (D.hi - (c - S.level)) / 2 :=
    (min_le_right δ _).trans (min_le_right _ _)
  have habs := abs_le.mp hr
  constructor <;> nlinarith [habs.1,habs.2,hc.1,hc.2]

/-- The actual original regular window also has the literal min-one one-edge estimate. -/
theorem exists_original_regular_oneEdgeTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) {c : ℝ}
    (hc : c - S.level ∈ Ioo D.lo D.hi) :
    ∃ δ > 0, ∀ l r : ℝ, l ≤ r → (∀ s ∈ Icc l r, |s - c| ≤ δ) →
      ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      m.1.1 - S.level ∈ Ioo D.lo D.hi →
      ∀ R M : ℝ, 0 ≤ R → 0 ≤ M → ∀ f : ℝ → ℝ≥0∞,
      (∀ s ∈ Icc l r, f s ≤ ENNReal.ofReal
        (M * ‖originalSeedKernel S w (s - S.level) *ᵥ originalSeedPairMomentum S w m‖)) →
      (∀ s ∈ Icc l r, R < ‖originalSeedCompletePath S w x m s‖ → f s = 0) →
      (∫⁻ s in Icc l r, f s) ≤ ENNReal.ofReal
        ((4 * M * (R + 1)) * min 1
          ((r - l) * ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m‖)) := by
  obtain ⟨δ,hδ,hcone⟩ := D.exists_original_regular_physicalVelocityCone hF hw hc
  refine ⟨δ,hδ,?_⟩
  intro l r hlr hband x m hm R M hR hM f hf hfR
  exact D.original_oneEdgeTraffic_le_min_one_of_physicalCone hF hw x m hm hlr hR hM
    (fun s hs ↦ (hcone s (hband s hs)).1)
    (fun s hs ↦ (hcone s (hband s hs)).2 _) hf hfR

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
