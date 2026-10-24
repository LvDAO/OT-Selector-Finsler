import OTSelector.Reconstruction.OriginalOrientedCubeReflectedKernel
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume

/-! A single actual near-axis orthogonal cube fills all but vanishing volume. -/
open Set Function MeasureTheory Filter
open scoped BigOperators InnerProductSpace ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {q : ℕ}

/-- The actual raw-coordinate rotation error is bounded by the original
basis-vector errors. The coordinate supremum norm is on both sides. -/
theorem originalOrientedShapeNearFrame_raw_bound
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {δ : ℝ}
    (hb : ∀ j, ‖b j-(EuclideanSpace.basisFun (Fin q) ℝ) j‖ ≤ δ)
    (v : Fin q → ℝ) :
    ‖orthonormalPhysicalCubeMap b v-v‖ ≤ (q : ℝ)*δ*‖v‖ := by
  have hrep :
      (EuclideanSpace.equiv (Fin q) ℝ).symm
          (orthonormalPhysicalCubeMap b v-v) =
        ∑ j, v j • (b j-(EuclideanSpace.basisFun (Fin q) ℝ) j) := by
    rw [map_sub]
    change (orthonormalCubeCoordinates b).symm v -
      (orthonormalCubeCoordinates
        (EuclideanSpace.basisFun (Fin q) ℝ)).symm v = _
    rw [orthonormalCubeCoordinates_symm_eq_sum,
      orthonormalCubeCoordinates_symm_eq_sum,← Finset.sum_sub_distrib]
    simp only [smul_sub]
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin q) ℝ).symm
        (orthonormalPhysicalCubeMap b v-v)‖ := raw_norm_le_euclidean_norm _
    _ = ‖∑ j, v j • (b j-(EuclideanSpace.basisFun (Fin q) ℝ) j)‖ := congrArg norm hrep
    _ ≤ ∑ j, ‖v j • (b j-(EuclideanSpace.basisFun (Fin q) ℝ) j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin q, ‖v‖*δ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v j) (hb j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

/-- One smaller near-axis physical cube lies in the native unit cube. This
is true also in zero dimensions and requires no displacement coercivity. -/
theorem originalOrientedShapeNearFrame_cube_subset
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hb : ∀ j, ‖b j-(EuclideanSpace.basisFun (Fin q) ℝ) j‖ ≤ δ) :
    originalCenteredPhysicalCubeRegion b (1/(1+(q:ℝ)*δ)) ⊆
      haarRootCube (Fin q) (1/2) := by
  let s : ℝ := 1/(1+(q:ℝ)*δ)
  have hden : 0 < 1+(q:ℝ)*δ := by positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  intro x hx
  rcases hx with ⟨v,hv,rfl⟩
  have hvnorm : ‖v‖ ≤ s/2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ s/2)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hv.1 i],hv.2 i⟩
  have hOnorm : ‖orthonormalPhysicalCubeMap b v‖ ≤ (1:ℝ)/2 := by
    calc
      _ = ‖(orthonormalPhysicalCubeMap b v-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ ‖orthonormalPhysicalCubeMap b v-v‖+‖v‖ := norm_add_le _ _
      _ ≤ (q:ℝ)*δ*‖v‖+‖v‖ :=
        add_le_add (originalOrientedShapeNearFrame_raw_bound b hb v) le_rfl
      _ = (1+(q:ℝ)*δ)*‖v‖ := by ring
      _ ≤ (1+(q:ℝ)*δ)*(s/2) := mul_le_mul_of_nonneg_left hvnorm hden.le
      _ = _ := by dsimp [s]; field_simp
  change (fun _ ↦ -((1:ℝ)/2)) ≤ orthonormalPhysicalCubeMap b v ∧
    orthonormalPhysicalCubeMap b v ≤ (fun _ ↦ (1:ℝ)/2)
  constructor
  · intro i
    exact (abs_le.mp ((norm_le_pi_norm _ i).trans hOnorm)).1
  · intro i
    exact (abs_le.mp ((norm_le_pi_norm _ i).trans hOnorm)).2

/-- Exact physical inner-cube volume in the same frame. -/
theorem originalOrientedShape_cube_volume
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 ≤ s) :
    volume (originalCenteredPhysicalCubeRegion b s) = ENNReal.ofReal (s^q) := by
  have hside : 2*(s/2)=s := by ring
  have hbase : volume (originalCenteredPhysicalCubeRegion b s) =
      volume (haarRootCube (Fin q) (s/2)) := by
    simpa only [hside] using volume_originalOrientedTraffic_cube b (s/2)
  rw [hbase,volume_haarRootCube (Fin q) (by positivity),Fintype.card_fin,hside]

theorem originalOrientedShape_cube_real_volume
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 ≤ s) :
    volume.real (originalCenteredPhysicalCubeRegion b s) = s^q := by
  rw [measureReal_def,originalOrientedShape_cube_volume b hs,ENNReal.toReal_ofReal (by positivity)]

/-- The literal remaining hole has exactly the complementary volume. -/
theorem originalOrientedShape_cube_hole_real_volume
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {s : ℝ} (hs : 0 ≤ s)
    (hsub : originalCenteredPhysicalCubeRegion b s ⊆ haarRootCube (Fin q) (1/2)) :
    volume.real (haarRootCube (Fin q) (1/2) \ originalCenteredPhysicalCubeRegion b s) = 1-s^q := by
  have hside : 2*(s/2)=s := by ring
  have hmeas : MeasurableSet (originalCenteredPhysicalCubeRegion b s) := by
    simpa only [hside] using measurableSet_originalOrientedTraffic_cube b (s/2)
  have hfinite : volume (haarRootCube (Fin q) (1/2)) ≠ ⊤ := by
    rw [volume_haarRootCube (Fin q) (by norm_num)]
    exact ENNReal.ofReal_ne_top
  rw [measureReal_sdiff hsub hmeas hfinite,originalOrientedShape_cube_real_volume b hs,
    volume_real_haarRootCube (Fin q) (by norm_num)]
  norm_num

/-- Sending the basis approximation error to zero fills the native cube. -/
theorem originalOrientedShape_hole_mass_tendsto_zero (q : ℕ) :
    Tendsto (fun δ : ℝ ↦ 1-(1/(1+(q:ℝ)*δ))^q) (𝓝 0) (𝓝 0) := by
  have h : ContinuousAt (fun δ : ℝ ↦ 1-(1/(1+(q:ℝ)*δ))^q) 0 := by
    fun_prop (disch := norm_num)
  simpa using h.tendsto

end OTSelector.Reconstruction
