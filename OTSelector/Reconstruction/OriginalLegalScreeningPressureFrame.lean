import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostFiniteValue
import OTSelector.Reconstruction.OriginalLegalPressureRelativeStability
import OTSelector.Reconstruction.OriginalOrientedCubeReflectedKernel

/-! Exact original finite legal values in an actual orthonormal physical frame. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {q : ℕ}

/-- The kinetic coefficient in the chosen physical frame. Original marks and
indices are unchanged; the actual spatial displacement is rotated. -/
def originalScreeningFrameKinetic
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) : ℝ → ℝ → (Fin q → ℝ) → ℝ :=
  fun a c v ↦ kin a c (orthonormalPhysicalCubeMap b v)

theorem measurable_originalScreeningFrameKinetic
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2))) :
    Measurable (Function.uncurry (fun p : ℝ × ℝ ↦
      originalScreeningFrameKinetic b kin p.1 p.2)) := by
  exact hk.comp (measurable_fst.prodMk
    ((orthonormalPhysicalCubeMap b).continuous.measurable.comp measurable_snd))

/-- Orthogonal placement preserves the genuine Euclidean quadratic form,
including the zero-dimensional coordinate space. -/
theorem originalScreeningFrame_sum_sq
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (v : Fin q → ℝ) :
    ∑ i, (orthonormalPhysicalCubeMap b v i)^2 = ∑ i, (v i)^2 := by
  have h := congrArg (fun a : ℝ ↦ a^2) (norm_euclidean_orthonormalPhysicalCubeMap b v)
  simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] at h
  convert h using 1 <;> rfl

/-- No extra dimension factor enters the transformed quadratic growth bound. -/
theorem originalScreeningFrameKinetic_quadratic_bound
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {C : ℝ}
    (hkin : ∀ a c v, |kin a c v| ≤ C * ∑ i, v i^2) :
    ∀ a c v, |originalScreeningFrameKinetic b kin a c v| ≤ C * ∑ i, v i^2 := by
  intro a c v
  exact (hkin a c _).trans_eq (by rw [originalScreeningFrame_sum_sq])

theorem originalScreeningFrameKinetic_homogeneous
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c * v i) = c^2 * kin a d v) :
    ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      originalScreeningFrameKinetic b kin a d (fun i ↦ c * v i) =
        c^2 * originalScreeningFrameKinetic b kin a d v := by
  intro a d c hc v
  change kin a d (orthonormalPhysicalCubeMap b (c • v)) = _
  rw [map_smul]
  exact hhom a d c hc _

/-- The literal centered physical displacement, before any support restriction. -/
theorem originalOrientedRawCubePhysicalMap_sub
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (u v : Fin q → ℝ) :
    originalOrientedRawCubePhysicalMap b R v - originalOrientedRawCubePhysicalMap b R u =
      orthonormalPhysicalCubeMap b ((2*R) • (v-u)) := by
  unfold originalOrientedRawCubePhysicalMap
  rw [← map_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Exact physical-frame transport of the original maximum-cardinality legal
minimum, for every original cloud, even outside the sampling cube. -/
theorem originalScreeningFullValue_eq_unclamped_frame
    (hq : 0 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 0 ≤ R) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c * v i) = c^2 * kin a d v)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (cloud : TwoMarkedCloudSpace q ℝ ℝ) :
    originalScreeningFullValue b R kin g t cloud =
      unclampedBlockLegalTilted q id id ((2*R)^q) (originalScreeningFrameKinetic b kin)
        g t (cloudEncode cloud.1) (cloudEncode cloud.2) := by
  have hs : 0 ≤ 2*R := mul_nonneg (by norm_num) hR
  have hp := rpow_affine_intensity q hq (r := 1) (by norm_num) hs
  simp only [one_mul,Real.one_rpow] at hp
  unfold originalScreeningFullValue unclampedBlockLegalTilted
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j _
  change 1 ^ (2/(q : ℝ)) * kin _ _
    (originalOrientedRawCubePhysicalMap b R (cloud.2.2 j).1 -
      originalOrientedRawCubePhysicalMap b R (cloud.1.2 i).1) + _ = _
  rw [originalOrientedRawCubePhysicalMap_sub,Real.one_rpow,one_mul,hp]
  exact congrArg (fun a : ℝ ↦ a + t*g (cloud.1.2 i).2 (cloud.2.2 j).2)
    (originalScreeningFrameKinetic_homogeneous b hhom _ _ (2*R) hs _)

/-- The genuine original iid cube sampler makes the exact transport agree
with the globally truncated finite legal value almost everywhere. -/
theorem ae_originalScreeningFullValue_eq_block_frame
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (rate : ℝ≥0) (hq : 0 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 0 ≤ R) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c * v i) = c^2 * kin a d v)
    (g : ℝ → ℝ → ℝ) (t : ℝ) :
    ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate,
      originalScreeningFullValue b R kin g t cloud =
        blockLegalTilted q id id ((2*R)^q) (originalScreeningFrameKinetic b kin)
          g t (cloudEncode cloud.1) (cloudEncode cloud.2) := by
  filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q α β rate] with cloud hc
  rw [originalScreeningFullValue_eq_unclamped_frame hq b hR kin hhom]
  exact unclampedBlockLegalTilted_eq_block q id id _ _ g t _ _
    (fun i ↦ hc.1 i) (fun j ↦ hc.2 j)

/-- The same equality in the canonical original-cloud pressure interface. -/
theorem ae_originalScreeningFullValue_eq_legalMarkedTilted_frame
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (rate : ℝ≥0) (hq : 0 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 0 ≤ R) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c * v i) = c^2 * kin a d v)
    (g : ℝ → ℝ → ℝ) (t : ℝ) :
    ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate,
      originalScreeningFullValue b R kin g t cloud =
        legalMarkedTilted q id id ((2*R)^q) (originalScreeningFrameKinetic b kin) g t cloud := by
  filter_upwards [ae_originalScreeningFullValue_eq_block_frame α β rate hq b hR kin hhom g t]
    with cloud hc
  exact hc.trans (by
    unfold blockLegalTilted legalMarkedTilted legalMarkedFixedValue
    congr 1)


/-- The standard orthonormal basis is the literal identity physical frame. -/
theorem orthonormalPhysicalCubeMap_basisFun (v : Fin q → ℝ) :
    orthonormalPhysicalCubeMap (EuclideanSpace.basisFun (Fin q) ℝ) v = v := rfl

/-- Exact axis-cube readout with the transformed kinetic coefficient, without
homogeneity, dimension, radius, or spatial support assumptions. -/
theorem originalScreeningFullValue_eq_axis_frame
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (cloud : TwoMarkedCloudSpace q ℝ ℝ) :
    originalScreeningFullValue b R kin g t cloud =
      originalScreeningFullValue (EuclideanSpace.basisFun (Fin q) ℝ) R
        (originalScreeningFrameKinetic b kin) g t cloud := by
  unfold originalScreeningFullValue unclampedBlockLegalTilted
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j _
  change _ * kin (cloud.1.2 i).2 (cloud.2.2 j).2
      (orthonormalPhysicalCubeMap b (fun l ↦ 2*R*(cloud.2.2 j).1 l-R) -
        orthonormalPhysicalCubeMap b (fun l ↦ 2*R*(cloud.1.2 i).1 l-R)) + _ =
    _ * kin (cloud.1.2 i).2 (cloud.2.2 j).2
      (orthonormalPhysicalCubeMap b
        (orthonormalPhysicalCubeMap (EuclideanSpace.basisFun (Fin q) ℝ)
          (fun l ↦ 2*R*(cloud.2.2 j).1 l-R) -
        orthonormalPhysicalCubeMap (EuclideanSpace.basisFun (Fin q) ℝ)
          (fun l ↦ 2*R*(cloud.1.2 i).1 l-R))) + _
  rw [orthonormalPhysicalCubeMap_basisFun,orthonormalPhysicalCubeMap_basisFun,map_sub]
  rfl

end OTSelector.Reconstruction
