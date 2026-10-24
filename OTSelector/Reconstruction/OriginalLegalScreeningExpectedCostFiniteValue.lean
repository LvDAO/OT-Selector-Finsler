import OTSelector.Reconstruction.FinslerRelativeLawOriginalRawClassValue
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedCubeCost
import OTSelector.Reconstruction.OriginalReserveMappedWindowSampler
import OTSelector.Reconstruction.OriginalIIDCubePopulationCouplingOrientedCubeVolume

/-! Genuine finite legal values of actual same-frame original Poisson arrays are integrable. -/
open Set Function MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {q : ℕ}

/-- The original maximum-cardinality finite legal optimum, evaluated on all
unchanged physical same-frame input indices and their actual clock marks. -/
def originalScreeningFullValue
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (cloud : TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  let arrays := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) cloud
  unclampedBlockLegalTilted q id id 1 kin g t arrays.1 arrays.2

/-- The actual finite value is measurable before choosing a screening plan. -/
theorem measurable_originalScreeningFullValue
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (originalScreeningFullValue b R kin g t) :=
  (measurable_unclampedBlockLegalTilted q measurable_id measurable_id 1 hk hg t).comp
    (measurable_originalMappedReserveCloudArrays q (measurable_originalOrientedRawCubePhysicalMap b R))

private theorem physicalMap_mem_cube
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 ≤ R)
    {x : Fin q → ℝ} (hx : x ∈ unitCube q) :
    originalOrientedRawCubePhysicalMap b R x ∈ originalCenteredPhysicalCubeRegion b (2*R) := by
  rw [originalOrientedTraffic_cube_eq_preimage]
  change (orthonormalPhysicalCubeMap b).symm
    ((orthonormalPhysicalCubeMap b) (fun i ↦ 2*R*x i-R)) ∈ haarRootCube (Fin q) R
  rw [ContinuousLinearEquiv.symm_apply_apply]
  constructor <;> intro i
  · have hx0 : 0 ≤ x i := (hx i (mem_univ i)).1.le
    change -R ≤ 2*R*x i-R
    nlinarith
  · have hx1 : x i ≤ 1 := (hx i (mem_univ i)).2.le
    change 2*R*x i-R ≤ R
    nlinarith

/-- Original Poisson counts and the true same-frame diameter bound give L1
for the literal unclamped finite optimum. The quadratic coefficient is fixed
before reserve intensity, physical radius and tilt are selected. -/
theorem originalScreeningFullValue_integrable_and_ae_bound
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 0 ≤ R)
    (rate : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C*∑ i, v i^2)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    Integrable (originalScreeningFullValue b R kin g t) (twoMarkedCloudLaw q ℝ ℝ α β rate) ∧
      ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate,
        |originalScreeningFullValue b R kin g t cloud| ≤
          (mSourceCount cloud : ℝ)*(4*C*(q : ℝ)*R^2+|t| * G) := by
  let A := 4*C*(q : ℝ)*R^2+|t| * G
  have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : ∀ᵐ cloud ∂twoMarkedCloudLaw q ℝ ℝ α β rate,
      |originalScreeningFullValue b R kin g t cloud| ≤ (mSourceCount cloud : ℝ)*A := by
    filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q α β rate] with cloud hcloud
    let arrays := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) cloud
    have hedge (i : Fin arrays.1.1) (j : Fin arrays.2.1) :
        |kin (arrays.1.2 i).2 (arrays.2.2 j).2
          (fun l ↦ (arrays.2.2 j).1 l-(arrays.1.2 i).1 l)+
          t*g (arrays.1.2 i).2 (arrays.2.2 j).2| ≤ A := by
      have hs := physicalMap_mem_cube b hR (hcloud.1 (i : ℕ))
      have ht := physicalMap_mem_cube b hR (hcloud.2 (j : ℕ))
      have hd := originalOrientedPhysicalCube_square_distance_le b hR hs ht
      change dist ((EuclideanSpace.equiv _ ℝ).symm (arrays.1.2 i).1)
        ((EuclideanSpace.equiv _ ℝ).symm (arrays.2.2 j).1)^2 ≤ 4*(q : ℝ)*R^2 at hd
      have hsum : (∑ l, ((arrays.2.2 j).1 l-(arrays.1.2 i).1 l)^2) =
          dist ((EuclideanSpace.equiv _ ℝ).symm (arrays.1.2 i).1)
            ((EuclideanSpace.equiv _ ℝ).symm (arrays.2.2 j).1)^2 := by
        rw [dist_comm,dist_eq_norm,EuclideanSpace.norm_sq_eq]
        apply Finset.sum_congr rfl
        intro l _
        simp only [PiLp.sub_apply,Real.norm_eq_abs,sq_abs]
        rfl
      have hk' := hkb (arrays.1.2 i).2 (arrays.2.2 j).2
        (fun l ↦ (arrays.2.2 j).1 l-(arrays.1.2 i).1 l)
      rw [hsum] at hk'
      have hg' : |t*g (arrays.1.2 i).2 (arrays.2.2 j).2| ≤ |t| * G := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg t)
      exact (abs_add_le _ _).trans
        ((add_le_add (hk'.trans (mul_le_mul_of_nonneg_left hd hC)) hg').trans_eq (by dsimp [A]; ring))
    have hv := PartialMatching.abs_legalMaximumValue_le_min
      (scalarClockLegalGraph (fun i ↦ (arrays.1.2 i).2) (fun j ↦ (arrays.2.2 j).2))
      (fun i j ↦ kin (arrays.1.2 i).2 (arrays.2.2 j).2
        (fun l ↦ (arrays.2.2 j).1 l-(arrays.1.2 i).1 l)+t*g (arrays.1.2 i).2 (arrays.2.2 j).2) hA hedge
    change |originalScreeningFullValue b R kin g t cloud| ≤ _
    have hv' : |originalScreeningFullValue b R kin g t cloud| ≤
        ((min arrays.1.1 arrays.2.1 : ℕ) : ℝ)*A := by
      simpa only [originalScreeningFullValue,unclampedBlockLegalTilted,
        Real.one_rpow,one_mul,id_eq] using hv
    exact hv'.trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.min_le_left _ _)) hA)
  refine ⟨((integrable_mSourceCount q α β rate).mul_const A).mono'
    (measurable_originalScreeningFullValue b R hk hg t).aestronglyMeasurable ?_,hb⟩
  exact hb.mono fun cloud h ↦ by simpa only [Real.norm_eq_abs] using h

section Focal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {α β : Measure ℝ}

/-- The original focal model supplies its own finite-value L1 and coarse
coefficient, chosen before frame, radius, raw reserve intensity and tilt.
Neither an energy bound nor a finite legal-value bound is assumed. -/
theorem OriginalSeedConditionalMoments.exists_original_screening_focalValue_bound
    (D : OriginalSeedConditionalMoments S w α β)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds α β gap diameter)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) :
    letI : IsProbabilityMeasure α := D.support.source.probability
    letI : IsProbabilityMeasure β := D.support.target.probability
    ∃ C ≥ 0, ∀ (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R : ℝ), 0 ≤ R →
      ∀ (rate : ℝ≥0) (t : ℝ),
        Integrable (originalScreeningFullValue b R (D.originalFocalKinetic gap) g t)
          (twoMarkedCloudLaw _ ℝ ℝ α β rate) ∧
        ∀ᵐ cloud ∂twoMarkedCloudLaw _ ℝ ℝ α β rate,
          |originalScreeningFullValue b R (D.originalFocalKinetic gap) g t cloud| ≤
            (mSourceCount cloud : ℝ)*(4*C*(finrank ℝ S.covector.ker : ℝ)*R^2+|t| * G) := by
  let : IsProbabilityMeasure α := D.support.source.probability
  let : IsProbabilityMeasure β := D.support.target.probability
  obtain ⟨C,hC,hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  exact ⟨C,hC,fun b R hR rate t ↦ originalScreeningFullValue_integrable_and_ae_bound
    α β b hR rate hC (D.measurable_originalFocalKinetic hF hw gap) hkb hg hgb t⟩

end Focal

end OTSelector.Reconstruction
