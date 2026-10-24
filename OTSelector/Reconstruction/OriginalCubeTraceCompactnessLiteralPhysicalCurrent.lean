import OTSelector.Reconstruction.OriginalCubeTraceCompactnessLiteralFaceReadout
import OTSelector.Reconstruction.OriginalCurrentPhysicalCubeTraceBound

/-! The physical common trace bound controls the literal original vector-current boundary pairing. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual signed true-normal boundary pairing of a physical vector field on the centered
side-R cube. Face coordinates use original coordinate area, with the same orthonormal frame. -/
def originalPhysicalCubeVectorBoundaryPairing {r : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
    (J : (Fin (r + 1) → ℝ) → Fin (r + 1) → ℝ) (R : ℝ)
    (φ : (Fin (r + 1) → ℝ) → ℝ) : ℝ :=
  ∑ j : Fin (r + 1) × Fin 2, (if j.2 = 0 then (-1 : ℝ) else 1) *
    ∫ z in Icc (fun _ : Fin r ↦ -R / 2) (fun _ ↦ R / 2),
      originalEuclideanNormalReadout (b j.1)
        (J (orthonormalPhysicalCubeMap b
          (j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) z))) *
        φ (orthonormalPhysicalCubeMap b
          (j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) z))

/-- Equality of the actual scalar normal fields on almost every face point preserves the
entire physical pairing for all tests on the same exceptional set. -/
theorem originalPhysicalCubeVectorBoundaryPairing_congr_ae {r : ℕ}
    (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
    {J K : (Fin (r + 1) → ℝ) → Fin (r + 1) → ℝ} (R : ℝ)
    (hJK : ∀ j : Fin (r + 1) × Fin 2, ∀ᵐ z ∂volume.restrict
      (Icc (fun _ : Fin r ↦ -R / 2) (fun _ ↦ R / 2)),
      originalEuclideanNormalReadout (b j.1)
          (J (orthonormalPhysicalCubeMap b
            (j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) z))) =
        originalEuclideanNormalReadout (b j.1)
          (K (orthonormalPhysicalCubeMap b
            (j.1.insertNth (if j.2 = 0 then -R / 2 else R / 2) z))))
    (φ : (Fin (r + 1) → ℝ) → ℝ) :
    originalPhysicalCubeVectorBoundaryPairing b J R φ =
      originalPhysicalCubeVectorBoundaryPairing b K R φ := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply integral_congr_ae
  filter_upwards [hJK j] with z hz
  rw [hz]

local instance originalLiteralPhysicalCurrentColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {r : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin (r + 1) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching (r + 1) α β kin g)
  (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
  (j : LegalMarkedOptimalInputScene (r + 1) → Fin (r + 1) → ℝ)
  (hj : ∀ k, MemLp (fun s ↦ j s k) 2 (Q.law : Measure _))

/-- The physical signed Hilbert face pairing agrees, simultaneously for all tests, with the
literal original current evaluated at actual rerooted physical boundary points. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_originalCurrent_physicalCube_pairing_eq
    (hm : Measurable j) (R : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ φ : (Fin (r + 1) → ℝ) → ℝ,
      Q.scenePhysicalCubeBoundaryPairing b
        (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
          (originalEuclideanNormalReadout (b i))) R s φ =
        originalPhysicalCubeVectorBoundaryPairing b
          (fun z ↦ j (legalMarkedInputSceneReroot (r + 1) z s)) R φ := by
  let x := fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
    (originalEuclideanNormalReadout (b i))
  have he : ∀ a : Fin (r + 1) × Fin 2, ∀ᵐ s ∂(Q.law : Measure _),
      ∀ᵐ z ∂volume.restrict (Icc (fun _ : Fin r ↦ -R / 2) (fun _ ↦ R / 2)),
      x a.1 (legalMarkedInputSceneReroot (r + 1)
        (orthonormalPhysicalCubeMap b
          (a.1.insertNth (if a.2 = 0 then -R / 2 else R / 2) z)) s) =
      originalEuclideanNormalReadout (b a.1)
        (j (legalMarkedInputSceneReroot (r + 1)
          (orthonormalPhysicalCubeMap b
            (a.1.insertNth (if a.2 = 0 then -R / 2 else R / 2) z)) s)) := by
    intro a
    apply Q.ae_ae_reroot_eq_of_ae_eq _ (Lp.stronglyMeasurable (x a.1)).measurable
      ((originalEuclideanNormalReadout (b a.1)).continuous_of_finiteDimensional.measurable.comp hm)
      (coeFn_originalLinearCurrentReadoutLtwo _ _ hj (originalEuclideanNormalReadout (b a.1)))
    fun_prop
  filter_upwards [ae_all_iff.mpr he] with s hs
  intro φ
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply integral_congr_ae
  filter_upwards [hs a] with z hz
  exact congrArg (fun t : ℝ ↦ t * φ (orthonormalPhysicalCubeMap b
    (a.1.insertNth (if a.2 = 0 then -R / 2 else R / 2) z))) hz

/-- The same concrete measurable random coefficient controls the literal original physical
current boundary pairing against every C1 mean-zero test, with actual physical gradient energy. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_smooth_originalCurrent_physicalCube_pairing_sq_le
    (hm : Measurable j) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ (φ : (Fin (r + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ →
      (∫ z in originalCenteredPhysicalCubeRegion b R, φ z) = 0 →
      (originalPhysicalCubeVectorBoundaryPairing b
        (fun z ↦ j (legalMarkedInputSceneReroot (r + 1) z s)) R φ)^2 ≤
        Q.scenePhysicalCubeTraceDualBound b
          (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
            (originalEuclideanNormalReadout (b i))) R s *
          ∑ k : Fin (r + 1), ∫ z in originalCenteredPhysicalCubeRegion b R,
            (fderiv ℝ φ z (Pi.single k 1))^2 := by
  let x := fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
    (originalEuclideanNormalReadout (b i))
  filter_upwards [Q.ae_all_originalCurrent_physicalCube_pairing_eq b j hj hm R,
    Q.ae_all_smooth_physicalCube_pairing_sq_le b x hR] with s he hb
  intro φ hφ hmφ
  rw [← he φ]
  exact hb φ hφ hmφ

end OTSelector.Reconstruction
