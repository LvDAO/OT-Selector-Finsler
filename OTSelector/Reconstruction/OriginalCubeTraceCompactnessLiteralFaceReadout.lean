import OTSelector.Reconstruction.OriginalCubeTraceCompactnessRawFaceFlux
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessNormalReadout
import OTSelector.Reconstruction.OriginalCurrentSpatialReroot
import OTSelector.Reconstruction.OriginalCurrentAllFacesTraceBound

/-! Almost-everywhere identification of Hilbert face representatives with literal current fields. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability
local instance originalLiteralFaceColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q α β kin g)

/-- Equality of two original scene observables remains valid on almost every point of any
measurably parameterized face, on one full-measure set of the original scenes. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_reroot_eq_of_ae_eq
    {T : Type*} [MeasurableSpace T] (ν : Measure T) [SFinite ν]
    {x f : LegalMarkedOptimalInputScene q → ℝ} (hx : Measurable x) (hf : Measurable f)
    (hxf : x =ᵐ[(Q.law : Measure _)] f) (v : T → Fin q → ℝ) (hv : Measurable v) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ᵐ y ∂ν,
      x (legalMarkedInputSceneReroot q (v y) s) =
        f (legalMarkedInputSceneReroot q (v y) s) := by
  have hr : Measurable (fun p : T × LegalMarkedOptimalInputScene q ↦
      legalMarkedInputSceneReroot q (v p.1) p.2) := by
    change Measurable ((fun p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q ↦
      legalMarkedInputSceneReroot q p.1 p.2) ∘
        (fun p : T × LegalMarkedOptimalInputScene q ↦ (v p.1, p.2)))
    exact (measurable_legalMarkedInputSceneReroot_joint q).comp
      ((hv.comp measurable_fst).prodMk measurable_snd)
  have hm : MeasurableSet {p : T × LegalMarkedOptimalInputScene q |
      x (legalMarkedInputSceneReroot q (v p.1) p.2) =
        f (legalMarkedInputSceneReroot q (v p.1) p.2)} :=
    measurableSet_eq_fun (hx.comp hr) (hf.comp hr)
  apply (Measure.ae_ae_comm hm).mp
  exact ae_of_all ν (fun y ↦ (Q.stationary (v y)).quasiMeasurePreserving.ae hxf)

/-- The selected Hilbert representative agrees with the literal observable at the exact
original face point, including its scale-dependent normal and tangential offsets. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_sceneScalarFaceReadout_eq_of_ae_eq
    {ι : Type*} [Fintype ι] (L : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))
    (offset : ℝ → EuclideanSpace ℝ (Fin q))
    (x : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    {f : LegalMarkedOptimalInputScene q → ℝ} (hf : Measurable f) (hxf : x =ᵐ[(Q.law : Measure _)] f)
    (R : ℝ) (ν : Measure (ι → ℝ)) [SFinite ν] :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ᵐ y ∂ν,
      Q.sceneScalarFaceReadout L offset x R y s =
        f (legalMarkedInputSceneReroot q
          (EuclideanSpace.equiv (Fin q) ℝ (offset R + L (R • y))) s) := by
  have hv : Measurable (fun y : ι → ℝ ↦
      EuclideanSpace.equiv (Fin q) ℝ (offset R + L (R • y))) := by fun_prop
  simpa only [Q.sceneScalarFaceReadout_apply] using
    Q.ae_ae_reroot_eq_of_ae_eq ν (Lp.stronglyMeasurable x).measurable hf hxf _ hv

/-- Almost-everywhere changes to individual face data preserve the complete signed boundary
pairing for every test, without any dependence of its exceptional set on that test. -/
theorem originalRawUnitCubeBoundaryPairing_congr_ae {r : ℕ}
    {f h : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ}
    (hfh : ∀ j, f j =ᵐ[volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))] h j)
    (φ : (Fin (r + 1) → ℝ) → ℝ) :
    originalRawUnitCubeBoundaryPairing f φ = originalRawUnitCubeBoundaryPairing h φ := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply integral_congr_ae
  filter_upwards [hfh j] with y hy
  rw [hy]

/-- Literal measurable original observables on the exact same ordered centered faces. -/
def LegalWeightedStationaryPoissonMatching.sceneLiteralAllFacesReadout {r : ℕ}
    {kin : ℝ → ℝ → (Fin (r + 1) → ℝ) → ℝ}
    (_Q : LegalWeightedStationaryPoissonMatching (r + 1) α β kin g)
    (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
    (f : Fin (r + 1) → LegalMarkedOptimalInputScene (r + 1) → ℝ)
    (R : ℝ) (s : LegalMarkedOptimalInputScene (r + 1))
    (j : Fin (r + 1) × Fin 2) (y : Fin r → ℝ) : ℝ :=
  f j.1 (legalMarkedInputSceneReroot (r + 1)
    (EuclideanSpace.equiv (Fin (r + 1)) ℝ
      (originalCenteredCubeFaceOffset b j (R / 2) + orderedOrthonormalFaceMap b j.1 (R • y))) s)

/-- The same concrete measurable Hilbert bound controls all smooth mean-zero tests against
the literal original observables, simultaneously on one full-measure scene set. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_smooth_literal_faces_pairing_sq_le
    {r : ℕ} {kin : ℝ → ℝ → (Fin (r + 1) → ℝ) → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (r + 1) α β kin g)
    (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
    (x : Fin (r + 1) → Lp ℝ 2 (Q.law : Measure _))
    (f : Fin (r + 1) → LegalMarkedOptimalInputScene (r + 1) → ℝ)
    (hf : ∀ i, Measurable (f i)) (hxf : ∀ i, x i =ᵐ[(Q.law : Measure _)] f i) (R : ℝ) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ (φ : (Fin (r + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ →
      (∫ z in Icc (fun _ : Fin (r + 1) ↦ (0 : ℝ)) (fun _ ↦ 1), φ z) = 0 →
      (originalRawUnitCubeBoundaryPairing (Q.sceneLiteralAllFacesReadout b f R s) φ)^2 ≤
        Q.sceneAllFacesTraceDualBound b x R s * originalRawUnitCubeGradientEnergy φ := by
  have heq : ∀ j : Fin (r + 1) × Fin 2, ∀ᵐ s ∂(Q.law : Measure _),
      Q.sceneAllFacesReadout b x R s j =ᵐ[
        volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))]
        Q.sceneLiteralAllFacesReadout b f R s j := by
    intro j
    exact Q.ae_ae_sceneScalarFaceReadout_eq_of_ae_eq (orderedOrthonormalFaceMap b j.1)
      (fun t ↦ originalCenteredCubeFaceOffset b j (t / 2)) (x j.1) (hf j.1) (hxf j.1) R _
  filter_upwards [ae_all_iff.mpr heq,
    Q.ae_all_smooth_all_faces_pairing_sq_le_sceneAllFacesTraceDualBound b x R] with s hs hb
  intro φ hφ hm
  rw [← originalRawUnitCubeBoundaryPairing_congr_ae hs φ]
  exact hb φ hφ hm

section ActualCurrent
open OTSelector.Geometry ContinuousFinslerNorm Module Manifold
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
  {w : S.covector.ker} (hw : w ∈ S.labels)
  {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
include hF hw hη

/-- The actual whole clock-set current is measurable for every clock set, including before
any conditional moments or finite-energy assumptions have been supplied. -/
theorem stronglyMeasurable_original_pathClockSetCurrent (A : Set ℝ) :
    StronglyMeasurable (originalSeedPathClockSetCurrent S w η A) := by
  exact (stronglyMeasurable_original_pathClockWindowReadout_joint S hF hw hη).integral_prod_right'

/-- The genuine L2 current readout on almost every face point is the literal original
spatially translated path current in the same scene and clock set. -/
theorem LegalWeightedStationaryPoissonMatching.ae_ae_originalLinearCurrent_face_eq
    {μ ν : Measure ℝ} {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (A : Set ℝ)
    (hj : ∀ k, MemLp (fun s ↦ originalSeedPathClockSetCurrent S w η A s k) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (C : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι]
    (L : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))
    (offset : ℝ → EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))
    (R : ℝ) (ρ : Measure (ι → ℝ)) [SFinite ρ] :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ᵐ y ∂ρ,
      Q.sceneScalarFaceReadout L offset
        (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
          (originalSeedPathClockSetCurrent S w η A) hj C.toLinearMap) R y s =
        C (originalSeedPathClockSetCurrent S w
          (fun z ↦ η (z - EuclideanSpace.equiv (Fin (finrank ℝ S.covector.ker)) ℝ
            (offset R + L (R • y)))) A s) := by
  have hf : Measurable (fun s ↦ C (originalSeedPathClockSetCurrent S w η A s)) :=
    C.continuous.measurable.comp
      (stronglyMeasurable_original_pathClockSetCurrent S hF hw hη A).measurable
  have he := Q.ae_ae_sceneScalarFaceReadout_eq_of_ae_eq L offset
    (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
      (originalSeedPathClockSetCurrent S w η A) hj C.toLinearMap) hf
    (coeFn_originalLinearCurrentReadoutLtwo _ _ hj C.toLinearMap) R ρ
  filter_upwards [he] with s hs
  filter_upwards [hs] with y hy
  exact hy.trans (congrArg C (originalSeedPathClockSetCurrent_reroot S hF hw hη A _ s))

end ActualCurrent
end OTSelector.Reconstruction
