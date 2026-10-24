import OTSelector.Reconstruction.OriginalStageAxisPortArrays

/-! The actual original finite port arrays yield physical probability families
with true unit Euclidean error and exact class measure readouts. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The literal canonical reflected law attached to the same original port,
read in its actual Euclidean physical coordinates. -/
def originalPhysicalAxisPortLaw {q : ℕ} (R : ℝ) (x : Fin q → ℝ) :=
  (originalAxisPortProbabilityMeasure R x).map (EuclideanSpace.equiv (Fin q) ℝ).symm

/-- The actual port law is a probability and pays at most one unit of genuine
Euclidean square deviation, without a coordinate dimension factor. -/
theorem originalPhysicalAxisPortLaw_spec {q : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {x : Fin q → ℝ} (hx : x ∈ haarRootCube (Fin q) R) :
    IsProbabilityMeasure (originalPhysicalAxisPortLaw R x) ∧
    Integrable (fun v ↦ dist ((EuclideanSpace.equiv (Fin q) ℝ).symm x) v^2)
      (originalPhysicalAxisPortLaw R x) ∧
    (∫ v, dist ((EuclideanSpace.equiv (Fin q) ℝ).symm x) v^2
      ∂originalPhysicalAxisPortLaw R x) ≤ 1 := by
  have : IsProbabilityMeasure (originalAxisPortProbabilityMeasure R x) :=
    originalAxisPortProbabilityMeasure_isProbability hR hx
  let e := (EuclideanSpace.equiv (Fin q) ℝ).symm
  have he : Measurable e := e.continuous.measurable
  have hprob : IsProbabilityMeasure (originalPhysicalAxisPortLaw R x) :=
    Measure.isProbabilityMeasure_map he.aemeasurable
  have hd : ∀ᵐ v ∂originalPhysicalAxisPortLaw R x, dist (e x) v ≤ 1 := by
    apply (ae_map_iff he.aemeasurable (measurableSet_le
      (measurable_const.dist measurable_id) measurable_const)).2
    filter_upwards [originalAxisPortProbabilityMeasure_ae_euclidean_deviation_le_one hx] with v hv
    change dist (e x) (e v) ≤ 1
    rw [dist_comm, dist_eq_norm, ← map_sub]
    exact hv
  have hb : ∀ᵐ v ∂originalPhysicalAxisPortLaw R x, dist (e x) v^2 ≤ (1 : ℝ) :=
    hd.mono (fun v hv ↦ by nlinarith [dist_nonneg (x := e x) (y := v)])
  have hI : Integrable (fun v ↦ dist (e x) v^2) (originalPhysicalAxisPortLaw R x) :=
    Integrable.of_bound ((measurable_const.dist measurable_id).pow_const 2).aestronglyMeasurable 1
      (hb.mono (fun v hv ↦ by
        change |dist (e x) v^2| ≤ 1
        rwa [abs_of_nonneg (sq_nonneg (dist (e x) v))]))
  refine ⟨hprob, hI, ?_⟩
  have h := integral_mono_ae hI (integrable_const (1 : ℝ)) hb
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using h

/-- The physical class sum uses the identical original endpoint labels. -/
theorem originalFiniteEndpointAtoms_physicalAxisPortClassMeasure {q n : ℕ}
    (points : Fin n → LegalMarkedPhysicalPoint q) (C : Set ℝ) (hC : MeasurableSet C) (R : ℝ) :
    (((volume.restrict (haarRootCube (Fin q) R)).withDensity
      (fun z ↦ ENNReal.ofReal (originalStageReflectedClassDensity (originalEuclideanMollifier q) R C
        (∑ i, Measure.dirac (points i)) z))).map (EuclideanSpace.equiv (Fin q) ℝ).symm) =
      ∑ i, if (points i).2 ∈ C then originalPhysicalAxisPortLaw R (points i).1 else 0 := by
  rw [originalFiniteEndpointAtoms_axisPortClassMeasure points C hC R,
    Measure.map_finset_sum' (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rfl
  · exact Measure.map_zero _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The genuine finite original port arrays give both full physical endpoint
families and all Borel class laws on one actual scene event. The arrays, probability
laws and their Euclidean deviation bounds are produced internally. -/
theorem ae_exists_originalPhysicalAxisStagePortFamilies
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (∃ n : ℕ, ∃ points : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker),
        (originalPathSourcePortPlan S w R ell scene :
          Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).fst = ∑ i, Measure.dirac (points i) ∧
        (∀ i, IsProbabilityMeasure (originalPhysicalAxisPortLaw R (points i).1)) ∧
        (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (points i).1) v^2)
          (originalPhysicalAxisPortLaw R (points i).1) ∧
          (∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (points i).1) v^2
            ∂originalPhysicalAxisPortLaw R (points i).1) ≤ 1) ∧
        ∀ C : Set ℝ, MeasurableSet C →
          (((volume.restrict (haarRootCube _ R)).withDensity
            (fun z ↦ ENNReal.ofReal (originalStageSourcePortDensity S w R ell
              (originalEuclideanMollifier _) C scene z))).map (EuclideanSpace.equiv _ ℝ).symm) =
            ∑ i, if (points i).2 ∈ C then originalPhysicalAxisPortLaw R (points i).1 else 0) ∧
      (∃ n : ℕ, ∃ points : Fin n → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker),
        (originalPathTargetPortPlan S w R ell scene :
          Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).snd = ∑ i, Measure.dirac (points i) ∧
        (∀ i, IsProbabilityMeasure (originalPhysicalAxisPortLaw R (points i).1)) ∧
        (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (points i).1) v^2)
          (originalPhysicalAxisPortLaw R (points i).1) ∧
          (∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (points i).1) v^2
            ∂originalPhysicalAxisPortLaw R (points i).1) ≤ 1) ∧
        ∀ C : Set ℝ, MeasurableSet C →
          (((volume.restrict (haarRootCube _ R)).withDensity
            (fun z ↦ ENNReal.ofReal (originalStageTargetPortDensity S w R ell
              (originalEuclideanMollifier _) C scene z))).map (EuclideanSpace.equiv _ ℝ).symm) =
            ∑ i, if (points i).2 ∈ C then originalPhysicalAxisPortLaw R (points i).1 else 0) := by
  filter_upwards [D.ae_exists_originalAxisStagePortArrays hF hw Q (by linarith) hR]
    with scene hscene
  obtain ⟨⟨ns, xs, hs, hxs⟩, ⟨nt, xt, ht, hxt⟩⟩ := hscene
  have hRone : 1 ≤ R := by linarith
  refine ⟨⟨ns, xs, hs, fun i ↦ (originalPhysicalAxisPortLaw_spec hRone (hxs i)).1,
    fun i ↦ (originalPhysicalAxisPortLaw_spec hRone (hxs i)).2, ?_⟩,
    ⟨nt, xt, ht, fun i ↦ (originalPhysicalAxisPortLaw_spec hRone (hxt i)).1,
    fun i ↦ (originalPhysicalAxisPortLaw_spec hRone (hxt i)).2, ?_⟩⟩
  · intro C hC
    change (((volume.restrict _).withDensity (fun z ↦ ENNReal.ofReal
      (originalStageReflectedClassDensity _ R C _ z))).map _) = _
    rw [hs]
    exact originalFiniteEndpointAtoms_physicalAxisPortClassMeasure xs C hC R
  · intro C hC
    change (((volume.restrict _).withDensity (fun z ↦ ENNReal.ofReal
      (originalStageReflectedClassDensity _ R C _ z))).map _) = _
    rw [ht]
    exact originalFiniteEndpointAtoms_physicalAxisPortClassMeasure xt C hC R
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
