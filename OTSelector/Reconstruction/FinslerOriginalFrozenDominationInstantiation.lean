import OTSelector.Reconstruction.FinslerOriginalFrozenDominationData
import OTSelector.Reconstruction.FinslerFrozenCoreDomination

/-!
# Instantiation of the frozen domination field at the physical Finsler pressure

The frozen data bundle FrozenPressureDominationData had its supported-pressure
domination field left explicit.  This module instantiates it for the concrete
frozen core family of the finite-domination lane:

* the frozen core cost family is the normalized masked frozen core cost
  fractionalAssignmentCost (maskedFrozenCost ...) / n;
* the empirical pressure is the physical Finsler supported pressure
  finslerSupportedPressure.

The instance identification is proven, not assumed:

1. finslerSupportedPressure_eq_supportedDistancePressure: the physical pressure is
   the supported distance pressure evaluated in the Finsler metric space (rfl);
2. distanceSlackEdgeCost_finsler_eq: once the ambient distance is the Finsler
   length, the ambient distance-slack cost matrix equals the physical one, using
   metricSpace_dist; this is the metric-instance bridge;
3. frozenCore_div_le_finslerSupportedPressure_add: the frozen core domination
   field, from frozenCore_div_le_pressure_add_of_probeBound (the geometric
   finite-domination lane) composed with the bridge above;
4. frozenPressureDominationData_of_geometricAndWholePath: the frozen data
   bundle, unconditional relative to the named whole-path data
   CommonScaleWholePathPressureData and to the finite-domination geometric
   inputs.

The probe matrix is the carrier probe matrix (supportProjection composition).
The propagation Lipschitz hypothesis is taken in the ambient pseudo-metric; the
physical Finsler form converts to it with metricSpace_dist and hdist.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators Manifold

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (modelWithCornersSelf ℝ E) (↑⊤) M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-! ## The instance identification -/

/-- The physical Finsler supported pressure is the supported distance pressure
evaluated in the Finsler metric space. -/
theorem finslerSupportedPressure_eq_supportedDistancePressure
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (X Y : Fin n → M) (φ : M → ℝ) (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    finslerSupportedPressure F μ ν K hK hμ hν X Y φ k f t =
      @OTSelector.Pressure.supportedDistancePressure M F.metricSpace inferInstance
        μ ν K hK hμ hν n X Y φ k f t := rfl

/-- **The metric-instance bridge for the distance-slack cost matrix.**

If the ambient distance is the Finsler length, the physical Finsler
distance-slack cost matrix (distances read in F.metricSpace) is the ambient
distance-slack cost matrix.  This is the identification needed to compare the
finite-domination lane (ambient pseudo-metric) with the physical pressure. -/
theorem distanceSlackEdgeCost_finsler_eq [PseudoMetricSpace M]
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {n : ℕ} (X Y : Fin n → M) (φ : M → ℝ) (k : ℝ) :
    (fun i j => k * @OTSelector.distanceSlackEdgeCost n M
        (OTSelector.Geometry.ContinuousFinslerNorm.metricSpace (F := F)).toPseudoMetricSpace
        X Y φ i j)
      = fun i j => k * OTSelector.distanceSlackEdgeCost X Y φ i j := by
  funext i j
  simp only [OTSelector.distanceSlackEdgeCost]
  rw [hdist (X i) (Y j)]
  congr 1

/-! ## The carrier probe matrix -/

/-- The carrier probe matrix of a bounded probe function: the probe evaluated at
the support projections of the source and target samples. -/
noncomputable def carrierProbeMatrix (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K) {n : ℕ} (X Y : Fin n → M)
    (f : (K × K) →ᵇ ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => f (supportProjection μ K hK hμ (X i),
    supportProjection ν K hK hν (Y j))

/-! ## The frozen domination field -/

section Deterministic

variable [PseudoMetricSpace M]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenCoreMetric : MetricSpace M := F.metricSpace;
    LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **The frozen core domination field at the physical Finsler pressure.**

If the fractional assignment is optimal for the tilted empirical problem with
the distance-slack base cost and the carrier probe, and the frozen matrix is
dominated edgewise by the tilted cost plus the probe constant (the geometric
finite-domination lane), then the normalized masked frozen core cost is at most
the physical supported pressure plus the probe slack. -/
theorem frozenCore_div_le_finslerSupportedPressure_add
    {C : OriginalPopulationCoefficientCore Seed a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    (μ ν : ProbabilityMeasure M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (hn : 0 < n) {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : LipschitzWith 1 φ) {k t probeError : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)} {Pmat : Matrix (Fin n) (Fin n) ℝ}
    (f : (K × K) →ᵇ ℝ)
    (hP : OptimalFractionalAssignment (perturbedEdgeCost
      (fun i j => k * distanceSlackEdgeCost X Y φ i j)
      (carrierProbeMatrix μ ν K hK hμ hν X Y f) t) Pmat)
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q →
      |carrierProbeMatrix μ ν K hK hμ hν X Y f i j - h i j| ≤ probeError)
    (hprobeError_le : probeError ≤ (‖f‖₊ : ℝ)) :
    fractionalAssignmentCost (maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h))
        Pmat / (n : ℝ) ≤
      finslerSupportedPressure F μ ν K hK hμ hν X Y φ k f t + |t| * (‖f‖₊ : ℝ) := by
  have hg_bound : ∀ i j,
      |carrierProbeMatrix μ ν K hK hμ hν X Y f i j| ≤ (‖f‖₊ : ℝ) := by
    intro i j
    have hnorm := f.norm_coe_le_norm
      (supportProjection μ K hK hμ (X i), supportProjection ν K hK hν (Y j))
    simpa only [carrierProbeMatrix, Real.norm_eq_abs, coe_nnnorm] using hnorm
  have hcore := frozenCore_div_le_pressure_add_of_probeBound (F := F) (u := u)
    (P := Seed) (a := a) (κ := κ) (lambda := lambda) (η₀ := η₀) (η₁ := η₁)
    (δ := δ) (C := C) (ε := ε) (n := n) (X := X) (Y := Y) (φ := φ)
    (hφu := hφu) (hφ := hφ) (k := k) (t := t) (probeError := probeError)
    (Bg := (‖f‖₊ : ℝ)) (hk := hk) (z₀ := z₀) (h := h)
    (g := carrierProbeMatrix μ ν K hK hμ hν X Y f) (Q := Q) (Pmat := Pmat)
    hF hcomplete hu ha hinj D hε hε1 hdist hn hP hgeom hgh hg_bound hprobeError_le
  have hfins : finslerSupportedPressure F μ ν K hK hμ hν X Y φ k f t =
      perturbedAssignmentValue (fun i j => k * distanceSlackEdgeCost X Y φ i j)
        (fun i j => f (supportProjection μ K hK hμ (X i),
          supportProjection ν K hK hν (Y j))) t / (n : ℝ) := by
    rw [finslerSupportedPressure_eq_supportedDistancePressure]
    have hbody : @OTSelector.Pressure.supportedDistancePressure M F.metricSpace
        inferInstance μ ν K hK hμ hν n X Y φ k f t =
        perturbedAssignmentValue (fun i j => k * @OTSelector.distanceSlackEdgeCost n M
          (OTSelector.Geometry.ContinuousFinslerNorm.metricSpace (F := F)).toPseudoMetricSpace
          X Y φ i j)
          (fun i j => f (supportProjection μ K hK hμ (X i),
            supportProjection ν K hK hν (Y j))) t / (n : ℝ) := rfl
    rw [hbody]
    rw [distanceSlackEdgeCost_finsler_eq (F := F) (hdist := hdist)]
  rw [hfins]
  exact hcore

end Deterministic


/-! ## The concrete frozen data instantiation -/

/-- The concrete frozen core cost family: the normalized masked frozen core cost
at each sample. -/
noncomputable def frozenCoreCostFamily
    {Ω : ℕ → Type*} {N : ℕ → ℕ}
    (C : OriginalPopulationCoefficientCore Seed a κ lambda η₀ η₁ δ) (ε : ℝ)
    (X Y : ∀ n, Ω n → Fin (N n) → M)
    (z₀ : ∀ n, Ω n → Fin (N n) → Fin (N n) → Z)
    (h : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (Q : ∀ n, Ω n → Set (Fin (N n) × Fin (N n)))
    (Pmat : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (k : ℝ) : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ :=
  fun f t n s =>
    fractionalAssignmentCost
      (maskedFrozenCost (Q n s)
        (frozenCoreMatrix C ε (z₀ n s) (X n s) (Y n s) k t (h n s)))
      (Pmat n s) / (N n : ℝ)

/-- The physical supported pressure family on the samples. -/
noncomputable def finslerSupportedPressureFamily (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K) {Ω : ℕ → Type*} {N : ℕ → ℕ}
    (X Y : ∀ n, Ω n → Fin (N n) → M) (φ : M → ℝ) (k : ℝ) :
    (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ :=
  fun f t n s => finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ k f t

section Data

variable [PseudoMetricSpace M]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenCoreMetric : MetricSpace M := F.metricSpace;
    LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
  {C : OriginalPopulationCoefficientCore Seed a κ lambda η₀ η₁ δ} {ε : ℝ}
  (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
  (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
  (μ ν : ProbabilityMeasure M) (hK : MeasurableSet K)
  (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
  (φ : M → ℝ) (hφu : ∀ x, φ x = u x) (hφ : LipschitzWith 1 φ)
  {k : ℝ} (hk : 0 ≤ k)
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (Pm : ∀ n, Measure (Ω n)) (hPmfin : ∀ n, IsFiniteMeasure (Pm n))
  {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
  (X Y : ∀ n, Ω n → Fin (N n) → M)
  (z₀ : ∀ n, Ω n → Fin (N n) → Fin (N n) → Z)
  (h : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℝ)
  (Q : ∀ n, Ω n → Set (Fin (N n) × Fin (N n)))
  (Pmat : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℝ)
  (probeError : ((K × K) →ᵇ ℝ) → ℝ)
  (hPopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂Pm n,
    OptimalFractionalAssignment (perturbedEdgeCost
      (fun i j => k * distanceSlackEdgeCost (X n s) (Y n s) φ i j)
      (carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f) t) (Pmat n s))
  (hgeom : ∀ n, ∀ᵐ s ∂Pm n,
    ∀ i j, (i, j) ∈ Q n s → FrozenCoreEdgeGeometry C D (z₀ n s) (X n s) (Y n s) i j)
  (hgh : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂Pm n,
    ∀ i j, (i, j) ∈ Q n s →
      |carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f i j -
        h n s i j| ≤ probeError f)
  (hprobeError_le : ∀ (f : (K × K) →ᵇ ℝ), probeError f ≤ (‖f‖₊ : ℝ))
  {traffic : ∀ n, Ω n → ℝ} {phaseBad : ∀ n, Set (Ω n)} {CBs CLs B0s : ℕ → ℝ}
  {Aamp Camp : ((K × K) →ᵇ ℝ) → ℝ → ℝ}
  (hdata : ∀ n, CommonScaleWholePathPressureData (Pm n) (traffic n) (phaseBad n)
    (CBs n) (CLs n) (B0s n))
  (htraf : ∀ n, Measurable (traffic n))
  (hbad : ∀ n, MeasurableSet (phaseBad n))
  (hbadint : ∀ n, Integrable ((phaseBad n).indicator (traffic n)) (Pm n))
  (hmeas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
    Measurable (frozenCoreCostFamily C ε X Y z₀ h Q Pmat k f t n))
  (hCamp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), 0 ≤ Camp f t)
  (hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n),
    |frozenCoreCostFamily C ε X Y z₀ h Q Pmat k f t n s| ≤
      Aamp f t + Camp f t * traffic n s)

include hF hcomplete hu ha hinj D hε hε1 hdist hφu hφ hk hN hPmfin
  probeError hPopt hgeom hgh hprobeError_le traffic phaseBad CBs CLs B0s Aamp Camp
  hdata htraf hbad hbadint hmeas hCamp hbound

/-- **The frozen data bundle instantiated unconditionally relative to the named
whole-path data.**  The supported-pressure domination field comes from the
geometric finite-domination lane; the frozen integrability field comes from the
whole-path second-moment data together with the amplitude plus linear traffic
domination. -/
theorem frozenPressureDominationData_of_geometricAndWholePath :
    FrozenPressureDominationData Pm
      (frozenCoreCostFamily (F := F) (u := u) (K := K) (C := C) (ε := ε)
      (X := X) (Y := Y) (z₀ := z₀) (h := h) (Q := Q) (Pmat := Pmat) (k := k))
      (finslerSupportedPressureFamily (F := F) μ ν K hK hμ hν X Y φ k) := by
  refine frozenPressureDominationData_of_wholePathDomination Pm hPmfin
    (frozenCoreCostFamily (F := F) (u := u) (K := K) (C := C) (ε := ε)
      (X := X) (Y := Y) (z₀ := z₀) (h := h) (Q := Q) (Pmat := Pmat) (k := k))
    (finslerSupportedPressureFamily (F := F) μ ν K hK hμ hν X Y φ k)
    hdata htraf hbad hbadint hmeas hCamp hbound ?_
  intro f t n
  filter_upwards [hPopt f t n, hgeom n, hgh f t n] with s hPs hgs hhs
  show fractionalAssignmentCost
      (maskedFrozenCost (Q n s)
        (frozenCoreMatrix C ε (z₀ n s) (X n s) (Y n s) k t (h n s)))
      (Pmat n s) / (N n : ℝ) ≤
    finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ k f t +
      |t| * (‖f‖₊ : ℝ)
  have hg_bound : ∀ i j,
      |carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f i j| ≤ (‖f‖₊ : ℝ) := by
    intro i j
    have hnorm := f.norm_coe_le_norm
      (supportProjection μ K hK hμ (X n s i), supportProjection ν K hK hν (Y n s j))
    simpa only [carrierProbeMatrix, Real.norm_eq_abs, coe_nnnorm] using hnorm
  have hcore := frozenCore_div_le_pressure_add_of_probeBound (F := F) (u := u)
    (P := Seed) (a := a) (κ := κ) (lambda := lambda) (η₀ := η₀) (η₁ := η₁)
    (δ := δ) (C := C) (ε := ε) (n := N n) (X := X n s) (Y := Y n s) (φ := φ)
    (hφu := hφu) (hφ := hφ) (k := k) (t := t) (probeError := probeError f)
    (Bg := (‖f‖₊ : ℝ)) (hk := hk) (z₀ := z₀ n s) (h := h n s)
    (g := carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f) (Q := Q n s)
    (Pmat := Pmat n s)
    hF hcomplete hu ha hinj D hε hε1 hdist (hN n) hPs hgs hhs hg_bound
    (hprobeError_le f)
  have hfins : finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ k f t =
      perturbedAssignmentValue
        (fun i j => k * distanceSlackEdgeCost (X n s) (Y n s) φ i j)
        (fun i j => f (supportProjection μ K hK hμ (X n s i),
          supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := by
    rw [finslerSupportedPressure_eq_supportedDistancePressure]
    have hbody : @OTSelector.Pressure.supportedDistancePressure M F.metricSpace
        inferInstance μ ν K hK hμ hν (N n) (X n s) (Y n s) φ k f t =
        perturbedAssignmentValue (fun i j => k * @OTSelector.distanceSlackEdgeCost
          (N n) M (OTSelector.Geometry.ContinuousFinslerNorm.metricSpace (F := F)).toPseudoMetricSpace
          (X n s) (Y n s) φ i j)
          (fun i j => f (supportProjection μ K hK hμ (X n s i),
            supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := rfl
    rw [hbody]
    rw [distanceSlackEdgeCost_finsler_eq (F := F) (hdist := hdist)]
  rw [hfins]
  exact hcore

end Data

end OTSelector.Reconstruction

end