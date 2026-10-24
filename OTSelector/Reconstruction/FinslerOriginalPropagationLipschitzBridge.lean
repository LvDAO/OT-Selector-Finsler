import OTSelector.Reconstruction.FinslerOriginalFrozenDominationInstantiation

/-!
# Propagation Lipschitz bridge, scaled frozen domination data, and the hprob frozen inputs

This module closes the remaining gap of
FinslerOriginalFrozenDominationInstantiation and connects the frozen data bundle
FrozenPressureDominationData to the hprob lane.

* lipschitzWith_ambient_of_finslerMetric: the propagation Lipschitz conversion.
  The physical form (LipschitzWith read in F.metricSpace) converts to the ambient
  pseudo-metric form using metricSpace_edist and hdist together with the
  finiteness of the Finsler length distance.
* frozenCoreCostFamilyWithScale and finslerSupportedPressureFamilyWithScale: the
  concrete frozen core cost family and the physical supported pressure family at
  a sample-dependent scale; the scale of the final assembly is the iid exponent
  ((n + 1 : R) ^ (2 / (finrank R E - 1))).
* frozenCore_div_le_finslerSupportedPressure_add_of_finslerMetric: the frozen
  domination field at the physical pressure with the physical Lipschitz
  hypothesis (the converted hypothesis).
* frozenDominated_withScale_of_geometricLane and
  frozenIntegrable_withScale_of_wholePathDomination: the two frozen fields.
* frozenPressureDominationData_withScale_of_geometricAndWholePath: the frozen
  data bundle end-to-end at the physical pressure.
* hprobFrozenInputs_of_geometricAndWholePath: the two hypothesis families
  (hfrozen_int, hfrozen_dom) of the hprob consumer
  physical_finsler_probability_lower_of_frozen_mean_lower, reduced to the
  whole-path data and the finite-domination geometric lane.

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

/-! ## Propagation Lipschitz conversion -/

section PropagationLipschitz

variable [PseudoMetricSpace M]

/-- **The propagation Lipschitz bridge (physical form to ambient form).**

If the ambient distance is the Finsler length, then a function which is
one-Lipschitz for the physical Finsler metric F.metricSpace is one-Lipschitz for
the ambient pseudo-metric.  The proof rewrites the physical extended distance of
the hypothesis with metricSpace_edist and the ambient extended distance of the
goal with edist_dist and hdist; finiteness of the Finsler length distance turns
ofReal ((lengthEDist x y).toReal) back into lengthEDist x y. -/
theorem lipschitzWith_ambient_of_finslerMetric
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {φ : M → ℝ}
    (hφ : let _instPropagationLipschitz : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ) :
    LipschitzWith 1 φ := by
  intro x y
  have h := hφ x y
  have hlt : F.lengthEDist x y ≠ ⊤ := (F.lengthEDist_lt_top x y).ne
  simpa only [OTSelector.Geometry.ContinuousFinslerNorm.metricSpace_edist,
    edist_dist, hdist x y, ENNReal.ofReal_toReal hlt] using h

end PropagationLipschitz

/-! ## Concrete families at a sample-dependent scale -/

/-- The normalised masked frozen core cost, at a sample-dependent scale.  This is
the concrete frozen core cost family of the finite-domination lane; the constant
scale case is frozenCoreCostFamily. -/
noncomputable def frozenCoreCostFamilyWithScale
    (scale : ℕ → ℝ) {Ω : ℕ → Type*} {N : ℕ → ℕ}
    (C : OriginalPopulationCoefficientCore Seed a κ lambda η₀ η₁ δ) (ε : ℝ)
    (X Y : ∀ n, Ω n → Fin (N n) → M)
    (z₀ : ∀ n, Ω n → Fin (N n) → Fin (N n) → Z)
    (h : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℝ)
    (Q : ∀ n, Ω n → Set (Fin (N n) × Fin (N n)))
    (Pmat : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℝ) :
    (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ :=
  fun f t n s =>
    fractionalAssignmentCost
      (maskedFrozenCost (Q n s)
        (frozenCoreMatrix C ε (z₀ n s) (X n s) (Y n s) (scale n) t (h n s)))
      (Pmat n s) / (N n : ℝ)

/-- The physical Finsler supported pressure at a sample-dependent scale.  This is
the empirical pressure family of the frozen data bundle for the hprob lane: the
pressure is the supported distance pressure at the scale of the sample. -/
noncomputable def finslerSupportedPressureFamilyWithScale
    (scale : ℕ → ℝ) (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K) (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K)
    (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K) {Ω : ℕ → Type*} {N : ℕ → ℕ}
    (X Y : ∀ n, Ω n → Fin (N n) → M) (φ : M → ℝ) :
    (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ :=
  fun f t n s =>
    finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ (scale n) f t

/-! ## The frozen domination field with the converted Lipschitz hypothesis -/

section Deterministic

variable [PseudoMetricSpace M]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenCoreMetric : MetricSpace M := F.metricSpace;
    LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **The frozen core domination field at the physical pressure, from the
physical propagation Lipschitz hypothesis.**

This is frozenCore_div_le_finslerSupportedPressure_add with the propagation
Lipschitz hypothesis in the physical Finsler form; the ambient form needed by the
finite-domination lane is produced by lipschitzWith_ambient_of_finslerMetric. -/
theorem frozenCore_div_le_finslerSupportedPressure_add_of_finslerMetric
    {C : OriginalPopulationCoefficientCore Seed a κ lambda η₀ η₁ δ} {ε : ℝ}
    (D : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    (μ ν : ProbabilityMeasure M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (hn : 0 < n) {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : let _instPropagationLipschitz : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    {k t probeError : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)} {Pmat : Matrix (Fin n) (Fin n) ℝ}
    (f : (K × K) →ᵇ ℝ)
    (hP : OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j => k * distanceSlackEdgeCost X Y φ i j)
        (carrierProbeMatrix μ ν K hK hμ hν X Y f) t) Pmat)
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C D z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q →
      |carrierProbeMatrix μ ν K hK hμ hν X Y f i j - h i j| ≤ probeError)
    (hprobeError_le : probeError ≤ (‖f‖₊ : ℝ)) :
    fractionalAssignmentCost (maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h))
        Pmat / (n : ℝ) ≤
      finslerSupportedPressure F μ ν K hK hμ hν X Y φ k f t + |t| * (‖f‖₊ : ℝ) := by
  have hφL : LipschitzWith 1 φ := lipschitzWith_ambient_of_finslerMetric hdist hφ
  exact frozenCore_div_le_finslerSupportedPressure_add (F := F) (u := u) (C := C)
    (ε := ε) (D := D) (hε := hε) (hε1 := hε1) (hdist := hdist) (μ := μ) (ν := ν)
    (hK := hK) (hμ := hμ) (hν := hν) (hn := hn) (X := X) (Y := Y) (φ := φ)
    (hφu := hφu) (hφ := hφL) (k := k) (t := t) (probeError := probeError)
    (hk := hk) (z₀ := z₀) (h := h) (Q := Q) (Pmat := Pmat) (f := f)
    (hF := hF) (hcomplete := hcomplete) (hu := hu) (ha := ha) (hinj := hinj)
    hP hgeom hgh hprobeError_le

end Deterministic

/-! ## End-to-end frozen data at the physical pressure -/

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
  (φ : M → ℝ) (hφu : ∀ x, φ x = u x)
  (hφ : let _instPropagationLipschitz : MetricSpace M := F.metricSpace
    LipschitzWith 1 φ)
  (scale : ℕ → ℝ) (hscale : ∀ n, 0 ≤ scale n)
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
      (fun i j => scale n * distanceSlackEdgeCost (X n s) (Y n s) φ i j)
      (carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f) t) (Pmat n s))
  (hgeom : ∀ n, ∀ᵐ s ∂Pm n,
    ∀ i j, (i, j) ∈ Q n s → FrozenCoreEdgeGeometry C D (z₀ n s) (X n s) (Y n s) i j)
  (hgh : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂Pm n,
    ∀ i j, (i, j) ∈ Q n s →
      |carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f i j - h n s i j| ≤
        probeError f)
  (hprobeError_le : ∀ (f : (K × K) →ᵇ ℝ), probeError f ≤ (‖f‖₊ : ℝ))
  {traffic : ∀ n, Ω n → ℝ} {phaseBad : ∀ n, Set (Ω n)} {CBs CLs B0s : ℕ → ℝ}
  {Aamp Camp : ((K × K) →ᵇ ℝ) → ℝ → ℝ}
  (hdata : ∀ n, CommonScaleWholePathPressureData (Pm n) (traffic n) (phaseBad n)
    (CBs n) (CLs n) (B0s n))
  (htraf : ∀ n, Measurable (traffic n))
  (hbad : ∀ n, MeasurableSet (phaseBad n))
  (hbadint : ∀ n, Integrable ((phaseBad n).indicator (traffic n)) (Pm n))
  (hmeas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
    Measurable (frozenCoreCostFamilyWithScale scale C ε X Y z₀ h Q Pmat f t n))
  (hCamp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), 0 ≤ Camp f t)
  (hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n),
    |frozenCoreCostFamilyWithScale scale C ε X Y z₀ h Q Pmat f t n s| ≤
      Aamp f t + Camp f t * traffic n s)

include hF hcomplete hu ha hinj D hε hε1 hdist hφu hφ hscale hN hPmfin
  probeError hPopt hgeom hgh hprobeError_le traffic phaseBad CBs CLs B0s Aamp Camp
  hdata htraf hbad hbadint hmeas hCamp hbound

/-- **The frozen dominated field at the physical pressure and a
sample-dependent scale.**

The frozen core cost is at most the physical supported pressure at the sample
scale plus the probe constant; this is the frozen_dominated field of the hprob
lane, derived from the geometric finite-domination lane with the physical
propagation Lipschitz hypothesis converted to the ambient form. -/
theorem frozenDominated_withScale_of_geometricLane :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂Pm n,
      frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale C ε X Y z₀ h
          Q Pmat f t n s ≤
        finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ (scale n) f t +
          |t| * (‖f‖₊ : ℝ) := by
  have hφL : LipschitzWith 1 φ := lipschitzWith_ambient_of_finslerMetric hdist hφ
  intro f t n
  filter_upwards [hPopt f t n, hgeom n, hgh f t n] with s hPs hgs hhs
  show fractionalAssignmentCost
      (maskedFrozenCost (Q n s)
        (frozenCoreMatrix C ε (z₀ n s) (X n s) (Y n s) (scale n) t (h n s)))
      (Pmat n s) / (N n : ℝ) ≤
    finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ (scale n) f t +
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
    (hφu := hφu) (hφ := hφL) (k := scale n) (t := t) (probeError := probeError f)
    (Bg := (‖f‖₊ : ℝ)) (hk := hscale n) (z₀ := z₀ n s) (h := h n s)
    (g := carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f) (Q := Q n s)
    (Pmat := Pmat n s)
    hF hcomplete hu ha hinj D hε hε1 hdist (hN n) hPs hgs hhs hg_bound
    (hprobeError_le f)
  have hfins : finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ
        (scale n) f t =
      perturbedAssignmentValue
        (fun i j => scale n * distanceSlackEdgeCost (X n s) (Y n s) φ i j)
        (fun i j => f (supportProjection μ K hK hμ (X n s i),
          supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := by
    rw [finslerSupportedPressure_eq_supportedDistancePressure]
    have hbody : @OTSelector.Pressure.supportedDistancePressure M F.metricSpace
        inferInstance μ ν K hK hμ hν (N n) (X n s) (Y n s) φ (scale n) f t =
        perturbedAssignmentValue (fun i j => scale n * @OTSelector.distanceSlackEdgeCost
          (N n) M (OTSelector.Geometry.ContinuousFinslerNorm.metricSpace (F := F)).toPseudoMetricSpace
          (X n s) (Y n s) φ i j)
          (fun i j => f (supportProjection μ K hK hμ (X n s i),
            supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := rfl
    rw [hbody]
    rw [distanceSlackEdgeCost_finsler_eq (F := F) (hdist := hdist) (k := scale n)]
  rw [hfins]
  exact hcore

/-- **The frozen integrability field from the whole-path data.** -/
theorem frozenIntegrable_withScale_of_wholePathDomination :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale
        C ε X Y z₀ h Q Pmat f t n) (Pm n) := by
  intro f t n
  exact frozenIntegrable_of_wholePathDomination Pm hPmfin
    (frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale C ε X Y z₀ h
      Q Pmat) hdata htraf hbad hbadint hmeas hCamp hbound f t n

/-- **The frozen data bundle at the physical pressure and a sample-dependent
scale.**  Both fields are unconditional relative to the named whole-path data and
the finite-domination geometric lane; the propagation Lipschitz hypothesis is
taken in the physical Finsler form. -/
theorem frozenPressureDominationData_withScale_of_geometricAndWholePath :
    FrozenPressureDominationData Pm
      (frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale C ε X Y z₀ h
        Q Pmat)
      (finslerSupportedPressureFamilyWithScale (F := F) scale μ ν K hK hμ hν X Y φ) := by
  refine ⟨?_, ?_⟩
  ·
    -- frozen dominated field
    have hφL : LipschitzWith 1 φ := lipschitzWith_ambient_of_finslerMetric hdist hφ
    intro f t n
    filter_upwards [hPopt f t n, hgeom n, hgh f t n] with s hPs hgs hhs
    show fractionalAssignmentCost
        (maskedFrozenCost (Q n s)
          (frozenCoreMatrix C ε (z₀ n s) (X n s) (Y n s) (scale n) t (h n s)))
        (Pmat n s) / (N n : ℝ) ≤
      finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ (scale n) f t +
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
      (hφu := hφu) (hφ := hφL) (k := scale n) (t := t)
      (probeError := probeError f) (Bg := (‖f‖₊ : ℝ)) (hk := hscale n)
      (z₀ := z₀ n s) (h := h n s)
      (g := carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f) (Q := Q n s)
      (Pmat := Pmat n s)
      hF hcomplete hu ha hinj D hε hε1 hdist (hN n) hPs hgs hhs hg_bound
      (hprobeError_le f)
    have hfins : finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ
          (scale n) f t =
        perturbedAssignmentValue
          (fun i j => scale n * distanceSlackEdgeCost (X n s) (Y n s) φ i j)
          (fun i j => f (supportProjection μ K hK hμ (X n s i),
            supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := by
      rw [finslerSupportedPressure_eq_supportedDistancePressure]
      have hbody : @OTSelector.Pressure.supportedDistancePressure M F.metricSpace
          inferInstance μ ν K hK hμ hν (N n) (X n s) (Y n s) φ (scale n) f t =
          perturbedAssignmentValue (fun i j => scale n * @OTSelector.distanceSlackEdgeCost
            (N n) M (OTSelector.Geometry.ContinuousFinslerNorm.metricSpace (F := F)).toPseudoMetricSpace
            (X n s) (Y n s) φ i j)
            (fun i j => f (supportProjection μ K hK hμ (X n s i),
              supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := rfl
      rw [hbody]
      rw [distanceSlackEdgeCost_finsler_eq (F := F) (hdist := hdist) (k := scale n)]
    rw [hfins]
    exact hcore
  ·
    -- frozen integrability field
    intro f t n
    exact frozenIntegrable_of_wholePathDomination Pm hPmfin
      (frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale C ε X Y z₀ h
        Q Pmat) hdata htraf hbad hbadint hmeas hCamp hbound f t n

/-- **The two frozen inputs of the hprob lane, reduced to the whole-path data.**

The conjunction is exactly the pair (hfrozen_int, hfrozen_dom) of the hprob
consumer physical_finsler_probability_lower_of_frozen_mean_lower, for the
concrete frozen core cost family at the sample scale: the pressure expression in
the domination half is the consumer's finslerSupportedPressure expression with
the iid scale, and the integrability half is its Integrable input.  Hence the
frozen input of hprob is reduced to the whole-path data, the finite-domination
geometric lane, and the physical propagation Lipschitz hypothesis. -/
theorem hprobFrozenInputs_of_geometricAndWholePath :
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale
        C ε X Y z₀ h Q Pmat f t n) (Pm n)) ∧
    (∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂Pm n,
      frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale C ε X Y z₀ h
          Q Pmat f t n s ≤
        finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ (scale n) f t +
          |t| * (‖f‖₊ : ℝ)) := by
  refine ⟨?_, ?_⟩
  ·
    -- frozen integrability input
    intro f t n
    exact frozenIntegrable_of_wholePathDomination Pm hPmfin
      (frozenCoreCostFamilyWithScale (F := F) (u := u) (K := K) scale C ε X Y z₀ h
        Q Pmat) hdata htraf hbad hbadint hmeas hCamp hbound f t n
  ·
    -- frozen dominated input
    have hφL : LipschitzWith 1 φ := lipschitzWith_ambient_of_finslerMetric hdist hφ
    intro f t n
    filter_upwards [hPopt f t n, hgeom n, hgh f t n] with s hPs hgs hhs
    show fractionalAssignmentCost
        (maskedFrozenCost (Q n s)
          (frozenCoreMatrix C ε (z₀ n s) (X n s) (Y n s) (scale n) t (h n s)))
        (Pmat n s) / (N n : ℝ) ≤
      finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ (scale n) f t +
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
      (hφu := hφu) (hφ := hφL) (k := scale n) (t := t)
      (probeError := probeError f) (Bg := (‖f‖₊ : ℝ)) (hk := hscale n)
      (z₀ := z₀ n s) (h := h n s)
      (g := carrierProbeMatrix μ ν K hK hμ hν (X n s) (Y n s) f) (Q := Q n s)
      (Pmat := Pmat n s)
      hF hcomplete hu ha hinj D hε hε1 hdist (hN n) hPs hgs hhs hg_bound
      (hprobeError_le f)
    have hfins : finslerSupportedPressure F μ ν K hK hμ hν (X n s) (Y n s) φ
          (scale n) f t =
        perturbedAssignmentValue
          (fun i j => scale n * distanceSlackEdgeCost (X n s) (Y n s) φ i j)
          (fun i j => f (supportProjection μ K hK hμ (X n s i),
            supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := by
      rw [finslerSupportedPressure_eq_supportedDistancePressure]
      have hbody : @OTSelector.Pressure.supportedDistancePressure M F.metricSpace
          inferInstance μ ν K hK hμ hν (N n) (X n s) (Y n s) φ (scale n) f t =
          perturbedAssignmentValue (fun i j => scale n * @OTSelector.distanceSlackEdgeCost
            (N n) M (OTSelector.Geometry.ContinuousFinslerNorm.metricSpace (F := F)).toPseudoMetricSpace
            (X n s) (Y n s) φ i j)
            (fun i j => f (supportProjection μ K hK hμ (X n s i),
              supportProjection ν K hK hν (Y n s j))) t / (N n : ℝ) := rfl
      rw [hbody]
      rw [distanceSlackEdgeCost_finsler_eq (F := F) (hdist := hdist) (k := scale n)]
    rw [hfins]
    exact hcore

end Data

end OTSelector.Reconstruction
