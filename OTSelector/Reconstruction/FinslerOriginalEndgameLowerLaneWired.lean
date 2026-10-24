import OTSelector.Reconstruction.FinslerOriginalEndgameLowerLaneInputsActual
import OTSelector.Reconstruction.FinslerOriginalFrozenScaleIdentification
import OTSelector.Reconstruction.FinslerOriginalHprobMeanWiring
import OTSelector.Reconstruction.FinslerOriginalConcretePalmSampleLaw

/-!
# The endgame lower lane with the frozen inputs DERIVED

The reduced endgame lower bundle endgameLowerFields_actual_lane_reduced
(FinslerOriginalEndgameLowerLaneInputsActual) still consumes two frozen-input
binders: the family integrability hfrozen_int and the shifted frozen domination
hfrozen_dom.  This module removes both by deriving them from the per-edge
finite-domination geometric lane at the concrete scene-cloud/tile-scale
presentation:

* sceneCloud_frozenInputs_wired: the derived pair (family integrability and
  support bound) at tileScale, a direct specialization of
  hprobFrozenInputs_tileScale_of_geometricLane (FinslerOriginalFrozenScaleIdentification);

* endgameLowerFields_actual_lane_wired: the endgame lower lane bundle
  (EndgameLowerFields) with pressureLower = fun f t => Psi f t - |t| ||f|| and
  unit radius, whose hprob field is built from that pair through
  finalProbLowerData_of_rootedTileMeanIdentification and the named tile Campbell
  mean identification hId.  No frozen-input binder remains.

## Which pressure presentation the lane uses (the F12 determination)

The consumer physical_finsler_probability_lower_of_frozen_mean_lower
(FinslerOriginalIIDPressureLowerLocalization) expects the frozen domination in the
SHIFTED form frozenCost <= finslerSupportedPressure + |t| * ||f|| and the mean
lower bound at pressureLower + |t| * ||f||.  At the lane readout
pressureLower = Psi - |t| * ||f|| the mean condition is therefore
Psi - eps <= integral frozenCost, exactly the Campbell lower bound supplied by
hId; and the domination is the shifted form.  The geometric lane proves precisely
this shifted form: the |t| * ||f|| slack is produced by the probe/model mismatch
bound hgh (it is the B_t term of the frozen summand), not by any additional paper
input.  Hence the lane consumes the shifted presentation and the geometric lane
feeds it directly at tileScale.

By contrast the F12 unshifted frozen domination hbaredom
(FinslerOriginalFrozenLowerDomination) is the same inequality after cancelling
B_t between both sides of the frozen summand; it is STRONGER than what the
per-edge geometric lane yields (it would require the model probe to agree exactly
with the physical probe).  The endgame lane does not consume it, and the F12
theorem finalProbLowerData_of_frozen_domination produces the UNSHIFTED readout
frozenPressureLower, not the probe-shifted readout Psi - |t| ||f|| used here.
Therefore no F12 composition is needed for this bundle; an unshifted-readout
consumer would have to compose F12 with an explicit hbaredom paper input, which
is outside this lane.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open OTSelector.Reconstruction.PopulationLocalPressureCore.TaylorTiles

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {q : ℝ}

/-! ## 1. The derived frozen inputs at the scene-cloud tile scale -/

/-- **The endgame lane frozen inputs, derived.**  At the concrete scene-cloud
lane and the tile scale, the family integrability and the shifted frozen
domination are consequences of the per-edge finite-domination geometric lane:
the tile geometry hgeom, the probe mismatch hgh, the optimal assignment wiring
hPopt, the probe/assignment/frozen bounds hbase, hphys and the frozen cost
measurability hmeas.  No frozen-input binder remains. -/
theorem sceneCloud_frozenInputs_wired
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instEndgameLowerLaneWiredMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp Bphys : ℝ} (hBp : 0 ≤ Bp) (hBphys : 0 ≤ Bphys)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Fin (n + 1)) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c)
        ((sceneCloudX pcloud) n i s) ((sceneCloudY qcloud) n j s) ≤ Bphys)
    (Assign : ∀ n, Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hAssignDS : ∀ (n : ℕ) (s : Fin (n + 1)),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hmeas : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s : Fin (n + 1) ↦
        T.tileFrozenCost (fun s' i ↦ (sceneCloudX pcloud) n i s')
          (fun s' i ↦ (sceneCloudY qcloud) n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (Assign n) (tileScale n) t c s))
    (hPopt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sceneCloudSample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
          distanceSlackEdgeCost (fun i ↦ (sceneCloudX pcloud) n i s)
            (fun i ↦ (sceneCloudY qcloud) n i s) u i j)
        (carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) f) t)
        (Assign n s))
    (hgeom : ∀ (n : ℕ), ∀ᵐ s ∂sceneCloudSample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ (sceneCloudX pcloud) n i s)
          (fun i ↦ (sceneCloudY qcloud) n i s) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (fun i ↦ (sceneCloudX pcloud) n i s)
        (fun i ↦ (sceneCloudY qcloud) n i s) i j)
    (hgh : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sceneCloudSample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ (sceneCloudX pcloud) n i s)
          (fun i ↦ (sceneCloudY qcloud) n i s) c →
      |carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) f i j -
        normalizedProbe (K := A ∪ B) base t n s c i j| ≤ (‖f‖₊ : ℝ)) :
    (∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
        Integrable (hprobFrozenCostFamily (K := A ∪ B) T
          (sceneCloudX pcloud) (sceneCloudY qcloud) base Assign tileScale f t n)
          (sceneCloudSample n)) ∧
      FrozenSupportBound (T := T) (F := F) (μ := physicalSourceProbability ωM dens₀)
        (ν := physicalTargetProbability ωM dens₁) (K := A ∪ B)
        (hA.union hB).measurableSet
        (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy) u
        (sceneCloudX pcloud) (sceneCloudY qcloud) base Assign tileScale
        sceneCloudSample :=
  hprobFrozenInputs_tileScale_of_geometricLane (T := T) (F := F)
    (Ω := fun n ↦ Fin (n + 1))
    (μ := physicalSourceProbability ωM dens₀)
    (ν := physicalTargetProbability ωM dens₁) (K := A ∪ B)
    hF hcomplete hu ha hinj hε hε1 hdist (hA.union hB).measurableSet
    (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
    (sceneCloudX pcloud) (sceneCloudY qcloud) base Assign sceneCloudSample hdim
    hBp hBphys hbase hphys hAssignDS hmeas hPopt hgeom hgh

/-! ## 2. The wired endgame lower bundle -/

/-- **The endgame lower lane with no frozen-input binders.**

Same conclusion as endgameLowerFields_actual_lane_reduced, but the family
integrability and the shifted frozen domination are DERIVED from the geometric
lane (sceneCloud_frozenInputs_wired), the hprob field is produced by the named
tile Campbell mean identification hId through
finalProbLowerData_of_rootedTileMeanIdentification, and the readout is the
probe-shifted pressureLower = fun f t => Psi f t - |t| ||f|| with unit radius.

The residual inputs are exactly: the analytic core (ambient metric with hdist,
hF, hcomplete, hu, ha, hinj, eps-range), the physical population data, the
sampling law, the geometric lane data (hPopt, hgeom, hgh, hmeas, hbase, hphys,
hBp, hBphys, hAssignDS, hbase), and the hprob identification hId with its
readout identification hread. -/
noncomputable def endgameLowerFields_actual_lane_wired
    [PseudoMetricSpace M]
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (hX : ∀ n i, Measurable ((sceneCloudX pcloud) n i))
    (hY : ∀ n i, Measurable ((sceneCloudY qcloud) n i))
    (hXi : ∀ n, iIndepFun ((sceneCloudX pcloud) n) (sceneCloudSample n))
    (hYi : ∀ n, iIndepFun ((sceneCloudY qcloud) n) (sceneCloudSample n))
    (hXlaw : ∀ n i, (sceneCloudSample n).map ((sceneCloudX pcloud) n i) =
      (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ n i, (sceneCloudSample n).map ((sceneCloudY qcloud) n i) =
      (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun s i ↦ (sceneCloudX pcloud) n i s)
      (fun s i ↦ (sceneCloudY qcloud) n i s) (sceneCloudSample n))
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp Bphys : ℝ} (hBp : 0 ≤ Bp) (hBphys : 0 ≤ Bphys)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Fin (n + 1)) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c)
        ((sceneCloudX pcloud) n i s) ((sceneCloudY qcloud) n j s) ≤ Bphys)
    (Assign : ∀ n, Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hAssignDS : ∀ (n : ℕ) (s : Fin (n + 1)),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hmeas : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (fun s : Fin (n + 1) ↦
        T.tileFrozenCost (fun s' i ↦ (sceneCloudX pcloud) n i s')
          (fun s' i ↦ (sceneCloudY qcloud) n i s')
          (fun s' c' ↦ normalizedProbe (K := A ∪ B) base t n s' c')
          (Assign n) (tileScale n) t c s))
    (hPopt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sceneCloudSample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
          distanceSlackEdgeCost (fun i ↦ (sceneCloudX pcloud) n i s)
            (fun i ↦ (sceneCloudY qcloud) n i s) u i j)
        (carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) f) t)
        (Assign n s))
    (hgeom : ∀ (n : ℕ), ∀ᵐ s ∂sceneCloudSample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ (sceneCloudX pcloud) n i s)
          (fun i ↦ (sceneCloudY qcloud) n i s) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (fun i ↦ (sceneCloudX pcloud) n i s)
        (fun i ↦ (sceneCloudY qcloud) n i s) i j)
    (hgh : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∀ᵐ s ∂sceneCloudSample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ (sceneCloudX pcloud) n i s)
          (fun i ↦ (sceneCloudY qcloud) n i s) c →
      |carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) f i j -
        normalizedProbe (K := A ∪ B) base t n s c i j| ≤ (‖f‖₊ : ℝ))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instEndgameLowerLaneWiredMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hId : RootedTileCampbellMeanIdentification P a κ lambda g q sceneCloudSample
      (hprobFrozenCostFamily (K := A ∪ B) T
        (sceneCloudX pcloud) (sceneCloudY qcloud) base Assign tileScale) T.Index)
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    EndgameLowerFields F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) u := by
  obtain ⟨hfrozen_int, hfrozen_dom⟩ :=
    sceneCloud_frozenInputs_wired (T := T) (F := F) hF hcomplete hu ha hinj
      hε hε1 hdist hdim ωM dens₀ dens₁ hA hB hμA hνB pcloud qcloud base hBp
      hBphys hbase hphys Assign hAssignDS hmeas hPopt hgeom hgh
  exact endgameLowerFields_mk (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ))
    (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
    (finalProbLowerData_of_rootedTileMeanIdentification (T := T) hdim ωM dens₀
      dens₁ hA hB hμA hνB sceneCloudSample (sceneCloudX pcloud)
      (sceneCloudY qcloud) hX hY hXi hYi hXlaw hYlaw hXY (fun _ ↦ 1) tileScale
      base Assign hfrozen_int hfrozen_dom g hId Ψ hread hcomplete hu)

end OTSelector.Reconstruction
