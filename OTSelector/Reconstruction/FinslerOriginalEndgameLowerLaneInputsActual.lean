import OTSelector.Reconstruction.FinslerOriginalEndgameLowerFieldActual
import OTSelector.Reconstruction.FinslerOriginalFixedPairIdentificationClosed
import OTSelector.Reconstruction.FinslerOriginalTileLaneDischarge

/-!
# Reduced actual-lane lower endgame bundle

Reduces the named inputs of `endgameLowerFields_actual_lane`:

* the TilePalmSampleLaw bundle `hPalm` is ELIMINATED: at the concrete scene-cloud
  lane (`sample = sceneCloudSample`, `X = sceneCloudX pcloud`,
  `Y = sceneCloudY qcloud`, `scale = tileScale`) it is derived from
  `tilePalmSampleLaw_sceneCloud_of_rootedConvergence` (which itself uses
  `tileFixedPair_tendsto_of_rootedTileMeanConvergence`), so its only LLN input is
  the named `RootedTileMeanConvergence` hypothesis `hconv`;
* the generic lane binders `sample`, `X`, `Y`, `scale` are eliminated (fixed to
  the concrete scene-cloud lane); the generic pair/sample-measurability binders are
  replaced by their scene-cloud instantiations.

The clipping vanishing `hclip` is kept as an explicit binder: it is exactly the
conclusion of the repo lemma `tileFixedPairClippingCorrection_tendsto_zero` /
`tileFixedPairClippingCorrection_tendsto_zero_of_retainedEdge` at the scene-cloud
lane (the latter needs the retained-edge data hz₀, hp, hphys which this bundle does
not carry).  The Campbell decomposition `hdecomp` and the plan-residual fields are
kept as binders; they are obtained from the cell-refinement hypothesis via
`tileLaneInputs_of_cellRefinement` (that wiring is not performed here).

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
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


noncomputable def endgameLowerFields_actual_lane_reduced
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (pcloud qcloud : ∀ n, Fin (n + 1) → M)
    (G : ℕ → (ℚ → M) → ℝ)
    (hX : ∀ n i, Measurable ((sceneCloudX pcloud) n i)) (hY : ∀ n i, Measurable ((sceneCloudY qcloud) n i))
    (hXi : ∀ n, iIndepFun ((sceneCloudX pcloud) n) (sceneCloudSample n)) (hYi : ∀ n, iIndepFun ((sceneCloudY qcloud) n) (sceneCloudSample n))
    (hXlaw : ∀ n i, (sceneCloudSample n).map ((sceneCloudX pcloud) n i) =
      (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ n i, (sceneCloudSample n).map ((sceneCloudY qcloud) n i) =
      (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sceneCloudSample i ↦ (sceneCloudX pcloud) n i sceneCloudSample)
      (fun sceneCloudSample i ↦ (sceneCloudY qcloud) n i sceneCloudSample) (sceneCloudSample n))
    (base : ∀ n, Fin (n + 1) → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Fin (n + 1)) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale n c) (sceneCloudSample n))
    (hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t (sceneCloudX pcloud) (sceneCloudY qcloud)
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hintLin : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) (n : ℕ),
      Integrable (T.tileLinearIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sceneCloudSample n))
    (hclip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (Assign : ∀ n, Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sceneCloudSample n) (T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hintRes : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
            (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sceneCloudSample n))
    (hresv : T.TilePlanResidualVanishing sceneCloudSample Assign (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ (sceneCloudX pcloud) n i s) (fun s i ↦ (sceneCloudY qcloud) n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (Assign n) (tileScale n) t c) (sceneCloudSample n))
    (hgt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ)
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Fin (n + 1)) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) (tileScale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n) (sceneCloudSample n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sceneCloudSample n,
      ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Fin (n + 1)) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) (tileScale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n s) ≤
        finslerSupportedPressure F
          (physicalSourceProbability ωM dens₀) (physicalTargetProbability ωM dens₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ (sceneCloudX pcloud) n i s) (fun i ↦ (sceneCloudY qcloud) n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hconv : T.RootedTileMeanConvergence
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index) ↦
        T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c)
      sceneCloudSample (sceneCloudX pcloud) (sceneCloudY qcloud) tileScale
      (fun f t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
      (uniformTilePlan (fun n ↦ Fin (n + 1))))
    :
    EndgameLowerFields (Ω := fun n ↦ Fin (n + 1)) F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sceneCloudSample
      (sceneCloudX pcloud) (sceneCloudY qcloud) u := by
  have hPalm : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw (ε := ε) f t sceneCloudSample (sceneCloudX pcloud)
        (sceneCloudY qcloud) tileScale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c) :=
    fun f t c ↦ T.tilePalmSampleLaw_sceneCloud_of_rootedConvergence f t pcloud qcloud base
      hBp hbase (hintLin f t c) (fun n ↦ hintClip f t n c) (fun n ↦ hintC f t n c)
      (fun n ↦ hintP f t n c) (hclip f t c) G
      (fun n c' i j ↦ hintEntry f t n c' i j) (fun n c' ↦ hExch f t n c') hconv
  exact endgameLowerFields_actual_lane (Ω := fun n ↦ Fin (n + 1))
    (hdim := hdim) (ωM := ωM) (dens₀ := dens₀) (dens₁ := dens₁) (hA := hA) (hB := hB)
    (hμA := hμA) (hνB := hνB) (sample := sceneCloudSample) (G := G)
    (X := sceneCloudX pcloud) (Y := sceneCloudY qcloud)
    (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi) (hXlaw := hXlaw) (hYlaw := hYlaw)
    (hXY := hXY) (scale := tileScale) (base := base) (hBp := hBp) (hbase := hbase)
    (hintC := hintC) (hintP := hintP) (hintClip := hintClip) (hPalm := hPalm)
    (hclip := hclip) (Assign := Assign) (hintEntry := hintEntry) (hExch := hExch)
    (hintCost := hintCost) (hintRes := hintRes) (hresv := hresv) (g := g) (hF := hF)
    (hcomplete := hcomplete) (hu := hu) (ha := ha) (hinj := hinj) (hint := hint)
    (hgt := hgt) (hdecomp := hdecomp) (Ψ := Ψ) (hread := hread)
    (hfrozen_int := hfrozen_int) (hfrozen_dom := hfrozen_dom)

end OTSelector.Reconstruction
