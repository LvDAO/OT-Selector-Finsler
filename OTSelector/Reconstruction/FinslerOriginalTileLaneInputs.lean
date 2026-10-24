/-
# Tile-lane inputs of the pressure-lower readout

This module discharges the remaining named lane inputs of the pressure-lower tile
lane (`FinslerOriginalPressureLowerReadout`) for the actual lane:

* the atlas readout family is instantiated at `atlasPiecewiseRoot`, so the gluing
  equation `hgt` holds by `rfl`;
* the masked-entry exchangeability `hExch` is discharged to the concrete
  pair-functional instance of `FinslerOriginalTileMaskedExchangeabilityInstance`;
* the plan-residual vanishing `hresv` is discharged to the concrete scale-bound
  instance of `FinslerOriginalTileEntryBound`;
* the remaining fields (population covering identity `hdecomp`, the entrywise and
  pair-sum integrability, and the analytic Palm/normalization inputs) are bundled
  explicitly in `TileLaneInputs` and documented below.

The final theorem `pressureLower_eq_sceneReadout_of_tileLane` states that
`pressureLower_eq_sceneReadout_of_palmSampleLaw` holds with these bundled lane
inputs: given the bundled lane and the remaining Palm/normalization inputs, the
empirical mean limit `pressureLower` equals the readout `Psi`.

## Exact remaining inputs

* `hintEntry`, `hintCost`, `hintRes`: entrywise and pair-sum integrability of the
  concrete tile cost matrix (measurability of the probe base is not part of the
  lane data, so these stay as explicit integrability fields);
* `hdecomp`: the population cell-refinement covering identity (sum over seed
  pieces of the weighted atlas integral equals the sum over retained tiles of the
  tile population value); this is the tiling-completeness input;
* the pair functionality of the probe (`hprobePair`) and the measurability and
  boundedness of the concrete pair kernel (`hPsi`, `hPsib`), used to discharge
  `hExch`;
* the scale normalization (`hscale0`, `hscale`), the uniform physical bound
  (`hphys`) and the probe normalization (`hprobeB`) used to discharge `hresv`;
* the optimal thin-plan structure (`hAnonneg`, `hrow`, `hcol`, `hopt`).
-/
import OTSelector.Reconstruction.FinslerOriginalPressureLowerReadout
import OTSelector.Reconstruction.FinslerOriginalTileEntryBound
import OTSelector.Reconstruction.FinslerOriginalTileMaskedExchangeabilityInstance

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

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  [MeasurableSpace.CountablySeparated (ℚ → M)]

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

structure TileLaneInputs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    {F : ContinuousFinslerNorm E M} {u : M → ℝ}
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda]
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
    {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
    {ε : ℝ} {T : D.TaylorTiles ε}
    {K : Set M} {q : ℝ} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (sample : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (scale : ℕ → ℝ)
    (G : ℕ → (ℚ → M) → ℝ) : Type _ where
  g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ
  hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G
  Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
  hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n)
  hExch : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
  hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n)
  hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n)
  hresv : T.TilePlanResidualVanishing sample Assign X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')
  hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c)


/-- **Bundled tile-lane inputs with the structural fields discharged.**

The atlas readout family is instantiated at `atlasPiecewiseRoot` (so `hgt` is
`rfl`), the masked-entry exchangeability is the concrete pair-functional
instance, and the plan-residual vanishing is the concrete scale-bound instance.
The population covering identity, the entrywise and pair-sum integrability and
the probe pair functionality remain explicit inputs (documented in the module
docstring). -/
def tileLaneInputs_of_laneData    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintCost : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c s i j)
        (sample n))
    {μ ν : ℕ → Measure M} [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (j : Fin (n + 1)), Measurable (Y n j))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (sample n).map (X n i) = μ n)
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (sample n).map (Y n j) = ν n)
    (hpair : ∀ (n : ℕ) (i j : Fin (n + 1)), IndepFun (X n i) (Y n j) (sample n))
    (probeKernel : ((K × K) →ᵇ ℝ) → ℝ → ℕ → T.Index → M × M → ℝ)
    (hprobePair : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)),
      normalizedProbe (K := K) base t n s c i j = probeKernel f t n c (X n i s, Y n j s))
    (hΨ : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Measurable (T.tilePairKernel c (scale n) t (probeKernel f t n c)))
    (hΨb : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      ∃ Cb : ℝ, ∀ p : M × M, |T.tilePairKernel c (scale n) t (probeKernel f t n c) p| ≤ Cb)
    (S B Pc : ℝ) (hB : 0 ≤ B) (hε0 : 0 ≤ 1 - 2 * ε)
    (hC₀ : 0 ≤ (1 - 2 * ε) * S * B + Pc)
    (hscale0 : ∀ n, 0 ≤ scale n)
    (hscale : ∀ n, scale n ≤ S / ((n + 1 : ℕ) : ℝ))
    (hphys : ∀ (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1)),
      (T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s) ≤ B)
    (hprobeB : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n)
      (i j : Fin (n + 1)),
      t * normalizedProbe (K := K) base t n s c i j ≤ Pc / ((n + 1 : ℕ) : ℝ))
    (hAnonneg : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)), 0 ≤ Assign n s i j)
    (hrow : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)), ∑ j, Assign n s i j = 1)
    (hcol : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)), ∑ i, Assign n s i j = 1)
    (hopt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index) (s : Ω n),
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')) n c s) (Assign n s) ≤
      fractionalAssignmentCost (T.tileCostMatrix f t X Y scale ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')) n c s)
        (fun _ _ ↦ 1 / ((n + 1 : ℕ) : ℝ)))
    
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    :
    TileLaneInputs (P := P) (a := a) (κ := κ) (lambda := lambda) (D := D) (ε := ε) (T := T) (K := K) (q := q) (base := base) (sample := sample) (X := X) (Y := Y) (scale := scale) (G := G) := by
  refine
    { g := fun _ _ ↦ atlasPiecewiseRoot P a κ lambda G
      hgt := fun _ _ ↦ rfl
      Assign := Assign
      hintEntry := hintEntry
      hExch := ?_
      hintCost := hintCost
      hintRes := hintRes
      hresv := ?_
      hdecomp := hdecomp }
  · exact maskedEntryExchangeability_tileCostMatrix_forall (T := T) sample X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')
      hX hY hXlaw hYlaw hpair probeKernel hprobePair hΨ hΨb
  · exact tilePlanResidualVanishing_of_scaleBounds (T := T) sample Assign X Y scale
      (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c')
      S B Pc hB hε0 hC₀ hscale0 hscale hphys hprobeB hAnonneg hrow hcol hopt
      hintCost hintRes

/-- **The tile-lane readout identification with the bundled lane inputs.**

With the tile-lane inputs bundled in `TileLaneInputs` (atlas readout family, thin
plan, masked exchangeability, integrability, plan-residual vanishing and
population covering identity), the remaining Palm sample-law/integrability inputs
of the pressure-lower tile lane, and the readout identification
`frozenPressureLower = Ψ`, the empirical mean-limit readout is identified with
`Ψ`. This is exactly `pressureLower_eq_sceneReadout_of_palmSampleLaw` with its
lane inputs discharged into the bundled structure. -/
theorem pressureLower_eq_sceneReadout_of_tileLane
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (lane : TileLaneInputs (P := P) (a := a) (κ := κ) (lambda := lambda)
      (D := D) (ε := ε) (T := T) (K := K) (q := q) (base := base)
      (sample := sample) (X := X) (Y := Y) (scale := scale) (G := G))
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
        atTop (𝓝 0))
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (fun s c' ↦ normalizedProbe (K := K) base t n s c')
        (lane.Assign n) (scale n) t c) (sample n))
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t ((fun (f : (K × K) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := K) base t n s c') f t n s)) (lane.Assign n s) /
          ((n + 1 : ℕ) : ℝ) ∂sample n) atTop
        (𝓝 (pressureLower f t)))
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda lane.g q = Ψ) :
    pressureLower = Ψ := by
  exact pressureLower_eq_sceneReadout_of_palmSampleLaw (T := T) sample G X Y scale
    base hBp hbase hintC hintP hintClip hPalm hclip lane.Assign lane.hintEntry
    lane.hExch lane.hintCost lane.hintRes lane.hresv lane.g hF hcomplete hu ha
    hinj hint lane.hgt lane.hdecomp pressureLower hlim Ψ hread

end PopulationLocalPressureCore.TaylorTiles
end OTSelector.Reconstruction
