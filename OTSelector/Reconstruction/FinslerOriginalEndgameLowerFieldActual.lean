import OTSelector.Reconstruction.FinslerOriginalEndgameLowerField
import OTSelector.Reconstruction.FinslerOriginalHprobWiring

/-!
# The actual-lane lower endgame bundle

Instantiates `EndgameLowerFields` for the actual lane end to end:

* `palmReadout_hprob_actual`: the hprob field at the probe-shifted scene Palm
  readout, obtained by transcribing the full hypothesis list of
  `finalProbLowerData_of_palmSampleReadout` (FinslerOriginalHprobWiring.lean).
* `endgameLowerFields_actual_lane`: the actual-lane lower bundle with
  `pressureLower = fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)`, `radius = fun _ ↦ 1` and
  `hradius = fun _ ↦ zero_lt_one` (since `FinalPositiveRadius radius ≡ ∀ f, 0 < radius f`).

Every hypothesis that the repo does not already prove stays an explicit binder:
nothing is silently assumed.

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
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]


theorem palmReadout_hprob_actual
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (sample n)) (hYi : ∀ n, iIndepFun (Y n) (sample n))
    (hXlaw : ∀ n i, (sample n).map (X n i) =
      (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ n i, (sample n).map (Y n i) =
      (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (sample n))
    (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample Assign X Y scale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (Assign n) (scale n) t c) (sample n))
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
      Integrable ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n) (sample n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n s) ≤
        finslerSupportedPressure F
          (physicalSourceProbability ωM dens₀) (physicalTargetProbability ωM dens₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    :
    FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) radius := by
  exact finalProbLowerData_of_palmSampleReadout (T := T) hdim ωM dens₀ dens₁ hA hB hμA hνB sample G X Y hX hY hXi hYi hXlaw hYlaw hXY radius scale base hBp hbase hintC hintP hintClip hPalm hclip Assign hintEntry hExch hintCost hintRes hresv g hF hcomplete hu ha hinj hint hgt hdecomp Ψ hread hfrozen_int hfrozen_dom

/-- **The actual-lane lower endgame bundle**: the lower fields of
`FinslerConditionalEndgameHypotheses` for the concrete lane, with the tilt
interval fixed to `1` (positive at every probe), the lower pressure field at the
probe-shifted scene Palm readout, and the lower probability localization from
`palmReadout_hprob_actual`. -/
noncomputable def endgameLowerFields_actual_lane
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (sample n)) (hYi : ∀ n, iIndepFun (Y n) (sample n))
    (hXlaw : ∀ n i, (sample n).map (X n i) =
      (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ n i, (sample n).map (Y n i) =
      (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (sample n))
    (scale : ℕ → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hintC : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearCostIntegrand (ε := ε) f t X Y scale n c) (sample n))
    (hintP : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileLinearProbeIntegrand f t X Y
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sample n))
    (hintClip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index), Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c) (sample n))
    (hPalm : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      T.TilePalmSampleLaw f t sample X Y scale c
        (fun _ ↦ T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda)
          (q := q) G c))
    (hclip : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (c : T.Index),
      Tendsto (fun n ↦ T.tileFixedPairClippingCorrection f t sample X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c)
        atTop (𝓝 0))
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hintEntry : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index)
      (i j : Fin (n + 1)),
      Integrable (fun s ↦ T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hExch : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      MaskedEntryExchangeability (sample n) (T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c))
    (hintCost : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j, T.tileCostMatrix f t X Y scale
        (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hintRes : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (fun s ↦ ∑ i, ∑ j,
        (Assign n s i j - 1 / ((n + 1 : ℕ) : ℝ)) *
          T.tileCostMatrix f t X Y scale
            (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') n c s i j)
        (sample n))
    (hresv : T.TilePlanResidualVanishing sample Assign X Y scale
      (fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c'))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileMeanProofMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (fun s c' ↦ normalizedProbe (K := A ∪ B) base t n s c')
        (Assign n) (scale n) t c) (sample n))
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
      Integrable ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n) (sample n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n s) ≤
        finslerSupportedPressure F
          (physicalSourceProbability ωM dens₀) (physicalTargetProbability ωM dens₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    :
    EndgameLowerFields F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u := by
  exact endgameLowerFields_mk (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) (fun _ ↦ 1) (fun _ ↦ zero_lt_one)
    (palmReadout_hprob_actual (hdim := hdim) (ωM := ωM) (dens₀ := dens₀) (dens₁ := dens₁) (hA := hA) (hB := hB) (hμA := hμA) (hνB := hνB) (sample := sample) (G := G) (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi) (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY) (radius := fun _ ↦ 1) (scale := scale) (base := base) (hBp := hBp) (hbase := hbase) (hintC := hintC) (hintP := hintP) (hintClip := hintClip) (hPalm := hPalm) (hclip := hclip) (Assign := Assign) (hintEntry := hintEntry) (hExch := hExch) (hintCost := hintCost) (hintRes := hintRes) (hresv := hresv) (g := g) (hF := hF) (hcomplete := hcomplete) (hu := hu) (ha := ha) (hinj := hinj) (hint := hint) (hgt := hgt) (hdecomp := hdecomp) (Ψ := Ψ) (hread := hread) (hfrozen_int := hfrozen_int) (hfrozen_dom := hfrozen_dom))

end OTSelector.Reconstruction
