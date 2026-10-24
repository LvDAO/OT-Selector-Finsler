import OTSelector.Reconstruction.FinslerOriginalPressureLowerReadout
import OTSelector.Reconstruction.FinslerOriginalPressureLowerAssembly
import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit

/-!
# Wiring the probability-lower input hprob of the final assembly

The final assembly carries the probability-lower field hprob, consumed through
FinalProbLowerData (the named interface of FinslerSelectorFinalInputsWiringAudit).
This module produces that field from

* the physical population data (physical source and target probabilities, compact
  carriers, the original iid arrays with their laws and independence, and the
  fixed one-Lipschitz probe);
* the frozen core cost data: frozen domination by the empirical supported pressure
  plus the probe constant, and frozen integrability;
* the tile Palm sample law paper fields together with the remaining named tile lane
  inputs (probe base bound, tile integrability, clipping-correction vanishing,
  masked-entry exchangeability, plan-residual vanishing, and the frozen readout
  family identification with its frozen core decomposition);
* the readout identification frozenPressureLower = Psi.

The tile mean identification is discharged from the Palm sample law fields: this
module uses rootedTileCampbellMeanIdentification_of_palmSampleLaw
(FinslerOriginalPressureLowerReadout) to produce the lower tile Campbell mean
identification, then frozenMeanLower_of_rootedTileIdentification to obtain the
expectation-level lower mean bound, and finally the paper's iid lower localization
physical_finsler_probability_lower_of_frozen_mean_lower to obtain the hprob field.

Three forms of the conclusion are provided:

* finalProbLowerData_of_palmSampleReadout: hprob at the probe-shifted scene Palm
  readout fun f t => Psi f t - |t| ||f||;
* finalProbLowerData_of_palmSampleLaw: the same hprob at the canonical
  frozenProbePressureLower readout (frozen Campbell readout minus the probe
  constant), equal to the former by the readout identification;
* finalProbLowerData_of_palmSampleMeanLimit: hprob at the probe-shifted empirical
  mean-limit readout fun f t => pressureLower f t - |t| ||f||, using the now
  proved readout identification pressureLower = Psi.

No sorry, admit or added axiom occurs.
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

/-- **The hprob field of the final assembly from the tile Palm sample law readout.**

Given the physical population data (physical source and target probabilities, compact
carriers, the original iid arrays with their laws and independence, and a fixed
one-Lipschitz probe), the frozen domination and integrability data of the frozen core
cost family, and the tile Palm sample law paper fields together with the remaining
named lane inputs (probe base bound, tile integrability, clipping-correction
vanishing, masked-entry exchangeability, plan-residual vanishing, and the frozen
readout family identification with its frozen core decomposition), the lower
probability input hprob of the final assembly holds at the probe-shifted scene Palm
readout Psi: for every probe and tilt in the readout interval, the empirical
supported pressure eventually lies above Psi f t - |t| ||f|| - eps with probability
tending to one.

The tile mean identification is discharged from the Palm sample law fields inside
this proof via rootedTileCampbellMeanIdentification_of_palmSampleLaw; the
expectation-level lower mean bound then follows from
frozenMeanLower_of_rootedTileIdentification, and the conclusion is the paper's iid
lower localization physical_finsler_probability_lower_of_frozen_mean_lower.  Only
the readout identification frozenPressureLower = Psi remains a named paper input.
-/
theorem finalProbLowerData_of_palmSampleReadout
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
  have hId : RootedTileCampbellMeanIdentification P a κ lambda g q sample
      ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ))) T.Index :=
    rootedTileCampbellMeanIdentification_of_palmSampleLaw (T := T) sample G X Y
      scale base hBp hbase hintC hintP hintClip hPalm hclip Assign hintEntry hExch
      hintCost hintRes hresv g hF hcomplete hu ha hinj hint hgt hdecomp
  intro f t ε ht hε
  refine physical_finsler_probability_lower_of_frozen_mean_lower 
    hcomplete hdim ωM dens₀ dens₁ hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw
    hYlaw hXY u hu (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) radius
    ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ))) hfrozen_int hfrozen_dom ?_ f t ε ht hε
  intro f t ε hε
  filter_upwards [frozenMeanLower_of_rootedTileIdentification (K := A ∪ B) P a κ
    lambda g (P := sample) (frozenCost := ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)))) (q := q)
    (ιt := T.Index) hId f t (ε / 2) (by positivity)] with n hn
  have hcamp : campbellAveragedFrozenCost P a κ lambda (g f t) q =
      frozenPressureLower P a κ lambda g q f t := rfl
  rw [hcamp, hread] at hn
  change Ψ f t - |t| * (‖f‖₊ : ℝ) + |t| * (‖f‖₊ : ℝ) - ε ≤
    ∫ s, ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n s) ∂sample n
  linarith

/-- **The hprob field at the canonical frozen probe-shifted readout.**

The same lower probability statement with the pressure readout written in its
canonical frozen form frozenProbePressureLower (the frozen Campbell readout minus
the probe constant |t| ||f||) rather than through Psi.  The two readouts agree by
the named readout identification frozenPressureLower = Psi. -/
theorem finalProbLowerData_of_palmSampleLaw
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
      (frozenProbePressureLower P a κ lambda g q) radius := by
  have hfun : frozenProbePressureLower P a κ lambda g q =
      (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) := by
    funext f t
    simp [frozenProbePressureLower, hread]
  rw [hfun]
  exact finalProbLowerData_of_palmSampleReadout (T := T) hdim ωM dens₀ dens₁ hA hB hμA hνB sample G X Y hX hY hXi hYi
      hXlaw hYlaw hXY radius scale base hBp hbase hintC hintP hintClip hPalm hclip
      Assign hintEntry hExch hintCost hintRes hresv g hF hcomplete hu ha hinj hint
      hgt hdecomp Ψ hread
    hfrozen_int hfrozen_dom

/-- **The hprob field at the empirical mean-limit readout.**

If pressureLower is the limit of the empirical frozen core means, then the
already proved readout identification pressureLower = Psi (proved from the tile
Palm sample law fields and the remaining named lane inputs by
pressureLower_eq_sceneReadout_of_palmSampleLaw) turns the hprob field of the first
theorem into the same statement for the probe-shifted mean-limit readout.  This is
the assembly's hprob field with pressureLower = Psi. -/
theorem finalProbLowerData_of_palmSampleMeanLimit
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
    (pressureLower : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hlim : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n) ↦ fractionalAssignmentCost (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s) (scale n) t ((fun (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) t n s c' ↦ normalizedProbe (K := A ∪ B) base t n s c') f t n s)) (Assign n s) / ((n + 1 : ℕ) : ℝ)) f t n s) ∂sample n) atTop
        (𝓝 (pressureLower f t)))
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
      (fun f t ↦ pressureLower f t - |t| * (‖f‖₊ : ℝ)) radius := by
  have hreadout : pressureLower = Ψ :=
    pressureLower_eq_sceneReadout_of_palmSampleLaw (T := T) sample G X Y scale
      base hBp hbase hintC hintP hintClip hPalm hclip Assign hintEntry hExch
      hintCost hintRes hresv g hF hcomplete hu ha hinj hint hgt hdecomp
      pressureLower hlim Ψ hread
  have hfun : (fun f t ↦ pressureLower f t - |t| * (‖f‖₊ : ℝ)) =
      (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) := by
    funext f t
    rw [show pressureLower f t = Ψ f t from congrFun (congrFun hreadout f) t]
  rw [hfun]
  exact finalProbLowerData_of_palmSampleReadout (T := T) hdim ωM dens₀ dens₁ hA hB hμA hνB sample G X Y hX hY hXi hYi
      hXlaw hYlaw hXY radius scale base hBp hbase hintC hintP hintClip hPalm hclip
      Assign hintEntry hExch hintCost hintRes hresv g hF hcomplete hu ha hinj hint
      hgt hdecomp Ψ hread
    hfrozen_int hfrozen_dom

end OTSelector.Reconstruction
