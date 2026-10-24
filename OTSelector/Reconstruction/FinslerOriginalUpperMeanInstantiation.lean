import OTSelector.Reconstruction.FinslerOriginalUpperMeanBound
import OTSelector.Reconstruction.FinslerOriginalTileCountingConvergence
import OTSelector.Reconstruction.FinslerOriginalTileMeanValues
import OTSelector.Reconstruction.FinslerOriginalRootedTileCampbellMean
import OTSelector.Reconstruction.FinslerOriginalFrozenCoreCampbellIdentification
import OTSelector.Reconstruction.FinslerOriginalScenePressureWiring

/-!
# Deep-context instantiation of the matching upper population mean bound

This module performs the deep TaylorTiles-context instantiation of
RootedTileCampbellMeanUpper of FinslerOriginalUpperMeanBound.lean and closes the
two-sided identification pressureLower = Psi of
FinslerOriginalScenePressureWiring.lean.

In the TaylorTiles context (D, T, epsilon, ...) the generic tile data of the
upper mean bound is instantiated as:

* tileCost := T.tileFrozenCost normalized by (n+1);
* popVal := T.tilePopValue (constant in the probe and tilt);
* err := the upper half of the two-sided per-tile counting convergence
  T.RootedTileMeanConvergence;
* hdec := T.integral_originalFrozenCorePressure_eq_sum_tiles;
* hpop := the per-tile Campbell decomposition
  campbellAveragedFrozenCost_eq_tileSum_add_tail.

The lower mean bound is supplied by the named tile Campbell mean identification
rootedTileMeanCampbellIdentification_of_tile_means composed with
rootedTileMeanCampbellValues_of_tile_decomposition, so the final theorem
pressureLower_eq_sceneReadout_of_rootedTileMeanConvergence has no generic tile
hypotheses left: it needs only the lane-named counting convergence, the
integrable tile costs, the frozen gluing/decomposition, the mean limit hlim and
the assembled readout identity hread.

No sorry, admit or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
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

namespace PopulationLocalPressureCore.TaylorTiles

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- **The matching upper population mean bound, instantiated in the deep
TaylorTiles context.**

From the two-sided per-tile counting convergence, the integrable tile frozen
costs, the frozen gluing of the root integrand and the per-tile Campbell
decomposition, the expected frozen core cost is eventually at most the
Campbell-averaged frozen cost plus eps.  This is the deep-context instantiation
of camFrozenMeanUpperBound_of_tileMeanUpperBound: no generic tile hypotheses
remain, only the lane-named counting convergence. -/
theorem camFrozenMeanUpperBound_of_rootedTileMeanConvergence
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instUpperMeanInstantiationMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (hconv : T.RootedTileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n ≤
        campbellAveragedFrozenCost P a κ lambda (g f t) q + ε := by
  have hpop : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      campbellAveragedFrozenCost P a κ lambda (g f t) q =
        ∑ c, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c := by
    intro f t
    have h := campbellAveragedFrozenCost_eq_tileSum_add_tail (q := q) (T := T) G
      hF hcomplete hu ha hinj (tail := 0) (by rw [add_zero]; exact hdecomp f t)
    calc campbellAveragedFrozenCost P a κ lambda (g f t) q
        = campbellAveragedFrozenCost P a κ lambda
            (atlasPiecewiseRoot P a κ lambda G) q := by rw [hgt f t]
      _ = (∑ c, T.tilePopValue (P := P) (a := a) (κ := κ)
            (lambda := lambda) (q := q) G c) + 0 := h
      _ = ∑ c, T.tilePopValue (P := P) (a := a) (κ := κ)
            (lambda := lambda) (q := q) G c := add_zero _
  have hdec : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      ∫ s, fractionalAssignmentCost
          (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
            (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n =
        ∑ c, ∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
            (hprobe f t n) (A n) (scale n) t c s / ((n + 1 : ℕ) : ℝ) ∂sample n := by
    intro f t n
    have h := T.integral_originalFrozenCorePressure_eq_sum_tiles (P₀ := sample n)
      (n := n + 1)
      (X := fun (s : Ω n) (i : Fin (n + 1)) ↦ X n i s)
      (Y := fun (s : Ω n) (i : Fin (n + 1)) ↦ Y n i s)
      (h := hprobe f t n) (A := A n) (scale := scale n) (t := t)
      (hint := fun c ↦ hint f t n c)
    simpa only [div_eq_mul_inv] using h
  have hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      ∃ err : ℕ → T.Index → ℝ,
        (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∑ c, err n c ≤ δ) ∧
        (∀ (n : ℕ) (c : T.Index),
          ∫ s, T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
            (hprobe f t n) (A n) (scale n) t c s / ((n + 1 : ℕ) : ℝ) ∂sample n ≤
          T.tilePopValue (P := P) (a := a) (κ := κ) (lambda := lambda) (q := q) G c +
            err n c) := by
    intro f t
    obtain ⟨err, herrSum, herrAbs⟩ := hconv f t
    refine ⟨err, herrSum, ?_⟩
    intro n c
    have h := herrAbs n c
    rw [MeasureTheory.integral_div]
    have hupper := (abs_le.mp h).2
    linarith
  exact camFrozenMeanUpperBound_of_tileMeanUpperBound P a κ lambda g (P := sample)
    (frozenCost := fun f t n s ↦ fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
        (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ))
    (popVal := fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
      (lambda := lambda) (q := q) G c)
    (tileCost := fun f t n s c ↦ T.tileFrozenCost (fun s i ↦ X n i s)
      (fun s i ↦ Y n i s) (hprobe f t n) (A n) (scale n) t c s / ((n + 1 : ℕ) : ℝ))
    hpop hdec hbound

/-- **The two-sided identification of the pressure lower readout in the deep
TaylorTiles context.**

With the lower mean bound discharged from the named tile Campbell mean
identification (tile values from the per-tile decomposition, identification from
the per-tile Campbell means) and the upper mean bound of the previous theorem,
the assembly's pressureLower readout equals the assembled Palm readout Psi.  No
generic tile hypotheses remain. -/
theorem pressureLower_eq_sceneReadout_of_rootedTileMeanConvergence
    [MeasurableSpace.CountablySeparated (ℚ → M)]
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (G : ℕ → (ℚ → M) → ℝ)
    (g : ((K × K) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (scale : ℕ → ℝ)
    (hprobe : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instUpperMeanReadoutMetric : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hint : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (c : T.Index),
      Integrable (T.tileFrozenCost (fun s i ↦ X n i s) (fun s i ↦ Y n i s)
        (hprobe f t n) (A n) (scale n) t c) (sample n))
    (hgt : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      g f t = atlasPiecewiseRoot P a κ lambda G)
    (hdecomp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      (∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
          populationAtlasTheta P a κ lambda j z ^ (-2 / q) * G j z ∂lambda) =
        (∑ c : T.Index, T.tilePopValue (P := P) (a := a) (κ := κ)
          (lambda := lambda) (q := q) G c))
    (hconv : T.RootedTileMeanConvergence
      (fun _ _ c ↦ T.tilePopValue (P := P) (a := a) (κ := κ)
        (lambda := lambda) (q := q) G c) sample X Y scale hprobe A)
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hlim : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, fractionalAssignmentCost
        (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
          (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ) ∂sample n) atTop
        (𝓝 (pressureLower f t)))
    (Ψ : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    pressureLower = Ψ := by
  have hvalues := rootedTileMeanCampbellValues_of_tile_decomposition (T := T) G g sample
    X Y scale hprobe A hF hcomplete hu ha hinj hgt hdecomp hconv
  have hId := rootedTileCampbellMeanIdentification_of_tile_means (T := T) sample
    hint hvalues
  have hUp := camFrozenMeanUpperBound_of_rootedTileMeanConvergence (T := T) sample G g X Y
    scale hprobe A hF hcomplete hu ha hinj hint hgt hdecomp hconv
  exact pressureLower_eq_sceneReadout_of_empirical_limit P a κ lambda g (P := sample)
    (frozenCost := fun f t n s ↦ fractionalAssignmentCost
      (T.originalFrozenCoreMatrix (fun i ↦ X n i s) (fun i ↦ Y n i s)
        (scale n) t (hprobe f t n s)) (A n s) / ((n + 1 : ℕ) : ℝ))
    pressureLower hId hlim hUp Ψ hread

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction