import OTSelector.Reconstruction.FinslerOriginalTileClippingConcrete
import OTSelector.Reconstruction.FinslerOriginalFrozenCostSupBound

/-!
# Frozen cost sup bound wired into the tile lane

This module closes gap (i) of `FinslerOriginalTileClippingConcrete.lean`: it instantiates
the frozen cost sup bound
`FinslerOriginalFrozenCostSupBound.frozenPhysicalCost_abs_le_of_boundedEdge` with the
tile lane's own data,

* the tile cover `T.cover c : (T.core c).TaylorRootCover ε` (a field of the
  `TaylorTiles` structure),
* the tile reference `T.reference c = (T.partition c.1).center c.2` (a cover center),
* the retained-edge geometric conditions (root membership, neighborhood membership,
  window membership, and the two exact readout equations) and the numerical bounds
  `Dm` on the Finsler length and `U` on the potential,

yielding the pointwise bound
```|(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)|
  ≤ (Dm + 2 U) / (1 - 2ε)```
in the actual lane (`frozenPhysicalCost_tileBound`), its uniform all-pairs form, and
finally the clipping correction vanishing for the actual lane with the concrete
normalized scene probe (`tileFixedPairClipping_tendsto_zero_of_tileLane`).

**What remains.**  Only the *linear Palm identification* of the plan-free tile lane;
the clipping side is now fully wired (the geometric conditions are the lane's
retained-edge data, and `T.edgeEvent` supplies the window condition for masked pairs).

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
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
  {K : Set M} {q : ℝ}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace PopulationLocalPressureCore.TaylorTiles

/-- **Frozen cost sup bound in the tile lane, pointwise form.**  For a retained edge
of the tile (reference a cover center, both roots in the tile's root set and
neighborhood, potentials in the retained window, and the two exact readouts), the
frozen physical cost is bounded by `(Dm + 2 U)/(1 - 2ε)`. -/
theorem frozenPhysicalCost_tileBound
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileBoundMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε0 : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (n : ℕ) (c : T.Index) (s : Ω n) (i j : Fin (n + 1))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hz₀ : T.reference c ∈ (T.cover c.1).centers)
    (hx : a (X n i s) ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c))
    (hy : a (Y n j s) ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c))
    (hp : (u (X n i s), u (Y n j s)) ∈ (T.core c).window.region)
    (hxread : X n i s = (P (T.core c).seedIndex).seed.curve
      (populationSeedRootLabelValue (P (T.core c).seedIndex).seed a (a (X n i s)))
      (u (X n i s) - (P (T.core c).seedIndex).seed.level))
    (hyread : Y n j s = (P (T.core c).seedIndex).seed.curve
      (populationSeedRootLabelValue (P (T.core c).seedIndex).seed a (a (Y n j s)))
      (u (Y n j s) - (P (T.core c).seedIndex).seed.level))
    {Dm U : ℝ} (hd : (F.lengthEDist (X n i s) (Y n j s)).toReal ≤ Dm)
    (hux : |u (X n i s)| ≤ U) (huy : |u (Y n j s)| ≤ U) :
    |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤
      (Dm + 2 * U) / (1 - 2 * ε) :=
  frozenPhysicalCost_abs_le_of_boundedEdge hF hcomplete hu ha hinj
    (T.cover c.1) hε0 hε1 hz₀ hx hy hp hxread hyread hd hux huy

/-- **Frozen cost sup bound in the tile lane, uniform form.** -/
theorem frozenPhysicalCost_tileBound_uniform
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileBoundMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε0 : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index)
    (hz₀ : T.reference c ∈ (T.cover c.1).centers)
    (hx : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)),
      a (X n i s) ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c))
    (hy : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)),
      a (Y n j s) ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c))
    (hp : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      (u (X n i s), u (Y n j s)) ∈ (T.core c).window.region)
    (hxread : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)),
      X n i s = (P (T.core c).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (T.core c).seedIndex).seed a (a (X n i s)))
        (u (X n i s) - (P (T.core c).seedIndex).seed.level))
    (hyread : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)),
      Y n j s = (P (T.core c).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (T.core c).seedIndex).seed a (a (Y n j s)))
        (u (Y n j s) - (P (T.core c).seedIndex).seed.level))
    {Dm U : ℝ}
    (hd : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      (F.lengthEDist (X n i s) (Y n j s)).toReal ≤ Dm)
    (hux : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)), |u (X n i s)| ≤ U)
    (huy : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)), |u (Y n j s)| ≤ U) :
    ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      |(T.core c).frozenPhysicalCost (T.reference c) (X n i s) (Y n j s)| ≤
        (Dm + 2 * U) / (1 - 2 * ε) :=
  fun n s i j ↦ frozenPhysicalCost_tileBound (T := T) hF hcomplete hu ha hinj hε0 hε1
    n c s i j X Y hz₀ (hx n s i) (hy n s j) (hp n s i j) (hxread n s i)
    (hyread n s j) (hd n s i j) (hux n s i) (huy n s j)

/-- **Clipping correction vanishing in the actual tile lane.**  Combining the wired
frozen sup bound with the concrete probe decay, the fixed-pair clipping correction of
the tile lane tends to zero. -/
theorem tileFixedPairClipping_tendsto_zero_of_tileLane
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (hε : ε ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instTileBoundMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (c : T.Index)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hz₀ : T.reference c ∈ (T.cover c.1).centers)
    (hx : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)),
      a (X n i s) ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c))
    (hy : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)),
      a (Y n j s) ∈ (T.core c).roots ∩ (T.cover c.1).neighborhood (T.reference c))
    (hp : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      (u (X n i s), u (Y n j s)) ∈ (T.core c).window.region)
    (hxread : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)),
      X n i s = (P (T.core c).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (T.core c).seedIndex).seed a (a (X n i s)))
        (u (X n i s) - (P (T.core c).seedIndex).seed.level))
    (hyread : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)),
      Y n j s = (P (T.core c).seedIndex).seed.curve
        (populationSeedRootLabelValue (P (T.core c).seedIndex).seed a (a (Y n j s)))
        (u (Y n j s) - (P (T.core c).seedIndex).seed.level))
    {Dm U : ℝ} (hDm : 0 ≤ Dm) (hU : 0 ≤ U)
    (hd : ∀ (n : ℕ) (s : Ω n) (i j : Fin (n + 1)),
      (F.lengthEDist (X n i s) (Y n j s)).toReal ≤ Dm)
    (hux : ∀ (n : ℕ) (s : Ω n) (i : Fin (n + 1)), |u (X n i s)| ≤ U)
    (huy : ∀ (n : ℕ) (s : Ω n) (j : Fin (n + 1)), |u (Y n j s)| ≤ U)
    (hint : ∀ n, Integrable
      (T.tileClippingIntegrand (ε := ε) f t X Y tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c) (sample n)) :
    Tendsto (fun n ↦
      T.tileFixedPairClippingCorrection f t sample X Y tileScale
        (fun f t n s c' ↦ normalizedProbe (K := K) base t n s c') n c)
      atTop (𝓝 0) := by
  have hden : 0 < 1 - 2 * ε := by linarith
  have hRnonneg : 0 ≤ (Dm + 2 * U) / (1 - 2 * ε) :=
    div_nonneg (by linarith) (le_of_lt hden)
  have hR := frozenPhysicalCost_tileBound_uniform (T := T) hF hcomplete hu ha hinj
    hε0 hε1 X Y c hz₀ hx hy hp hxread hyread hd hux huy
  exact tileFixedPairClipping_tendsto_zero_of_concreteData (T := T) sample hε f t X Y c
    base hBp hbase hRnonneg hR hint

end PopulationLocalPressureCore.TaylorTiles

end OTSelector.Reconstruction
