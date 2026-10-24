import OTSelector.Reconstruction.FinslerOriginalUpperMeanBound
import OTSelector.Reconstruction.FinslerOriginalPressureLowerAssembly
import OTSelector.Reconstruction.FinslerOriginalCommonScalePressureWiring
import OTSelector.Reconstruction.FinslerFrozenCoreDomination

/-!
# Frozen domination and frozen integral limit data for the pressure-lower readout

The pressure-lower probabilistic readout
physical_finsler_probability_lower_of_tileIdentification consumes two frozen
fields for the frozen core cost family frozenCost:

* an integrability field hfrozen_int, i.e. frozenCost f t n is integrable;
* a frozen domination field hfrozen_dom: the frozen core is almost surely at
  most the empirical supported pressure shifted by the probe constant |t| ||f||.

The readout identification pressureLower_eq_sceneReadout_of_tileIdentification
additionally consumes the frozen integral limit hlim: the empirical frozen
integrals converge to the pressure readout.

This module produces:

1. tendsto_frozenIntegral_frozenPressureLower: the frozen integral limit.  The
   already-named lower tile Campbell mean identification and its named upper
   mirror sandwich the empirical frozen means at the Campbell-averaged frozen
   cost, and the readout is exactly frozenPressureLower.

2. integrable_of_ae_norm_le_integrable and frozenIntegrable_of_wholePathDomination:
   the frozen integrability field from frozen domination by an integrable
   function of the edge/tile data (the whole-path traffic), via the amplitude
   plus linear traffic domination and the lane whole-path second-moment data.

3. FrozenPressureDominationData: the frozen data bundle whose fields are
   definitionally the two frozen fields consumed by the readout, with a
   constructor that produces the integrability field from the domination data
   and keeps the supported-pressure domination field explicit.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

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
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {K : Set M}

/-! ## The frozen integral limit -/

/-- **The frozen integral limit: frozen integrals converge to the readout.**

Let P be the sample laws, frozenCost the frozen core cost family and g the
frozen root integrand.  If the frozen core mean is controlled from below by the
named tile Campbell mean identification RootedTileCampbellMeanIdentification and
from above by its named upper mirror RootedTileCampbellMeanUpper, then for every
probe f and tilt t the frozen integrals converge to the frozen lower pressure
readout frozenPressureLower, which is exactly the Campbell-averaged frozen cost
of the frozen root integrand. -/
theorem tendsto_frozenIntegral_frozenPressureLower
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (g : ((K × K) →ᵇ ℝ) → ℝ → Z → ℝ) {q : ℝ}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {ιt : Type*} [Fintype ιt]
    (hId : RootedTileCampbellMeanIdentification Seed a κ lambda g q P frozenCost ιt)
    (hUp : RootedTileCampbellMeanUpper Seed a κ lambda g q P frozenCost ιt) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ),
      Tendsto (fun n ↦ ∫ s, frozenCost f t n s ∂P n) atTop
        (𝓝 (frozenPressureLower Seed a κ lambda g q f t)) := by
  intro f t
  change Tendsto (fun n ↦ ∫ s, frozenCost f t n s ∂P n) atTop
    (𝓝 (campbellAveragedFrozenCost Seed a κ lambda (g f t) q))
  have hlow := camFrozenMeanBound_of_rootedTileIdentification Seed a κ lambda g
    (P := P) (frozenCost := frozenCost) (q := q) hId
  have hupp := camFrozenMeanUpperBound_of_rootedTileUpper Seed a κ lambda g
    (P := P) (frozenCost := frozenCost) (q := q) hUp
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    have hε : 0 < (campbellAveragedFrozenCost Seed a κ lambda (g f t) q - b) / 2 := by
      linarith
    filter_upwards [hlow f t ((campbellAveragedFrozenCost Seed a κ lambda (g f t) q - b) / 2) hε]
      with n hn
    linarith
  · intro b hb
    have hε : 0 < (b - campbellAveragedFrozenCost Seed a κ lambda (g f t) q) / 2 := by
      linarith
    filter_upwards [hupp f t ((b - campbellAveragedFrozenCost Seed a κ lambda (g f t) q) / 2) hε]
      with n hn
    linarith

/-! ## The frozen integrability field from frozen domination -/

/-- **Frozen integrability from domination by an integrable function.** -/
theorem integrable_of_ae_norm_le_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → ℝ} (hT : Measurable T) {bound : α → ℝ}
    (hbound : Integrable bound μ) (hle : ∀ᵐ s ∂μ, |T s| ≤ bound s) :
    Integrable T μ := by
  refine hbound.mono' hT.aestronglyMeasurable ?_
  filter_upwards [hle] with s hs
  simpa only [Real.norm_eq_abs] using hs

/-- **Frozen integrability from whole-path traffic domination.**

The frozen core cost family is dominated by the integrable whole-path traffic:
|frozenCost f t n s| ≤ Aamp f t + Camp f t * traffic n s with Camp f t ≥ 0 and
the whole-path second-moment data CommonScaleWholePathPressureData.  Then the
frozen cost is integrable: this is the integrability field consumed by the
readout. -/
theorem frozenIntegrable_of_wholePathDomination
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (hPfin : ∀ n, IsFiniteMeasure (P n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {traffic : ∀ n, Ω n → ℝ} {phaseBad : ∀ n, Set (Ω n)}
    {CBs CLs B0s : ℕ → ℝ}
    {Aamp Camp : ((K × K) →ᵇ ℝ) → ℝ → ℝ}
    (hdata : ∀ n, CommonScaleWholePathPressureData (P n) (traffic n) (phaseBad n)
      (CBs n) (CLs n) (B0s n))
    (htraf : ∀ n, Measurable (traffic n))
    (hbad : ∀ n, MeasurableSet (phaseBad n))
    (hbadint : ∀ n, Integrable ((phaseBad n).indicator (traffic n)) (P n))
    (hmeas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), Measurable (frozenCost f t n))
    (hCamp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), 0 ≤ Camp f t)
    (hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n),
      |frozenCost f t n s| ≤ Aamp f t + Camp f t * traffic n s) :
    ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), Integrable (frozenCost f t n) (P n) := by
  intro f t n
  haveI : IsFiniteMeasure (P n) := hPfin n
  exact integrable_of_dominated_by_wholePath (hdata n) (htraf n) (hbad n)
    (hbadint n) (hmeas f t n) (hCamp f t) (hbound f t n)

/-! ## The frozen data bundle -/

/-- **Frozen pressure domination data consumed by the readout.**

The two frozen fields of physical_finsler_probability_lower_of_tileIdentification
(the supported-pressure domination and the frozen integrability), for an
arbitrary empirical pressure family standing for the supported pressure.
This is exactly the frozen data the readout consumes. -/
structure FrozenPressureDominationData
    {K : Set M} {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (empiricalPressure : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ) : Prop where
  /-- Frozen domination: frozen core at most supported pressure plus probe. -/
  frozen_dominated : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
    frozenCost f t n s ≤ empiricalPressure f t n s + |t| * (‖f‖₊ : ℝ)
  /-- Frozen integrability. -/
  frozen_integrable : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
    Integrable (frozenCost f t n) (P n)

/-- **The frozen data bundle from frozen domination by whole-path traffic.**

The integrability field is produced from the amplitude plus linear traffic
domination and the whole-path second-moment data; the supported-pressure frozen
domination field is kept explicit, since it is supplied by the finite-domination
geometric lane. -/
theorem frozenPressureDominationData_of_wholePathDomination
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (hPfin : ∀ n, IsFiniteMeasure (P n))
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (empiricalPressure : ((K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    {traffic : ∀ n, Ω n → ℝ} {phaseBad : ∀ n, Set (Ω n)}
    {CBs CLs B0s : ℕ → ℝ}
    {Aamp Camp : ((K × K) →ᵇ ℝ) → ℝ → ℝ}
    (hdata : ∀ n, CommonScaleWholePathPressureData (P n) (traffic n) (phaseBad n)
      (CBs n) (CLs n) (B0s n))
    (htraf : ∀ n, Measurable (traffic n))
    (hbad : ∀ n, MeasurableSet (phaseBad n))
    (hbadint : ∀ n, Integrable ((phaseBad n).indicator (traffic n)) (P n))
    (hmeas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), Measurable (frozenCost f t n))
    (hCamp : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), 0 ≤ Camp f t)
    (hbound : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) (s : Ω n),
      |frozenCost f t n s| ≤ Aamp f t + Camp f t * traffic n s)
    (hfrozen_dom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤ empiricalPressure f t n s + |t| * (‖f‖₊ : ℝ)) :
    FrozenPressureDominationData P frozenCost empiricalPressure :=
  ⟨hfrozen_dom,
    frozenIntegrable_of_wholePathDomination P hPfin frozenCost hdata htraf hbad
      hbadint hmeas hCamp hbound⟩

end OTSelector.Reconstruction
