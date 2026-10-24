import OTSelector.Reconstruction.FinslerOriginalUpperPoolReverseBound
import OTSelector.Reconstruction.FinslerOriginalEndgameLowerField
import OTSelector.Reconstruction.FinslerOriginalEndgameUpperField
import OTSelector.Reconstruction.FinslerOriginalEndgameUpperFieldActual

/-!
# The F18 pressure data inputs on the common perturbation interval

This module assembles the remaining pressure-data inputs of the actual endgame
assembly (the hU field of F18) from the lane producers.

## What is produced

The lower consumer field FinalProbLowerData is the hprob field of the endgame
lower bundle EndgameLowerFields (in the actual lane: the frozen readout
pressureLower = Psi f t - |t| * ||f|| with the rooted-tile mean identification,
or the unshifted readout with the paper identification).  The upper consumer
field FinalProbUpperData is the hupper field of the endgame upper bundle
EndgameUpperFields (in the actual lane: endgameUpperFields_actual_lane, built
from the block weighted physical upper localization
physicalWeightedLocalizationFamily_actualLane via
finalProbUpperData_actualPool).  The bundle EndgamePressureData packages the two
fields on one common radius field; endgamePressureData_mk builds it from the two
lane bundles plus the radius agreement, which is definitional for the actual
lane (both lane radii are fun _ => 1: endgameUpperRadius_actual).

## The reverse bound on the interval

FinslerOriginalUpperPoolReverseBound proves the comparison step
le_of_probabilityLower_and_integralUpper and instantiates it at the physical
pressure (pressureLower_le_pressureUpper_of_lower_and_upper_data).  Feeding it
the two consumer fields gives pressureLower <= pressureUpper on the common
radius.  With the frozen-readout identification hL (pressureLower = Iw) and the
class screening (Iw = I2), this is the reverse bound I2 <= pool on the
perturbation interval (upperPoolReverseBoundOnRadius_of_endgamePressureData).
The lower-bound half of the bridge is assignment 9's blockwise weak duality
(upperPoolLowerBound_of_blockwiseWeakDuality), so the actual pool readout
equality holds on the interval (upperStationaryReadout_on_radius_of_endgamePressureData).

## The off-interval convention

Both consumer fields are restricted to |t| < radius f, and the paper's
estimates are only available there; off the interval the local limits pc are
unconstrained.  The canonical extension upperPoolPressureExtension sets the pool
equal to I2 off the interval (each local limit is set to I2 t).  This leaves pc
unchanged on the interval, so the localization data, the per-block
identification hpc and the upper expectation bound all transfer to the
extension (physicalWeightedLocalizationFamily_upperPoolPressureExtension).  The
extended pool then satisfies both halves of the bridge unconditionally:

* reverse: on the interval from the pressure estimates, off the interval
  because the pool equals I2 (upperPoolReverseBound_upperPoolPressureExtension);
* lower bound: on the interval from the blockwise weak duality for pc, off the
  interval from weak duality I2 <= K w + t P w for second-moment competitors
  (upperPoolLowerBound_upperPoolPressureExtension).

Hence ActualUpperReadout holds for the extended field
(actualUpperReadout_of_endgamePressureData), and the extension agrees with the
lane's pc on the perturbation interval.  The residual inputs are exactly the
lane data of the two bundles (unchanged, those of the producers
endgameLowerFields_actual_lane_wired and endgameUpperFields_actual_lane), the
frozen readout identification hL, the class screening Iw = I2, and the
blockwise weak-duality data kappa, pi for the lower-bound half.  There is no
residual physical estimate: the only convention is the value of the local
limits pc outside the perturbation interval, where the paper makes no claim.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex OTSelector.Pressure Module
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : ProbabilityMeasure M}

/-! ## 1. The bundle of the two consumer pressure data fields -/

/-- **The two consumer pressure data fields on one common perturbation
interval.**  This is the exact pair consumed by the pressure comparison: the
lower probability localization at pressureLower and the upper expectation
localization at pressureUpper, both on the common radius. -/
structure EndgamePressureData (F : ContinuousFinslerNorm E M)
    (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ) where
  /-- The lower pressure localization limit. -/
  pressureLower : FinalPressureField A B
  /-- The upper pressure localization limit. -/
  pressureUpper : FinalPressureField A B
  /-- The common tilt interval. -/
  radius : FinalRadiusField A B
  /-- The tilt interval is positive at every probe. -/
  hradius : FinalPositiveRadius radius
  /-- The lower probability localization (paper weighted lower bound). -/
  hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius
  /-- The upper expectation localization (paper second-moment upper bound). -/
  hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius

/-- **The two consumer fields, packaged.**  The lower bundle contributes hprob
and the positivity of the common radius, the upper bundle contributes hupper;
the radius agreement makes the two fields live on the same perturbation
interval. -/
def endgamePressureData_mk
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (L : EndgameLowerFields F μ ν hA hB hμA hνB P X Y u)
    (S : EndgameUpperFields F μ ν hA hB hμA hνB P X Y u)
    (hrad : L.radius = S.radius) :
    EndgamePressureData F μ ν hA hB hμA hνB P X Y u where
  pressureLower := L.pressureLower
  pressureUpper := S.pressureUpper
  radius := L.radius
  hradius := L.hradius
  hprob := L.hprob
  hupper := by
    rw [hrad]
    exact S.hupper

/-- The two consumer fields from raw data: only the two localization fields, the
common radius, its positivity and the radius agreement are needed.  This is the
form used when the lane provides the frozen readout directly (pressureLower)
and the weighted upper localization directly (pressureUpper). -/
def endgamePressureData_of_data
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B) (hradius : FinalPositiveRadius radius)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius) :
    EndgamePressureData F μ ν hA hB hμA hνB P X Y u where
  pressureLower := pressureLower
  pressureUpper := pressureUpper
  radius := radius
  hradius := hradius
  hprob := hprob
  hupper := hupper

/-- The lower consumer field of the bundle. -/
theorem finalProbLowerData_of_endgamePressureData
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (D : EndgamePressureData F μ ν hA hB hμA hνB P X Y u) :
    FinalProbLowerData F μ ν hA hB hμA hνB P X Y u D.pressureLower D.radius :=
  D.hprob

/-- The upper consumer field of the bundle. -/
theorem finalProbUpperData_of_endgamePressureData
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)}
    {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}
    (D : EndgamePressureData F μ ν hA hB hμA hνB P X Y u) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u D.pressureUpper D.radius :=
  D.hupper

/-- **The two consumer fields of the actual upper lane.**  The lower field is
the hprob field of the endgame lower bundle (the lane's frozen readout route) and
the upper field is the actual-lane weighted-localization bundle
endgameUpperFields_actual_lane (hpc field from the block weighted physical upper
localization).  The radius agreement is the lane identity
lower.radius = endgameUpperRadius_actual = fun _ => 1. -/
def endgamePressureData_of_upperLane
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (lower : EndgameLowerFields F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (hu : let _instEndgameUpperLane : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (hAB : Disjoint A B)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (q m : ℕ) (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c)
    (hrad : lower.radius = endgameUpperRadius_actual (A := A) (B := B)) :
    EndgamePressureData F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u :=
  endgamePressureData_mk lower
    (endgameUpperFields_actual_lane (F := F) (u := u) (hu := hu)
      (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
      (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB) (P := P)
      (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
      (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY) (q := q) (m := m)
      (hm := hm) (pc := pc) (Am := Am) (Cm := Cm) (data := data) (hpc := hpc))
    hrad

/-! ## 2. The pressure comparison and the reverse bound on the interval -/

/-- **The paper pressure comparison at the common radius.**  The two consumer
fields of the bundle feed the comparison step of the paper: the lower
probability bound and the upper expectation bound force
pressureLower <= pressureUpper on the perturbation interval. -/
theorem endgamePressureData_pressureLower_le_pressureUpper
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instEndgamePressureData : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (D : EndgamePressureData F μ ν hA hB hμA hνB P X Y u) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < D.radius f →
      D.pressureLower f t ≤ D.pressureUpper f t := by
  intro f t ht
  exact pressureLower_le_pressureUpper_of_lower_and_upper_data hA hB hμA hνB
    hcomplete hX hY hXlaw hYlaw hφ D.hprob D.hupper ht

/-- **The reverse bound on the common perturbation interval.**  The comparison
gives pressureLower <= pool.  The frozen-readout identification hL
(pressureLower = Iw) and the class screening Iw = I2 turn this into
I2 <= pool. -/
theorem upperPoolReverseBoundOnRadius_of_endgamePressureData
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instEndgamePressureData : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (D : EndgamePressureData F μ ν hA hB hμA hνB P X Y u)
    {q m : ℕ} {W : Type*} {G Cb : ℝ}
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hpcid : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      D.pressureUpper f t = endgameUpperPressure_actual q m pc f t)
    (hL : LowerStationaryReadout D.pressureLower datum)
    (hscreen : StationaryScreening datum) :
    UpperPoolReverseBoundOnRadius q m pc datum D.radius := by
  intro f t ht
  have hcmp : D.pressureLower f t ≤ D.pressureUpper f t :=
    endgamePressureData_pressureLower_le_pressureUpper hcomplete hX hY hXlaw hYlaw hφ D f t ht
  rw [hpcid f t] at hcmp
  have hIw : (datum f).Iw t = (datum f).I2 t := by
    simpa only [stationaryLowerField, stationaryUpperField] using
      finalValueIdentification_stationaryFields datum hscreen f t
  rw [← hIw, ← hL f t]
  exact hcmp

/-- **The pool readout equality on the common perturbation interval.**  The
lower-bound half of assignment 9 (blockwise weak duality) and the reverse bound
above give pool = I2 on the interval, without any off-interval convention. -/
theorem upperStationaryReadout_on_radius_of_endgamePressureData
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instEndgamePressureData : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (D : EndgamePressureData F μ ν hA hB hμA hνB P X Y u)
    {q m : ℕ} {W : Type*} {G Cb : ℝ}
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hpcid : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      D.pressureUpper f t = endgameUpperPressure_actual q m pc f t)
    (hL : LowerStationaryReadout D.pressureLower datum)
    (hscreen : StationaryScreening datum)
    (hlow : UpperPoolLowerBound q m pc datum) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < D.radius f →
      endgameUpperPressure_actual q m pc f t = (datum f).I2 t := by
  intro f t ht
  have hle : endgameUpperPressure_actual q m pc f t ≤ (datum f).I2 t :=
    (upperPoolLowerBound_iff_le_I2 q m pc datum).mp hlow f t
  have hrev : (datum f).I2 t ≤ endgameUpperPressure_actual q m pc f t :=
    upperPoolReverseBoundOnRadius_of_endgamePressureData hcomplete hX hY hXlaw hYlaw
      hφ D pc hpcid hL hscreen f t ht
  exact le_antisymm hle hrev

/-! ## 3. The canonical off-interval extension of the local limits -/

/-- **The canonical off-interval extension of the local limits.**  On the
perturbation interval the limit field is unchanged; off it, every local limit is
set to the second-moment readout, so the block weighted pool equals I2 there.
The extension is the natural representative of the localization class: the
paper constrains pc only on the perturbation interval. -/
def upperPoolPressureExtension
    {A B : Set M} {q m : ℕ} {W : Type*} {G Cb : ℝ}
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (radius : FinalRadiusField A B) :
    FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ :=
  fun f t c => if |t| < radius f then pc f t c else (datum f).I2 t

/-- The extension agrees with the local limits on the perturbation interval. -/
theorem upperPoolPressureExtension_eq_on_radius
    {A B : Set M} {q m : ℕ} {W : Type*} {G Cb : ℝ}
    {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {radius : FinalRadiusField A B}
    {f : FinalProbeSpace A B} {t : ℝ} (ht : |t| < radius f)
    (c : Fin q → Fin m) :
    upperPoolPressureExtension pc datum radius f t c = pc f t c := by
  simp only [upperPoolPressureExtension]
  exact ite_eq_left ht

/-- Off the perturbation interval the extension equals the second-moment
readout. -/
theorem upperPoolPressureExtension_eq_off_radius
    {A B : Set M} {q m : ℕ} {W : Type*} {G Cb : ℝ}
    {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {radius : FinalRadiusField A B}
    {f : FinalProbeSpace A B} {t : ℝ} (ht : ¬ |t| < radius f)
    (c : Fin q → Fin m) :
    upperPoolPressureExtension pc datum radius f t c = (datum f).I2 t := by
  simp only [upperPoolPressureExtension]
  exact ite_eq_right ht

/-- The pool of the extension equals the pool of the local limits on the
perturbation interval. -/
theorem endgameUpperPressure_actual_extension_eq_of_lt
    {A B : Set M} {q m : ℕ} {W : Type*} {G Cb : ℝ}
    {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {radius : FinalRadiusField A B}
    {f : FinalProbeSpace A B} {t : ℝ} (ht : |t| < radius f) :
    endgameUpperPressure_actual q m (upperPoolPressureExtension pc datum radius) f t =
      endgameUpperPressure_actual q m pc f t := by
  rw [endgameUpperPressure_actual_apply, endgameUpperPressure_actual_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [upperPoolPressureExtension_eq_on_radius ht]

/-- Off the perturbation interval the pool of the extension equals the
second-moment readout (the weighted sum of a constant block). -/
theorem endgameUpperPressure_actual_extension_of_not_lt
    {A B : Set M} {q m : ℕ} {W : Type*} {G Cb : ℝ}
    {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {radius : FinalRadiusField A B} {hm : 0 < m}
    {f : FinalProbeSpace A B} {t : ℝ} (ht : ¬ |t| < radius f) :
    endgameUpperPressure_actual q m (upperPoolPressureExtension pc datum radius) f t =
      (datum f).I2 t := by
  rw [endgameUpperPressure_actual_apply]
  have hsum : (∑ c : Fin q → Fin m,
      (1 / (((m ^ q : ℕ) : ℝ))) *
        upperPoolPressureExtension pc datum radius f t c) =
      (∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * ((datum f).I2 t)) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [upperPoolPressureExtension_eq_off_radius ht]
  rw [hsum, sum_blockWeight_mul hm ((datum f).I2 t)]

/-! ## 4. Transfer of the lane data to the extension -/

/-- The block weighted upper localization is unchanged by the off-interval
extension: its conclusion only refers to the local limits on the perturbation
interval. -/
theorem physicalWeightedLocalizationFamily_upperPoolPressureExtension
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    {q m : ℕ} {W : Type*} {G Cb : ℝ}
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (radius : FinalRadiusField A B)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius) :
    PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => upperPoolPressureExtension pc datum radius f t c) radius := by
  intro f t ht ε hε
  filter_upwards [hLoc f t ht ε hε] with n hn
  have hsum : (∑ c : Fin q → Fin m,
      (1 / (((m ^ q : ℕ) : ℝ))) *
        upperPoolPressureExtension pc datum radius f t c) =
      ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [upperPoolPressureExtension_eq_on_radius (datum := datum) (radius := radius) ht]
  rw [hsum]
  exact hn

/-- The per-block identification of the population limits with the local
limits transfers to the extension on the perturbation interval. -/
theorem popData_identification_upperPoolPressureExtension
    {A B : Set M} {q m : ℕ} {W : Type*} {G Cb : ℝ}
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (radius : FinalRadiusField A B) {p : (Fin q → Fin m) → ℝ → ℝ}
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ∀ c : Fin q → Fin m, p c t = pc f t c)
    {f : FinalProbeSpace A B} {t : ℝ} (ht : |t| < radius f)
    (c : Fin q → Fin m) :
    p c t = upperPoolPressureExtension pc datum radius f t c := by
  rw [upperPoolPressureExtension_eq_on_radius (datum := datum) (radius := radius) ht]
  exact hpc f t ht c

/-! ## 5. Both halves of the bridge for the extended field -/

/-- **Reverse half for the extended field, unconditionally.**  On the interval
the pool is that of pc, so the reverse bound on the interval applies; off the
interval the pool equals I2, so the comparison is an equality. -/
theorem upperPoolReverseBound_upperPoolPressureExtension
    {A B : Set M} {q m : ℕ} {W : Type*} {G Cb : ℝ}
    {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {radius : FinalRadiusField A B} (hm : 0 < m)
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius) :
    UpperPoolReverseBound q m (upperPoolPressureExtension pc datum radius) datum := by
  intro f t
  by_cases ht : |t| < radius f
  · rw [endgameUpperPressure_actual_extension_eq_of_lt ht]
    exact hon f t ht
  · rw [endgameUpperPressure_actual_extension_of_not_lt (hm := hm) ht]

/-- **Lower-bound half for the extended field, unconditionally.**  On the
interval the pool is that of pc, so the blockwise lower bound applies; off the
interval weak duality I2 <= K w + t P w bounds the extended pool by every
second-moment competitor cost. -/
theorem upperPoolLowerBound_upperPoolPressureExtension
    {A B : Set M} {W : Type*} {G Cb : ℝ} {q m : ℕ}
    (hm : 0 < m) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {radius : FinalRadiusField A B}
    (hlow : UpperPoolLowerBound q m pc datum) :
    UpperPoolLowerBound q m (upperPoolPressureExtension pc datum radius) datum := by
  intro f t w hw
  by_cases ht : |t| < radius f
  · rw [endgameUpperPressure_actual_extension_eq_of_lt ht]
    exact hlow f t w hw
  · rw [endgameUpperPressure_actual_extension_of_not_lt (hm := hm) ht]
    exact I2_le_competitor (datum f) t hw

/-! ## 6. The actual upper readout from the pressure data -/

/-- **hU from the pressure data plus the frozen readout and screening.**  The
two consumer fields give the reverse bound on the perturbation interval; the
blockwise weak-duality data gives the lower-bound half; the canonical extension
of the local limits gives both halves off the interval.  The result is the
actual upper readout bridge for the extended local limits, which agree with the
lane's limits on the perturbation interval. -/
theorem actualUpperReadout_of_endgamePressureData
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instEndgamePressureData : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (D : EndgamePressureData F μ ν hA hB hμA hνB P X Y u)
    {q m : ℕ} {W : Type*} {G Cb : ℝ} {hm : 0 < m}
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hpcid : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      D.pressureUpper f t = endgameUpperPressure_actual q m pc f t)
    (hL : LowerStationaryReadout D.pressureLower datum)
    (hscreen : StationaryScreening datum)
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * π c w) :
    ActualUpperReadout q m (upperPoolPressureExtension pc datum D.radius) datum := by
  have hlow : UpperPoolLowerBound q m pc datum :=
    upperPoolLowerBound_of_blockwiseWeakDuality hm pc datum κ π hloc hK hP
  have hon : UpperPoolReverseBoundOnRadius q m pc datum D.radius :=
    upperPoolReverseBoundOnRadius_of_endgamePressureData hcomplete hX hY hXlaw hYlaw
      hφ D pc hpcid hL hscreen
  exact actualUpperReadout_of_lowerBound_and_reverseBound q m
    (upperPoolPressureExtension pc datum D.radius) datum
    (upperPoolLowerBound_upperPoolPressureExtension hm hlow)
    (upperPoolReverseBound_upperPoolPressureExtension hm hon)

/-- **Existence form of the hU closure.**  There is a field of local limits,
agreeing with the lane's limits on the perturbation interval, for which the
actual upper readout (the hU field of F18) holds.  Choosing the canonical
extension is the only convention involved. -/
theorem exists_actualUpperReadout_of_endgamePressureData
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
    {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instEndgamePressureData : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (D : EndgamePressureData F μ ν hA hB hμA hνB P X Y u)
    {q m : ℕ} {W : Type*} {G Cb : ℝ} {hm : 0 < m}
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hpcid : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      D.pressureUpper f t = endgameUpperPressure_actual q m pc f t)
    (hL : LowerStationaryReadout D.pressureLower datum)
    (hscreen : StationaryScreening datum)
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * π c w) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      (∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
        |t| < D.radius f → pc' f t c = pc f t c) ∧
      ActualUpperReadout q m pc' datum :=
  ⟨upperPoolPressureExtension pc datum D.radius,
    fun f t c ht => upperPoolPressureExtension_eq_on_radius ht c,
    actualUpperReadout_of_endgamePressureData (hm := hm) hcomplete hX hY hXlaw hYlaw hφ D pc
      hpcid hL hscreen κ π hloc hK hP⟩

/-- **hU of the actual upper lane from its own data.**  This is the lane-level
form of the hU closure: everything except the frozen-readout identification hL,
the class screening Iw = I2 and the blockwise weak-duality data kappa, pi is the
lane's own input (the lower bundle and the upper localization family with its
population data).  The conclusion is the actual upper readout for the canonical
off-interval extension of the lane's local limits, which agrees with them on the
perturbation interval. -/
theorem actualUpperReadout_of_upperLane
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (lower : EndgameLowerFields F (physicalSourceProbability ωM ρ₀)
      (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (hu : let _instEndgameUpperLane : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    (hAB : Disjoint A B)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (q m : ℕ) (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F u q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c)
    (hrad : lower.radius = endgameUpperRadius_actual (A := A) (B := B))
    {W : Type*} {G Cb : ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (hL : LowerStationaryReadout lower.pressureLower datum)
    (hscreen : StationaryScreening datum)
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * π c w) :
    ActualUpperReadout q m
      (upperPoolPressureExtension pc datum lower.radius) datum := by
  exact actualUpperReadout_of_endgamePressureData (hm := hm) hcomplete hX hY hXlaw
    hYlaw hu
    (endgamePressureData_of_upperLane (F := F) ωM ρ₀ ρ₁ hA hB hμA hνB P X Y
      lower hcomplete hdim hu hAB hX hY hXi hYi hXlaw hYlaw hXY q m hm pc data hpc hrad)
    pc (fun _ _ => rfl) hL hscreen κ π hloc hK hP

end OTSelector.Reconstruction
