import OTSelector.Reconstruction.FinslerOriginalActualUpperReadoutProducer
import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationData

/-!
# The upper pool envelope: reduction to two named halves

This module attacks the named identity UpperPoolEnvelope q m pc datum introduced
in FinslerOriginalActualUpperReadoutProducer: for every probe f and tilt t, the
block weighted pool

  pool f t = sum over c : Fin q -> Fin m of (1 / m^q) * pc f t c

is a lower bound of the second-moment cost K w + t P w over the second-moment
class (datum f).C2, and the bound is attained at a class member.

## What the repo provides (the upper localization limits)

The repo proves the physical upper localization in family form
(PhysicalWeightedLocalizationFamily, FinslerOriginalWeightedUpperLocalizationData):
for every probe and tilt in the common interval, the expected physical supported
pressure is eventually at most the block weighted sum of the local marked
pressure limits pc plus any eps > 0.  The lane supplies pc through
PopData.hp (FinslerOriginalWeightedUpperLocalizationRestated: p c t is the limit
of markedScalePressure at top) and the localization theorem
physicalWeightedLocalizationFamily_of_popData.  Composing with the pool
unfolding, that is exactly the upper readout consumer field FinalProbUpperData
for pressureUpper = endgameUpperPressure_actual q m pc (theorem
finalProbUpperData_actualPool below).

This is the inequality pressure <= pool.  The envelope needs the OPPOSITE
comparison pool <= K w + t P w for every second-moment class member w, i.e. the
dual weak-duality bound of the physical upper limit against the cost of every
admissible second-moment matching.  No theorem in the repo states that
comparison: the localization limits are only compared with the physical
pressure, and the abstract StationaryPressureDatum carries no link between pc
and K, P.  This is the first missing input, named UpperPoolLowerBound.

## Attainment

StationaryPressureDatum.C2 is an abstract Set W: the structure carries no
topology, compactness, closedness or finite-dimensional structure on W, so no
compactness attainment argument is possible at this level of abstraction.  The
module proves:

* the finite-class criterion upperPoolReadoutAttained_of_finite (any finite
  second-moment class attains its infimum, via Set.exists_min_image), hence
  upperPoolEnvelope_of_finite: bridge + finite class implies the envelope;
* the singleton-class criterion upperPoolReadoutAttained_of_singletonClass;
* a concrete counterexample (posDatum) showing that the bridge/readout does NOT
  imply the envelope: C2 = (0, infinity), K = id, P = 0 has I2 = 0, which is not
  attained.  The zero pool equals that readout, so ActualUpperReadout holds while
  UpperPoolEnvelope fails.  Hence attainment is a genuinely independent input,
  not derivable from the upper localization limits.

## Exact remaining inputs for the actual lane

To obtain UpperPoolEnvelope q m pc datum it suffices (and, given the bridge, is
equivalent, theorem upperPoolEnvelope_iff_bridge_and_readoutAttained) to supply:

(a) UpperPoolLowerBound q m pc datum, equivalently for every f t the pool is at
    most (datum f).I2 t (theorem upperPoolLowerBound_iff_le_I2) - the dual
    weak-duality comparison, absent from the repo;
(b) UpperPoolReadoutAttained q m pc datum: for every f t some w in (datum f).C2
    has K w + t P w = (datum f).I2 t - the attainment / second-moment argument.

Then UpperPoolEnvelope follows and composes to ActualUpperReadout
(actualUpperReadout_of_halves).  Equivalently the bridge ActualUpperReadout plus
(b) already give the envelope.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability Module
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : ProbabilityMeasure M}

/-! ## 1. Splitting the envelope into two named halves -/

section Halves

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- **First half of the upper pool envelope**: the block weighted pool is a lower
bound of the second-moment cost over the whole second-moment class. -/
def UpperPoolLowerBound (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ) (w : W), w ∈ (datum f).C2 →
    endgameUpperPressure_actual q m pc f t ≤ (datum f).K w + t * (datum f).P w

/-- **Second half of the upper pool envelope**: the lower bound is attained at a
second-moment class member. -/
def UpperPoolAttainment (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), ∃ w ∈ (datum f).C2,
    (datum f).K w + t * (datum f).P w = endgameUpperPressure_actual q m pc f t

/-- Attainment of the second-moment stationary readout itself: for every probe and
tilt some class member realizes the value I2. -/
def UpperPoolReadoutAttained (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), ∃ w ∈ (datum f).C2,
    (datum f).K w + t * (datum f).P w = (datum f).I2 t

/-- The envelope is the conjunction of its two named halves. -/
theorem upperPoolEnvelope_iff_halves (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    UpperPoolEnvelope q m pc datum ↔
      UpperPoolLowerBound q m pc datum ∧ UpperPoolAttainment q m pc datum := by
  constructor
  · intro h
    exact ⟨fun f t w hw => (h f t).1 w hw, fun f t => (h f t).2⟩
  · rintro ⟨hl, ha⟩ f t
    exact ⟨hl f t, ha f t⟩

/-- **The lower-bound half is exactly the one-sided readout inequality**
pool <= I2.  The nontrivial direction compares the pool with the infimum over the
second-moment class; the converse uses that the infimum is below every class
value. -/
theorem upperPoolLowerBound_iff_le_I2 (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    UpperPoolLowerBound q m pc datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        endgameUpperPressure_actual q m pc f t ≤ (datum f).I2 t := by
  constructor
  · intro h f t
    apply le_csInf
      ((datum f).nonempty_C2.image (fun w => (datum f).K w + t * (datum f).P w))
    rintro z ⟨y, hy, rfl⟩
    exact h f t y hy
  · intro h f t w hw
    exact (h f t).trans (stationaryValue_le ((datum f).bddBelow_C2 t) hw)

/-- The bridge implies the lower-bound half. -/
theorem upperPoolLowerBound_of_actualUpperReadout (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h : ActualUpperReadout q m pc datum) :
    UpperPoolLowerBound q m pc datum :=
  fun f t w hw => actualUpperReadout_bound q m pc datum h f t hw

/-- Attainment of the envelope and attainment of the readout agree as soon as the
bridge holds. -/
theorem upperPoolAttainment_iff_readoutAttained_of_actualUpperReadout (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hbridge : ActualUpperReadout q m pc datum) :
    UpperPoolAttainment q m pc datum ↔ UpperPoolReadoutAttained q m pc datum := by
  constructor
  · intro h f t
    obtain ⟨w, hw, hwp⟩ := h f t
    exact ⟨w, hw, hwp.trans (hbridge f t)⟩
  · intro h f t
    obtain ⟨w, hw, hwI⟩ := h f t
    exact ⟨w, hw, by rw [hwI, hbridge f t]⟩

/-- **Characterization of the envelope**: given the repo-level bridge, the
envelope is exactly the attainment of the second-moment stationary readout.  This
isolates attainment as the only additional input beyond the bridge. -/
theorem upperPoolEnvelope_iff_bridge_and_readoutAttained (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    UpperPoolEnvelope q m pc datum ↔
      ActualUpperReadout q m pc datum ∧ UpperPoolReadoutAttained q m pc datum := by
  constructor
  · intro h
    have hbridge := actualUpperReadout_of_envelope q m pc datum h
    refine ⟨hbridge, ?_⟩
    intro f t
    obtain ⟨-, w, hw, hwp⟩ := h f t
    exact ⟨w, hw, hwp.trans (hbridge f t)⟩
  · rintro ⟨hbridge, hatt⟩
    refine (upperPoolEnvelope_iff_halves q m pc datum).mpr ⟨?_, ?_⟩
    · intro f t w hw
      rw [hbridge f t]
      exact stationaryValue_le ((datum f).bddBelow_C2 t) hw
    · intro f t
      obtain ⟨w, hw, hwI⟩ := hatt f t
      exact ⟨w, hw, by rw [hwI, hbridge f t]⟩

/-- **Composition to the readout**: the two halves give the bridge. -/
theorem actualUpperReadout_of_halves (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hl : UpperPoolLowerBound q m pc datum)
    (ha : UpperPoolAttainment q m pc datum) :
    ActualUpperReadout q m pc datum :=
  actualUpperReadout_of_envelope q m pc datum
    ((upperPoolEnvelope_iff_halves q m pc datum).mpr ⟨hl, ha⟩)

/-- **Composition to the readout from the bridge plus readout attainment.** -/
theorem actualUpperReadout_of_bridge_and_readoutAttained (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hbridge : ActualUpperReadout q m pc datum)
    (hatt : UpperPoolReadoutAttained q m pc datum) :
    UpperPoolEnvelope q m pc datum :=
  (upperPoolEnvelope_iff_bridge_and_readoutAttained q m pc datum).mpr
    ⟨hbridge, hatt⟩

end Halves

/-! ## 2. Attainment criteria available at the abstract level -/

section Attainment

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- **Finite-class attainment criterion.**  If every second-moment class is
finite, then the second-moment infimum is attained (the minimum of a nonempty
finite set of real values exists). -/
theorem upperPoolReadoutAttained_of_finite (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hfin : ∀ f : FinalProbeSpace A B, (datum f).C2.Finite) :
    UpperPoolReadoutAttained q m pc datum := by
  intro f t
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image (datum f).C2
    (fun w => (datum f).K w + t * (datum f).P w) (hfin f) (datum f).nonempty_C2
  refine ⟨w, hw, le_antisymm ?_ ?_⟩
  · apply le_csInf
      ((datum f).nonempty_C2.image (fun w => (datum f).K w + t * (datum f).P w))
    rintro z ⟨y, hy, rfl⟩
    exact hmin y hy
  · exact csInf_le ((datum f).bddBelow_C2 t) ⟨w, hw, rfl⟩

/-- **Finite-class envelope criterion**: the bridge plus a finite second-moment
class gives the envelope. -/
theorem upperPoolEnvelope_of_finite (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hbridge : ActualUpperReadout q m pc datum)
    (hfin : ∀ f : FinalProbeSpace A B, (datum f).C2.Finite) :
    UpperPoolEnvelope q m pc datum :=
  (upperPoolEnvelope_iff_bridge_and_readoutAttained q m pc datum).mpr
    ⟨hbridge, upperPoolReadoutAttained_of_finite q m pc datum hfin⟩

/-- **Singleton-class attainment criterion**: a singleton class attains its
infimum at its unique member. -/
theorem upperPoolReadoutAttained_of_singletonClass (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    {c : FinalProbeSpace A B → W} (hC2 : ∀ f, (datum f).C2 = {c f}) :
    UpperPoolReadoutAttained q m pc datum := by
  intro f t
  refine ⟨c f, ?_, ?_⟩
  · rw [hC2 f]
    exact Set.mem_singleton (c f)
  · rw [I2_eq_of_singletonClass q m pc datum hC2 f t]

end Attainment

/-! ## 3. What the upper localization limits give: the readout, not the envelope -/

section Localization

variable {W : Type*} {G Cb : ℝ}

/-- **The upper localization limits give the upper readout consumer field at the
weighted pool.**  From the repo physical upper localization family for the block
weights (as supplied by PopData.hp through
physicalWeightedLocalizationFamily_of_popData) and the pool unfolding, the
pressure upper field endgameUpperPressure_actual q m pc satisfies
FinalProbUpperData, i.e. the expected physical pressure is eventually bounded
above by the pool plus eps.

This is the inequality pressure <= pool.  It does not compare the pool with the
second-moment cost K + t P, so it does not give the envelope lower-bound half. -/
theorem finalProbUpperData_actualPool
    {A B : Set M} {hA : IsCompact A} {hB : IsCompact B}
    {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A} {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} {X Y : ∀ n, Fin (n + 1) → Ω n → M} {v : M → ℝ}
    {q m : ℕ} {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    {radius : FinalRadiusField A B}
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y v
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ))) (fun f t c => pc f t c) radius) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y v
      (endgameUpperPressure_actual q m pc) radius :=
  finalProbUpperData_actualLane q m radius hLoc (endgameUpperPressure_actual q m pc)
    (fun f t _ => endgameUpperPressure_actual_apply q m pc f t)

end Localization

/-! ## 4. A concrete counterexample: the bridge does not imply the envelope -/

section Counterexample

variable {A B : Set M}

/-- A second-moment datum on the positive half-line whose stationary values tend
to zero without attaining it: kinetic energy K x = x, probe P = 0, and both
classes the open half-line (0, infinity). -/
def posDatum : StationaryPressureDatum ℝ 1 1 where
  K := fun x => x
  P := fun _ => 0
  Cw := Set.Ioi (0 : ℝ)
  C2 := Set.Ioi (0 : ℝ)
  C2_subset_Cw := fun _ hx => hx
  kinetic_nonneg := fun w hw => le_of_lt hw
  probe_bound := fun w _ => by simp
  competitor := 1
  competitor_mem := by norm_num
  kinetic_competitor_le := by norm_num
  competitor2 := 1
  competitor2_mem := by norm_num
  kinetic_competitor2_le := by norm_num

/-- The second-moment stationary readout of posDatum vanishes. -/
theorem posDatum_I2 (t : ℝ) : posDatum.I2 t = 0 := by
  have himg : ((fun x : ℝ => posDatum.K x + t * posDatum.P x) '' posDatum.C2) =
      Set.Ioi (0 : ℝ) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [posDatum] using hx
    · intro hz
      exact ⟨z, by simpa [posDatum] using hz, by simp [posDatum]⟩
  show sInf ((fun x : ℝ => posDatum.K x + t * posDatum.P x) '' posDatum.C2) = 0
  rw [himg]
  apply le_antisymm
  · by_contra h
    rw [not_le] at h
    have hmem : sInf (Set.Ioi (0 : ℝ)) / 2 ∈ Set.Ioi (0 : ℝ) := by
      show 0 < sInf (Set.Ioi (0 : ℝ)) / 2
      linarith
    have hbdd : BddBelow (Set.Ioi (0 : ℝ)) := ⟨0, fun z hz => le_of_lt hz⟩
    have hle := csInf_le hbdd hmem
    linarith
  · apply le_csInf ⟨1, by norm_num⟩
    intro z hz
    exact le_of_lt hz

/-- The zero block pool: every local upper pressure limit vanishes. -/
def zeroPool {q m : ℕ} : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ :=
  fun _ _ _ => 0

/-- The zero pressure field. -/
def zeroField : FinalProbeSpace A B → ℝ → ℝ := fun _ _ => 0

/-- The zero block pool satisfies the bridge against posDatum. -/
theorem actualUpperReadout_posDatum {q m : ℕ} (hm : 0 < m) :
    ActualUpperReadout (A := A) (B := B) (W := ℝ) (G := 1) (Cb := 1) q m
      zeroPool (fun _ => posDatum) := by
  intro f t
  show endgameUpperPressure_actual (A := A) (B := B) q m zeroPool f t = posDatum.I2 t
  rw [endgameUpperPressure_actual_eq_of_constBlock (A := A) (B := B) hm zeroPool
    zeroField (by intro f t c; rfl) f t, posDatum_I2 t]
  rfl

/-- The envelope fails for posDatum: the readout value zero is not attained on the
open half-line. -/
theorem not_upperPoolEnvelope_posDatum {q m : ℕ} (hm : 0 < m)
    (f : FinalProbeSpace A B) :
    ¬ UpperPoolEnvelope (A := A) (B := B) (W := ℝ) (G := 1) (Cb := 1) q m
      zeroPool (fun _ => posDatum) := by
  intro h
  obtain ⟨-, w, hw, hval⟩ := h f 0
  have hpool : endgameUpperPressure_actual (A := A) (B := B) q m zeroPool f 0 = 0 := by
    rw [endgameUpperPressure_actual_eq_of_constBlock (A := A) (B := B) hm zeroPool
      zeroField (by intro f t c; rfl) f 0]
    rfl
  have hwpos : 0 < w := by simpa [posDatum] using hw
  have hval0 : w = 0 := by
    have hh := hval
    rw [hpool] at hh
    simpa [posDatum] using hh
  linarith

/-- **Attainment is a genuinely independent input**: there is a datum and a pool
realizing the bridge for which the envelope fails.  Thus the upper localization
limits (which supply the bridge side) cannot yield the envelope without an
additional attainment argument. -/
theorem exists_actualUpperReadout_not_upperPoolEnvelope [Nonempty (FinalProbeSpace A B)]
    {q m : ℕ} (hm : 0 < m) :
    ∃ datum : FinalProbeSpace A B → StationaryPressureDatum ℝ 1 1,
      ActualUpperReadout (A := A) (B := B) (W := ℝ) (G := 1) (Cb := 1) q m zeroPool datum ∧
      ¬ UpperPoolEnvelope (A := A) (B := B) (W := ℝ) (G := 1) (Cb := 1) q m zeroPool datum := by
  classical
  let f0 : FinalProbeSpace A B := Classical.arbitrary (FinalProbeSpace A B)
  exact ⟨fun _ => posDatum, actualUpperReadout_posDatum (q := q) (m := m) hm,
    not_upperPoolEnvelope_posDatum (q := q) (m := m) hm f0⟩

end Counterexample

end OTSelector.Reconstruction
