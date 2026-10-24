import OTSelector.Reconstruction.FinslerOriginalUpperPoolEnvelope
import OTSelector.Reconstruction.FinslerCampbellLowerAssembly

/-!
# Upper pool duality: infimum direction, weak duality and the corrected input

This module continues the upper stationary lane (F18).  It reconciles the
direction of the upper stationary readout with the paper, splits the upper pool
bridge into its two halves, proves the lower-bound half from blockwise weak
duality plus a block decomposition of the competitor cost, and records the
corrected typed input of the actual upper readout producer.

## Direction: the paper's upper stationary readout is an infimum

In main.tex, Definition general-gluing-two-classes, both stationary pressures
are infima over their competitor classes: I_{j,w}(z,v) is the infimum of the
stationary source-Palm cost over stationary forward perfect matchings with
finite weighted kinetic mean, and I_{j,2}(z,v) is the same infimum with the
additional condition E^S |D|^2 < infinity, i.e. over the second-moment class
C_2.  The same definition records I_{j,w} <= I_{j,2}: the second-moment infimum
is the larger of the two stationary pressures.  The word "upper" in the upper
lane refers to this ordering between two infima and NOT to a supremum over the
competitor class.  The scalar endgame version (label degenerate-scalar-pressure)
is the displayed infimum

  I_2(t) = inf_{P in C_2} E^S_P[k + t g].

The repository agrees definitionally: stationaryValue is sInf of the cost image
(StationaryPressureClasses), StationaryPressureDatum.I2 is that infimum over C2,
and for the stationary forward matching datum stationaryForwardDatum the value
is secondMomentStationaryPressure (stationaryForwardDatum_I2), which is by
definition the infimum over secondMomentClass.  Consequently the producer's
bridge direction is correct: the lower-bound half of the bridge keeps the form
pool <= K w + t P w for every w in C2, and no direction restatement is needed.
The lemma sup_version_reverses_direction records what would have changed had
the readout been a supremum instead.

## Which half of the bridge is a paper identity

The bridge ActualUpperReadout (pool = I2) splits into

* UpperPoolLowerBound (pool <= K w + t P w for every competitor w in C2),
  equivalently pool <= I2 (upperPoolLowerBound_iff_le_I2), and
* UpperPoolReverseBound (I2 <= pool).

The lower-bound half is a paper identity: it follows by weak duality (an infimum
is at most every competitor cost, I2_le_competitor) together with the block
structure of the pool.  Concretely, the pool is the block weighted sum of local
upper pressure limits; each local limit is at most the local assignment value of
every local competitor (local weak duality), and the global competitor cost is
the same block weighted sum of local assignment values
(upperPoolLowerBound_of_localReadout).  No attainment is used.

The reverse half is the upper localization identity of the paper: the physical
pressure is bounded above by both I2 and the pool, hence I2 <= pool.  It is kept
here as the single named typed input UpperPoolReverseBound.  It is strictly
weaker than attainment: attainment of the envelope implies the reverse bound
(upperPoolReverseBound_of_attainment), but not conversely.

The stronger upper pool envelope additionally requires the infimum to be
attained (UpperPoolReadoutAttained).  Attainment is not needed for the bridge
ActualUpperReadout, and the counterexample of the previous module shows that the
bridge does not imply the envelope.  The corrected producer input is therefore
UpperPoolLowerBound (proved here from blockwise weak duality) together with
UpperPoolReverseBound, and the equivalence with ActualUpperReadout is
actualUpperReadout_iff_lowerBound_and_reverseBound.  Composition:
actualUpperReadout_of_blockwiseWeakDuality_and_reverseBound.

## The paper's class-level weak duality in the repository

For the paper's second-moment class, secondMomentStationaryPressure is the
infimum over secondMomentClass, and
secondMomentStationaryPressure_le_matchingCost proves that it is at most the
kinetic-plus-probe cost of every second-moment matching.  The weighted-class
analogue is already in FinslerCampbellLowerAssembly
(weightedStationaryPressure_le_matchingCost).

## Exact remaining gap

To obtain ActualUpperReadout for the actual lane it now suffices to supply the
single one-sided inequality UpperPoolReverseBound q m pc datum, i.e. I2 <= pool
for every probe and tilt; the lower-bound half is proved here.  For the stronger
envelope one additionally needs UpperPoolReadoutAttained.  Nothing else is
missing at this interface.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability Module
open OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
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

/-! ## 1. Direction of the upper stationary readout -/

section Direction

variable {W : Type*} {G Cb : ℝ}

/-- The second-moment readout is the infimum of the stationary cost over the
second-moment class, i.e. the paper's I_2. -/
theorem I2_eq_sInf (D : StationaryPressureDatum W G Cb) (t : ℝ) :
    D.I2 t = sInf ((fun w => D.K w + t * D.P w) '' D.C2) :=
  stationaryPressureDatum_I2_apply D t

/-- Weak duality: the second-moment infimum is at most the cost of every
competitor in the second-moment class. -/
theorem I2_le_competitor (D : StationaryPressureDatum W G Cb) (t : ℝ) {w : W}
    (hw : w ∈ D.C2) :
    D.I2 t ≤ D.K w + t * D.P w :=
  stationaryValue_le (D.bddBelow_C2 t) hw

/-- Infimum direction: a constant is below an infimum exactly when it is below
every member.  This is the direction used by the lower-bound half of the
bridge. -/
theorem inf_version_direction {s : Set ℝ} (hb : BddBelow s) (hs : s.Nonempty) {a : ℝ} :
    a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b := by
  constructor
  · intro h b hb'
    exact h.trans (csInf_le hb hb')
  · intro h
    exact le_csInf hs h

/-- Supremum direction: a constant bounds a supremum from above exactly when it
bounds every member from above.  If the upper stationary readout were a
supremum over the competitor class, the lower-bound half of the bridge would
have the opposite direction (competitor cost <= pool).  The paper's I_2 is an
infimum, so this alternative does not apply. -/
theorem sup_version_reverses_direction {s : Set ℝ} (hb : BddAbove s) (hs : s.Nonempty)
    {a : ℝ} :
    sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  csSup_le_iff hb hs

end Direction

/-! ## 2. The two halves of the bridge -/

section Halves

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- Reverse half of the bridge: the second-moment readout is at most the block
weighted pool.  This is the one-sided inequality supplied by the paper's upper
localization; it is weaker than attainment. -/
def UpperPoolReverseBound (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ),
    (datum f).I2 t ≤ endgameUpperPressure_actual q m pc f t

/-- The bridge decomposes exactly into the lower-bound half and the reverse
bound. -/
theorem actualUpperReadout_iff_lowerBound_and_reverseBound (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ActualUpperReadout q m pc datum ↔
      UpperPoolLowerBound q m pc datum ∧ UpperPoolReverseBound q m pc datum := by
  constructor
  · intro h
    exact ⟨upperPoolLowerBound_of_actualUpperReadout q m pc datum h,
      fun f t => le_of_eq (h f t).symm⟩
  · rintro ⟨hl, hr⟩ f t
    exact le_antisymm ((upperPoolLowerBound_iff_le_I2 q m pc datum).mp hl f t) (hr f t)

/-- The corrected producer input, first form: the two named halves give the
bridge. -/
theorem actualUpperReadout_of_lowerBound_and_reverseBound (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hl : UpperPoolLowerBound q m pc datum)
    (hr : UpperPoolReverseBound q m pc datum) :
    ActualUpperReadout q m pc datum :=
  (actualUpperReadout_iff_lowerBound_and_reverseBound q m pc datum).mpr ⟨hl, hr⟩

/-- The bridge gives the reverse bound. -/
theorem upperPoolReverseBound_of_actualUpperReadout (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h : ActualUpperReadout q m pc datum) :
    UpperPoolReverseBound q m pc datum :=
  fun f t => le_of_eq (h f t).symm

/-- Attainment implies the reverse bound: the infimum is below the attained
value of the pool. -/
theorem upperPoolReverseBound_of_attainment (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (ha : UpperPoolAttainment q m pc datum) :
    UpperPoolReverseBound q m pc datum := by
  intro f t
  obtain ⟨w, hw, hwp⟩ := ha f t
  rw [← hwp]
  exact csInf_le ((datum f).bddBelow_C2 t) ⟨w, hw, rfl⟩

/-- Full split of the envelope: envelope is the lower-bound half, the reverse
bound and the attainment of the second-moment readout.  This records exactly
which conjuncts are paper identities and which is the attainment input. -/
theorem upperPoolEnvelope_iff_lowerBound_and_reverseBound_and_readoutAttained (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    UpperPoolEnvelope q m pc datum ↔
      UpperPoolLowerBound q m pc datum ∧ UpperPoolReverseBound q m pc datum ∧
        UpperPoolReadoutAttained q m pc datum := by
  constructor
  · intro h
    obtain ⟨hbridge, hatt⟩ :=
      (upperPoolEnvelope_iff_bridge_and_readoutAttained q m pc datum).mp h
    obtain ⟨hl, hr⟩ :=
      (actualUpperReadout_iff_lowerBound_and_reverseBound q m pc datum).mp hbridge
    exact ⟨hl, hr, hatt⟩
  · rintro ⟨hl, hr, hatt⟩
    exact (upperPoolEnvelope_iff_bridge_and_readoutAttained q m pc datum).mpr
      ⟨(actualUpperReadout_iff_lowerBound_and_reverseBound q m pc datum).mpr ⟨hl, hr⟩,
        hatt⟩

end Halves

/-! ## 3. The lower-bound half from blockwise weak duality -/

section Blockwise

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- Positivity of the block weight 1 / m^q. -/
theorem blockWeight_pos {q m : ℕ} (hm : 0 < m) :
    (0 : ℝ) < 1 / (((m ^ q : ℕ) : ℝ)) := by
  have hmq : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by
    exact_mod_cast pow_pos hm q
  exact one_div_pos.mpr hmq

/-- The block weighted sum distributes over the affine competitor cost. -/
theorem sum_blockWeight_mul_add {q m : ℕ}
    (κ π : (Fin q → Fin m) → ℝ) (t : ℝ) :
    (∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * (κ c + t * π c)) =
      (∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * κ c) +
        t * (∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * π c) := by
  have h1 : ∀ c : Fin q → Fin m,
      (1 / (((m ^ q : ℕ) : ℝ))) * (κ c + t * π c) =
        (1 / (((m ^ q : ℕ) : ℝ))) * κ c +
          t * ((1 / (((m ^ q : ℕ) : ℝ))) * π c) :=
    fun c => by ring
  simp only [h1, Finset.sum_add_distrib]
  rw [Finset.mul_sum]

/-- The lower-bound half of the bridge from blockwise weak duality.  The pool is
the block weighted sum of the local upper pressure limits.  If each local limit
is at most the local assignment value of every competitor in the local class,
and the global competitor cost is the same block weighted sum of local
assignment values, then the pool is a lower bound of the global competitor cost
over the second-moment class.  Both hypotheses are paper identities of the
localized upper pressure; no attainment is involved. -/
theorem upperPoolLowerBound_of_blockwiseWeakDuality {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * π c w) :
    UpperPoolLowerBound q m pc datum := by
  intro f t w hw
  rw [endgameUpperPressure_actual_apply]
  have hcost : (datum f).K w + t * (datum f).P w =
      ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * (κ c w + t * π c w) := by
    rw [hK f w hw, hP f w hw]
    exact (sum_blockWeight_mul_add (κ := fun c => κ c w) (π := fun c => π c w) t).symm
  rw [hcost]
  exact Finset.sum_le_sum (fun c _ =>
    mul_le_mul_of_nonneg_left (hloc f t c w hw) (le_of_lt (blockWeight_pos hm)))

/-- Local readout form of the lower-bound half.  If every local pool entry is
the local second-moment stationry value (the local upper readout identity), then
local weak duality bounds it by the local assignment value of every competitor,
and the block decomposition gives the lower-bound half.  This is the form in
which the paper's per-block pressure identity feeds the global bound; no
attainment is used. -/
theorem upperPoolLowerBound_of_localReadout {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (κ π : (Fin q → Fin m) → W → ℝ)
    {Wl : Type*} {Gl Cbl : ℝ}
    (Dloc : (Fin q → Fin m) → StationaryPressureDatum Wl Gl Cbl)
    (embed : (Fin q → Fin m) → W → Wl)
    (hread : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
      pc f t c = (Dloc c).I2 t)
    (hmem : ∀ (f : FinalProbeSpace A B) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → embed c w ∈ (Dloc c).C2)
    (hval : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 →
        (Dloc c).K (embed c w) + t * (Dloc c).P (embed c w) = κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * π c w) :
    UpperPoolLowerBound q m pc datum :=
  upperPoolLowerBound_of_blockwiseWeakDuality hm pc datum κ π
    (fun f t c w hw => by
      rw [hread f t c, ← hval f t c w hw]
      exact I2_le_competitor (Dloc c) t (hmem f c w hw))
    hK hP

/-- The corrected producer input, composed: blockwise weak duality gives the
lower-bound half and the reverse bound gives the rest, hence the bridge.  The
only named input is UpperPoolReverseBound. -/
theorem actualUpperReadout_of_blockwiseWeakDuality_and_reverseBound {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * π c w)
    (hr : UpperPoolReverseBound q m pc datum) :
    ActualUpperReadout q m pc datum :=
  actualUpperReadout_of_lowerBound_and_reverseBound q m pc datum
    (upperPoolLowerBound_of_blockwiseWeakDuality hm pc datum κ π hloc hK hP) hr

/-- Envelope form of the blockwise route: weak duality plus attainment gives the
envelope, hence also the bridge.  This is the stronger route that needs the
attainment input. -/
theorem upperPoolEnvelope_of_blockwiseWeakDuality_and_attainment {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * π c w)
    (ha : UpperPoolAttainment q m pc datum) :
    UpperPoolEnvelope q m pc datum :=
  (upperPoolEnvelope_iff_halves q m pc datum).mpr
    ⟨upperPoolLowerBound_of_blockwiseWeakDuality hm pc datum κ π hloc hK hP, ha⟩

/-- Readout form of the blockwise plus attainment route. -/
theorem actualUpperReadout_of_blockwiseWeakDuality_and_attainment {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * π c w)
    (ha : UpperPoolAttainment q m pc datum) :
    ActualUpperReadout q m pc datum :=
  actualUpperReadout_of_envelope q m pc datum
    (upperPoolEnvelope_of_blockwiseWeakDuality_and_attainment hm pc datum κ π hloc hK hP ha)

end Blockwise

/-! ## 4. The paper's class-level weak duality for stationary forward matchings -/

section ForwardMatching

variable {α β : Measure UnitMark}

/-- The paper's second-moment upper pressure is the infimum over the
second-moment class (Definition general-gluing-two-classes). -/
theorem secondMomentStationaryPressure_eq_sInf {A : ℝ → ℝ → ℝ}
    {f : MarkedCloudPoint → MarkedCloudPoint → ℝ} (v : ℝ) :
    secondMomentStationaryPressure α β A f v =
      sInf ((fun M => palmKinetic A M + v * palmProbe f M) '' secondMomentClass α β) :=
  rfl

/-- Weak duality for the second-moment stationary class.  The second-moment
upper pressure is at most the kinetic-plus-probe cost of every stationary
forward matching with finite second moment.  This is the paper identity that
feeds the lower-bound half of the bridge. -/
theorem secondMomentStationaryPressure_le_matchingCost {A : ℝ → ℝ → ℝ}
    {f : MarkedCloudPoint → MarkedCloudPoint → ℝ} {G : ℝ}
    (hA_nonneg : ∀ a b, 0 ≤ A a b)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    {M : StationaryForwardMatching α β} (hM : FiniteSecondMoment M) (v : ℝ) :
    secondMomentStationaryPressure α β A f v ≤ palmKinetic A M + v * palmProbe f M := by
  unfold secondMomentStationaryPressure
  have hbdd : BddBelow ((fun c : StationaryForwardMatching α β =>
      palmKinetic A c + v * palmProbe f c) '' secondMomentClass α β) :=
    bddBelow_stationaryValue (G := G) (v := v)
      (fun c _ => palmKinetic_nonneg hA_nonneg c)
      (fun c _ => abs_palmProbe_le hf hfG c)
  have hmem : M ∈ secondMomentClass α β := by
    simpa only [secondMomentClass, Set.mem_ofPred_eq] using hM
  exact stationaryValue_le hbdd hmem

end ForwardMatching

end OTSelector.Reconstruction
