import OTSelector.Reconstruction.FinslerOriginalUpperShiftConvention
import OTSelector.Reconstruction.FinslerOriginalReadoutTiltDerivativeActual

/-!
# Producer for the actual upper readout bridge

This module unfolds and reduces the isolated upper readout bridge
ActualUpperReadout q m pc datum (FinslerOriginalUpperShiftConvention):
for all probes f and tilts t,

  endgameUpperPressure_actual q m pc f t = (datum f).I2 t.

## Unfolding both sides

* The actual upper pool is the block weighted sum of the local upper pressure
  limits: endgameUpperPressure_actual q m pc f t = sum over c : Fin q -> Fin m of
  (1 / m^q) * pc f t c (endgameUpperPressure_actual_apply).
* The second-moment stationary readout is the stationary value over the
  second-moment class: (datum f).I2 t = stationaryValue (datum f).K (datum f).P
  (datum f).C2 t, i.e. the infimum of K + t P over the class
  (stationaryPressureDatum_I2_apply, actualUpperReadout_iff_stationaryValue).

So the bridge is NOT definitional: the weighted pool is a finite block average
while I2 is an infimum over the second-moment class of matchings.  The paper
closes the gap by the upper-envelope construction: the weighted pool is the
stationary upper envelope, i.e. a lower bound of K + t P on the class that is
attained there.  That identity is isolated as the named predicate
UpperPoolEnvelope with a precise type, and actualUpperReadout_of_envelope proves
that it implies the bridge.  The bound half is conversely extracted from the
bridge (actualUpperReadout_bound).  The envelope identity is genuinely extra
content: the stationary value need not be attained in general, so the bridge
does not follow from the bound alone.

## Special cases reduced to the localization limit data

* Constant block pool (single-valued pool, in particular a subsingleton block
  index such as m = 1): the pool is that single value
  (endgameUpperPressure_actual_eq_of_constBlock), and the bridge reduces to the
  single identity pool = I2 (actualUpperReadout_of_constBlock,
  actualUpperReadout_of_subsingletonIndex).
* Singleton second-moment class: I2 is the affine readout K c + t P c of the
  realized competitor (I2_eq_of_singletonClass), so the bridge is equivalent to
  the affine identity pool = K c + t P c
  (actualUpperReadout_iff_singletonClass), and the envelope identity is
  equivalent to the same equation (upperPoolEnvelope_iff_singletonClass).
* Pool realized by the competitor of a singleton class together with a
  constant block pool: bridge proved outright
  (actualUpperReadout_of_singletonClass_and_constBlock).

## Nonemptiness witnesses

For any probe-indexed coefficients a b satisfying 0 <= a f, |b f| <= G and
a f <= Cb, the affine singleton-class datum affineSingletonDatum a b has
I2 t = a f + t b f; hence an affine block pool pc f t c = a f + t b f satisfies
the bridge (exists_actualUpperReadout_of_affineBlock).  The zero pool case is
recorded concretely (exists_actualUpperReadout_zeroPool).

## Exact remaining input for the actual lane

For the concrete lane one must supply UpperPoolEnvelope qU mU pc datum: for every
probe f and tilt t, the weighted pool endgameUpperPressure_actual qU mU pc f t is
a lower bound of K + t P over the second-moment class (datum f).C2 and is
attained at some class member.  In paper terms this is the upper-envelope
identification of the block weighted pool with the stationary upper pressure;
the repo currently provides only the marked pressure localization limits pc, not
their identification with stationary values.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability Module
open scoped ContDiff Topology ENNReal NNReal BigOperators CompactlySupported BoundedContinuousFunction

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
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## 1. Unfolding both sides of the bridge -/

section Unfold

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The actual upper lane pool, unfolded: the block weighted sum of the local
upper pressure limits with weight 1 / m^q. -/
theorem endgameUpperPressure_actual_apply (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (f : FinalProbeSpace A B) (t : ℝ) :
    endgameUpperPressure_actual q m pc f t =
      ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c :=
  rfl

/-- The second-moment stationary readout, unfolded: the stationary value over the
second-moment class. -/
theorem stationaryPressureDatum_I2_apply (D : StationaryPressureDatum W G Cb) (t : ℝ) :
    D.I2 t = stationaryValue D.K D.P D.C2 t :=
  rfl

/-- The bridge unfolded through the stationary value: the weighted pool equals the
infimum of K + t P over the second-moment class. -/
theorem actualUpperReadout_iff_stationaryValue (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) :
    ActualUpperReadout q m pc datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        endgameUpperPressure_actual q m pc f t =
          stationaryValue (datum f).K (datum f).P (datum f).C2 t :=
  actualUpperReadout_iff q m pc datum

/-- The bound half extracted from the bridge: the weighted pool is below every
value K + t P of the second-moment class. -/
theorem actualUpperReadout_bound (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h : ActualUpperReadout q m pc datum)
    (f : FinalProbeSpace A B) (t : ℝ) {w : W} (hw : w ∈ (datum f).C2) :
    endgameUpperPressure_actual q m pc f t ≤ (datum f).K w + t * (datum f).P w := by
  rw [h f t]
  exact stationaryValue_le ((datum f).bddBelow_C2 t) hw

end Unfold

/-! ## 2. The isolated upper-envelope identity -/

section Envelope

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- **The upper-envelope identity** behind the bridge: for every probe and tilt the
weighted pool is a lower bound of K + t P over the second-moment class and is
attained at a class member.  This is the paper's statement that the block weighted
upper pool is the stationary upper envelope; it implies the bridge
(actualUpperReadout_of_envelope). -/
def UpperPoolEnvelope (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ),
    (∀ w ∈ (datum f).C2,
      endgameUpperPressure_actual q m pc f t ≤ (datum f).K w + t * (datum f).P w) ∧
    ∃ w ∈ (datum f).C2,
      (datum f).K w + t * (datum f).P w = endgameUpperPressure_actual q m pc f t

/-- **The upper-envelope identity implies the bridge.**  A lower bound of the class
that is attained is the infimum, hence the stationary value. -/
theorem actualUpperReadout_of_envelope (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h : UpperPoolEnvelope q m pc datum) :
    ActualUpperReadout q m pc datum := by
  intro f t
  obtain ⟨hle, w, hw, hattain⟩ := h f t
  have hbdd : BddBelow ((fun w => (datum f).K w + t * (datum f).P w) '' (datum f).C2) :=
    (datum f).bddBelow_C2 t
  apply le_antisymm
  · apply le_csInf ((datum f).nonempty_C2.image (fun w => (datum f).K w + t * (datum f).P w))
    rintro z ⟨y, hy, rfl⟩
    exact hle y hy
  · calc stationaryValue (datum f).K (datum f).P (datum f).C2 t
        ≤ (datum f).K w + t * (datum f).P w := csInf_le hbdd ⟨w, hw, rfl⟩
      _ = endgameUpperPressure_actual q m pc f t := hattain

/-- In the singleton second-moment class case the second-moment readout is the
affine readout of the realized competitor. -/
theorem I2_eq_of_singletonClass (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    {c : FinalProbeSpace A B → W} (hC2 : ∀ f, (datum f).C2 = {c f})
    (f : FinalProbeSpace A B) (t : ℝ) :
    (datum f).I2 t = (datum f).K (c f) + t * (datum f).P (c f) := by
  rw [stationaryPressureDatum_I2_apply, hC2 f]
  exact stationaryValue_singleton (datum f).K (datum f).P (c f) t

/-- **Singleton second-moment class reduction**: the bridge is equivalent to the
affine identity pool = K c + t P c. -/
theorem actualUpperReadout_iff_singletonClass (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    {c : FinalProbeSpace A B → W} (hC2 : ∀ f, (datum f).C2 = {c f}) :
    ActualUpperReadout q m pc datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        endgameUpperPressure_actual q m pc f t =
          (datum f).K (c f) + t * (datum f).P (c f) := by
  constructor
  · intro h f t
    rw [h f t, I2_eq_of_singletonClass q m pc datum hC2 f t]
  · intro h f t
    rw [h f t, I2_eq_of_singletonClass q m pc datum hC2 f t]

/-- **Singleton second-moment class reduction of the envelope identity**: it is
equivalent to the affine identity pool = K c + t P c. -/
theorem upperPoolEnvelope_iff_singletonClass (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    {c : FinalProbeSpace A B → W} (hC2 : ∀ f, (datum f).C2 = {c f}) :
    UpperPoolEnvelope q m pc datum ↔
      ∀ (f : FinalProbeSpace A B) (t : ℝ),
        endgameUpperPressure_actual q m pc f t =
          (datum f).K (c f) + t * (datum f).P (c f) := by
  constructor
  · intro h f t
    obtain ⟨-, w, hw, hattain⟩ := h f t
    rw [hC2 f, Set.mem_singleton_iff] at hw
    subst hw
    exact hattain.symm
  · intro h f t
    refine ⟨?_, c f, ?_, ?_⟩
    · intro w hw
      rw [hC2 f, Set.mem_singleton_iff] at hw
      subst hw
      exact le_of_eq (h f t)
    · rw [hC2 f]
      exact Set.mem_singleton (c f)
    · exact (h f t).symm

end Envelope

/-! ## 3. Constant block pools and the single-atom reduction -/

section ConstantBlock

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The block weights sum to one. -/
theorem sum_blockWeight_eq_one {q m : ℕ} (hm : 0 < m) :
    (∑ _c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ)))) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [mul_one_div, div_self]
  exact_mod_cast pow_ne_zero q (Nat.pos_iff_ne_zero.mp hm)

/-- Multiplying the block weights into a constant sums to the constant. -/
theorem sum_blockWeight_mul {q m : ℕ} (hm : 0 < m) (X : ℝ) :
    (∑ _c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * X) = X := by
  rw [← Finset.sum_mul, sum_blockWeight_eq_one hm, one_mul]

/-- A pool that is constant in the block index gives the constant as actual upper
pool. -/
theorem endgameUpperPressure_actual_eq_of_constBlock {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (X : FinalProbeSpace A B → ℝ → ℝ)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m), pc f t c = X f t)
    (f : FinalProbeSpace A B) (t : ℝ) :
    endgameUpperPressure_actual q m pc f t = X f t := by
  rw [endgameUpperPressure_actual_apply]
  calc (∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c)
      = ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * X f t := by
        refine Finset.sum_congr rfl ?_
        intro c _
        rw [hpc f t c]
    _ = X f t := sum_blockWeight_mul hm (X f t)

/-- **Constant block pool reduction**: if the pool is the fixed readout X and X
equals I2 of the datum, the bridge holds. -/
theorem actualUpperReadout_of_constBlock {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (X : FinalProbeSpace A B → ℝ → ℝ)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m), pc f t c = X f t)
    (hX : ∀ (f : FinalProbeSpace A B) (t : ℝ), X f t = (datum f).I2 t) :
    ActualUpperReadout q m pc datum := by
  intro f t
  rw [endgameUpperPressure_actual_eq_of_constBlock hm pc X hpc f t, hX f t]

/-- **Single-atom (subsingleton block index) reduction**: if the block index has a
single element the pool is a single value, and the bridge reduces to the identity
of that value with I2. -/
theorem actualUpperReadout_of_subsingletonIndex {q m : ℕ} (hm : 0 < m)
    [Subsingleton (Fin q → Fin m)] (c0 : Fin q → Fin m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (h : ∀ (f : FinalProbeSpace A B) (t : ℝ), pc f t c0 = (datum f).I2 t) :
    ActualUpperReadout q m pc datum := by
  have hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
      pc f t c = pc f t c0 := by
    intro f t c
    rw [Subsingleton.elim c c0]
  exact actualUpperReadout_of_constBlock hm pc datum (fun f t => pc f t c0) hpc h

end ConstantBlock

/-! ## 4. Nonemptiness: singleton-class witnesses for affine pools -/

section Witness

variable {A B : Set M} {W : Type*} {G Cb : ℝ}

/-- The affine singleton-class datum: for each probe the second-moment class is the
single matching carrying kinetic energy a f and probe b f, so I2 is the affine
readout a f + t b f. -/
noncomputable def affineSingletonDatum (a b : FinalProbeSpace A B → ℝ)
    {G Cb : ℝ} (ha : ∀ f, 0 ≤ a f) (hb : ∀ f, |b f| ≤ G) (hab : ∀ f, a f ≤ Cb) :
    FinalProbeSpace A B → StationaryPressureDatum (FinalProbeSpace A B × ℝ × ℝ) G Cb :=
  fun f =>
    { K := fun w => w.2.1
      P := fun w => w.2.2
      Cw := {(f, a f, b f)}
      C2 := {(f, a f, b f)}
      C2_subset_Cw := by
        intro w hw
        exact hw
      kinetic_nonneg := by
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ha f
      probe_bound := by
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact hb f
      competitor := (f, a f, b f)
      competitor_mem := by
        rw [Set.mem_singleton_iff]
      kinetic_competitor_le := hab f
      competitor2 := (f, a f, b f)
      competitor2_mem := by
        rw [Set.mem_singleton_iff]
      kinetic_competitor2_le := hab f }

/-- The second-moment readout of the affine singleton-class datum is affine. -/
theorem affineSingletonDatum_I2 (a b : FinalProbeSpace A B → ℝ)
    {G Cb : ℝ} (ha : ∀ f, 0 ≤ a f) (hb : ∀ f, |b f| ≤ G) (hab : ∀ f, a f ≤ Cb)
    (f : FinalProbeSpace A B) (t : ℝ) :
    (affineSingletonDatum a b ha hb hab f).I2 t = a f + t * b f := by
  rw [stationaryPressureDatum_I2_apply]
  rw [show (affineSingletonDatum a b ha hb hab f).C2 = {(f, a f, b f)} from rfl]
  rw [stationaryValue_singleton]
  rfl

/-- **Nonemptiness of the bridge for an affine block pool.**  If the pool is constant
in the block index and affine in the tilt with probe-dependent coefficients
a f + t b f, and the coefficients satisfy the kinetic nonnegativity, probe bound
and competitor bound, then the affine singleton-class datum realizes the bridge. -/
theorem exists_actualUpperReadout_of_affineBlock {q m : ℕ} (hm : 0 < m)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (a b : FinalProbeSpace A B → ℝ) {G Cb : ℝ}
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
      pc f t c = a f + t * b f)
    (ha : ∀ f, 0 ≤ a f) (hb : ∀ f, |b f| ≤ G) (hab : ∀ f, a f ≤ Cb) :
    ∃ datum : FinalProbeSpace A B → StationaryPressureDatum (FinalProbeSpace A B × ℝ × ℝ) G Cb,
      ActualUpperReadout q m pc datum := by
  refine ⟨affineSingletonDatum a b ha hb hab, ?_⟩
  intro f t
  rw [endgameUpperPressure_actual_eq_of_constBlock hm pc (fun f t => a f + t * b f) hpc f t,
    affineSingletonDatum_I2 a b ha hb hab f t]

/-- The zero datum: a singleton second-moment class at matching (f, 0, 0). -/
noncomputable def zeroSingletonDatum : FinalProbeSpace A B →
    StationaryPressureDatum (FinalProbeSpace A B × ℝ × ℝ) 0 0 :=
  affineSingletonDatum (G := 0) (Cb := 0) (fun _ => 0) (fun _ => 0)
    (by intro f; exact le_refl 0) (by intro f; simp) (by intro f; exact le_refl 0)

/-- The second-moment readout of the zero datum vanishes. -/
theorem zeroSingletonDatum_I2 (f : FinalProbeSpace A B) (t : ℝ) :
    (zeroSingletonDatum (A := A) (B := B) f).I2 t = 0 := by
  rw [stationaryPressureDatum_I2_apply]
  rw [show (zeroSingletonDatum (A := A) (B := B) f).C2 =
    {(f, (0 : ℝ), (0 : ℝ))} from rfl]
  rw [stationaryValue_singleton]
  show (0 : ℝ) + t * 0 = 0
  ring

/-- **Nonemptiness in the concrete zero-pool case.** -/
theorem exists_actualUpperReadout_zeroPool {q m : ℕ} (hm : 0 < m) :
    ∃ datum : FinalProbeSpace A B → StationaryPressureDatum (FinalProbeSpace A B × ℝ × ℝ) 0 0,
      ActualUpperReadout q m (fun _ _ _ => (0 : ℝ)) datum := by
  refine ⟨zeroSingletonDatum, ?_⟩
  intro f t
  rw [endgameUpperPressure_actual_eq_of_constBlock hm (fun _ _ _ => (0 : ℝ))
    (fun _ _ => (0 : ℝ)) (by intro f t c; rfl) f t,
    zeroSingletonDatum_I2 f t]

end Witness

end OTSelector.Reconstruction
