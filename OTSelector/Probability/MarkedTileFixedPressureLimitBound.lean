import OTSelector.Probability.MarkedTilePressureLimitBound
import OTSelector.Probability.MarkedDePoissonization

/-!
# The fixed-sample-size finite-tile pressure bound

De-Poissonization transfers the sharp finite-tile scale bound to the actual
iid marked cube model with fixed sample size `n`.  This is the form needed by
the physical semidiscrete mean, whose target cloud has a deterministic number
of points.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {C A B : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace A] [MeasurableSpace B]

/-- **Fixed-size finite-tile pressure limit.**  For a finite family of tiles with
weights `w`, the iid fixed-sample-size pressure of the encoded model converges
to the same limit as the Poissonized scale pressure, and that limit is at most
the weighted sum of the local limits. -/
theorem exists_markedFixedPressure_limit_tile_le_sum
    (q : ℕ) (hq : 4 < q)
    {w : C → ℝ≥0} (hw : ∑ c, w c = 1)
    {kin : C → A → B → (Fin q → ℝ) → ℝ} {g : C → A → B → ℝ}
    {Cb G Kcross : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G) (hK0 : 0 ≤ Kcross)
    (hkin_meas : Measurable (fun p : C × A × B × (Fin q → ℝ) =>
      kin p.1 p.2.1 p.2.2.1 p.2.2.2))
    (hkin_nonneg : ∀ c a b v, 0 ≤ kin c a b v)
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hkin_homog : ∀ c a b (s : ℝ), 0 ≤ s → ∀ v : Fin q → ℝ,
      kin c a b (fun l => s * v l) = s ^ 2 * kin c a b v)
    (hg_meas : Measurable (fun p : C × A × B => g p.1 p.2.1 p.2.2))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : C → Measure A) [∀ c, IsProbabilityMeasure (α c)]
    (β : C → Measure B) [∀ c, IsProbabilityMeasure (β c)]
    [IsProbabilityMeasure (mixtureMarkLaw w α)]
    [IsProbabilityMeasure (mixtureMarkLaw w β)]
    (p : C → ℝ → ℝ)
    (hp : ∀ (c : C) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A B (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t))) :
    ∃ pglobal : ℝ → ℝ,
      (∀ t, Tendsto (fun n : ℕ =>
        (∫ ω : TwoMarkedCloudSpace q (C × A) (C × B),
          markedFixedValue q (n : ℝ) t (tileKin q w kin Kcross) (tileProbe g) n ω
            ∂(twoMarkedCloudLaw q (C × A) (C × B)
              (mixtureMarkLaw w α) (mixtureMarkLaw w β) (n : ℝ≥0))) / (n : ℝ))
        atTop (𝓝 (pglobal t))) ∧
      (∀ t, pglobal t ≤ ∑ c : C, (w c : ℝ) * p c t) := by
  classical
  obtain ⟨pglobal, hpg, hbound⟩ :=
    exists_markedScalePressure_limit_tile_le_sum (q := q) hq (w := w) hw
      (kin := kin) (g := g) (Cb := Cb) (G := G) (Kcross := Kcross)
      hCb0 hG0 hK0 hkin_meas hkin_nonneg hkin_bound hkin_homog hg_meas hgb
      α β p hp
  refine ⟨pglobal, fun t => ?_, hbound⟩
  have hwmeas : Measurable w := measurable_of_countable w
  have hwle : ∀ c, w c ≤ 1 := by
    intro c
    have h := Finset.single_le_sum (s := Finset.univ) (f := w)
      (fun i _ => by positivity) (Finset.mem_univ c)
    simpa [hw] using h
  have hCg0 : 0 ≤ max Cb Kcross := le_trans hCb0 (le_max_left _ _)
  exact tendsto_markedFixedPressure_div (q := q) hq
    (C := max Cb Kcross) (G := G) hCg0 hG0
    (measurable_tileKin hwmeas hkin_meas)
    (abs_tileKin_le (w := w) (kin := kin) (Kcross := Kcross)
      (Cb := Cb) (by omega) hwle hkin_bound hCb0 hK0)
    (show Measurable (Function.uncurry (tileProbe g)) from measurable_tileProbe hg_meas)
    (abs_tileProbe_le hG0 hgb)
    (mixtureMarkLaw w α) (mixtureMarkLaw w β)
    pglobal hpg t

/-- **Fixed-size local tile limits.**  Each local marked model has the same
fixed-sample-size pressure limit as its Poissonized scale limit. -/
theorem tendsto_markedFixedPressure_local
    (q : ℕ) (hq : 4 < q)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin_meas : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_bound : ∀ a b v, |kin a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg_meas : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun R => markedScalePressure q A B α β kin g R t)
      atTop (𝓝 (p t))) :
    ∀ t, Tendsto (fun n : ℕ =>
      (∫ ω : TwoMarkedCloudSpace q A B,
        markedFixedValue q (n : ℝ) t kin g n ω
          ∂(twoMarkedCloudLaw q A B α β (n : ℝ≥0))) / (n : ℝ))
      atTop (𝓝 (p t)) :=
  tendsto_markedFixedPressure_div (q := q) hq hCb0 hG0
    hkin_meas hkin_bound hg_meas hgb α β p hp

end OTSelector.Probability
