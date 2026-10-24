import OTSelector.Reconstruction.MarkedStationaryValueLegalShapeBinomial
import OTSelector.Probability.BinomialPoissonVarying

/-! Exact fixed-prefix expectations of the original legal count cloud. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Legal value of the two original iid sequences at prescribed prefix sizes. -/
def legalFixedSeqValue (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (m k : ℕ) (z : (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B)) : ℝ :=
  legalMarkedFixedValue q m k source target r kin probe t ((m, z.1), (k, z.2))

/-- The deterministic finite-size expectation keeps the original legal graph. -/
def legalFixedSeqExpectation (q : ℕ) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (m k : ℕ) : ℝ :=
  ∫ z, legalFixedSeqValue q source target r kin probe t m k z
    ∂(markedSeqLaw q A α).prod (markedSeqLaw q B β)

theorem measurable_legalFixedSeqValue (q m k : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe)) (r t : ℝ) :
    Measurable (legalFixedSeqValue q source target r kin probe t m k) :=
  (measurable_legalMarkedFixedValue q m k hs ht hk hp r t).comp
    ((measurable_const.prodMk measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))

theorem abs_legalFixedSeqValue_le (q m k : ℕ) (source : A → ℝ) (target : B → ℝ)
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ)
    (z : (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B)) :
    |legalFixedSeqValue q source target r kin probe t m k z| ≤
      ((min m k : ℕ) : ℝ) * (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G) :=
  abs_legalMarkedTilted_le q source target hr hC hG hkb hpb t ((m, z.1), (k, z.2))

theorem integrable_legalFixedSeqValue (q m k : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    Integrable (legalFixedSeqValue q source target r kin probe t m k)
      ((markedSeqLaw q A α).prod (markedSeqLaw q B β)) := by
  apply Integrable.of_bound (measurable_legalFixedSeqValue q m k hs ht hk hp r t).aestronglyMeasurable
    (((min m k : ℕ) : ℝ) * (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G))
  exact .of_forall fun z ↦ by
    rw [Real.norm_eq_abs]
    exact abs_legalFixedSeqValue_le q m k source target hr hC hG hkb hpb t z

theorem abs_legalFixedSeqExpectation_le (q m k : ℕ) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    |legalFixedSeqExpectation q source target α β r kin probe t m k| ≤
      (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G) * ((min m k : ℕ) : ℝ) := by
  rw [legalFixedSeqExpectation, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const
    (μ := (markedSeqLaw q A α).prod (markedSeqLaw q B β))
    (C := ((min m k : ℕ) : ℝ) * (r ^ (2 / (q : ℝ)) * (C * q) + |t| * G))
    (.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact abs_legalFixedSeqValue_le q m k source target hr hC hG hkb hpb t z)
  simpa [measureReal_def, mul_comm] using h

/-- Separating the original two independent counts preserves the literal legal value. -/
theorem integral_legalMarkedTilted_countLaw_eq_fixed (q : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (κ : Measure ℕ) [IsProbabilityMeasure κ]
    (hκ : Integrable (fun n : ℕ ↦ (n : ℝ)) κ)
    {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    (∫ ω, legalMarkedTilted q source target r kin probe t ω
      ∂twoMarkedCountLaw q α β κ) =
      ∫ m, ∫ k, legalFixedSeqExpectation q source target α β r kin probe t m k ∂κ ∂κ := by
  let V := legalMarkedTilted q source target r kin probe t
  let Bnd := r ^ (2 / (q : ℝ)) * (C * q) + |t| * G
  have hBnd : 0 ≤ Bnd := by dsimp [Bnd]; positivity
  have hV := integrable_legalMarkedTilted_countLaw q hs ht α β κ hκ hr hC hG hk hkb hp hpb t
  have hT (m : ℕ) (xs : ℕ → (Fin q → ℝ) × A) :
      Integrable (fun p : MarkedCloudSpace q B ↦ V ((m, xs), p))
      (markedCountLaw q β κ) := by
    apply Integrable.of_bound
      ((measurable_legalMarkedTilted q hs ht hk hp r t).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable ((m : ℝ) * Bnd)
    filter_upwards [] with p
    rw [Real.norm_eq_abs]
    exact (abs_legalMarkedTilted_le q source target hr hC hG hkb hpb t _).trans
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_left _ _)) hBnd)
  rw [twoMarkedCountLaw, integral_prod _ hV]
  change (∫ p : ℕ × (ℕ → (Fin q → ℝ) × A),
    (∫ y, V (p, y) ∂markedCountLaw q β κ) ∂κ.prod (markedSeqLaw q A α)) = _
  rw [integral_prod _ hV.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with m
  have hexpand : (fun xs : ℕ → (Fin q → ℝ) × A ↦
      ∫ y, V ((m, xs), y) ∂markedCountLaw q β κ) =
      (fun xs ↦ ∫ k, ∫ ys, V ((m, xs), (k, ys)) ∂markedSeqLaw q B β ∂κ) := by
    funext xs
    exact integral_prod _ (hT m xs)
  rw [hexpand]
  have hmid : Integrable (fun p : (ℕ → (Fin q → ℝ) × A) × ℕ ↦
      ∫ ys, V ((m, p.1), (p.2, ys)) ∂markedSeqLaw q B β)
      ((markedSeqLaw q A α).prod κ) := by
    refine Integrable.of_bound ?_ ((m : ℝ) * Bnd) ?_
    · have hm : Measurable (fun p : ((ℕ → (Fin q → ℝ) × A) × ℕ) ×
          (ℕ → (Fin q → ℝ) × B) ↦ V ((m, p.1.1), (p.1.2, p.2))) :=
        (measurable_legalMarkedTilted q hs ht hk hp r t).comp
        ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      exact hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · filter_upwards [] with p
      rw [Real.norm_eq_abs]
      rw [← Real.norm_eq_abs]
      have hh := norm_integral_le_of_norm_le_const (μ := markedSeqLaw q B β)
        (f := fun ys ↦ V ((m, p.1), (p.2, ys)))
        (C := (m : ℝ) * Bnd) (Filter.Eventually.of_forall fun ys ↦ by
          rw [Real.norm_eq_abs]
          exact (abs_legalMarkedTilted_le q source target hr hC hG hkb hpb t _).trans
            (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (min_le_left _ _)) hBnd))
      simpa using hh
  rw [integral_integral_swap hmid]
  apply integral_congr_ae
  filter_upwards [] with k
  exact (integral_prod _ (integrable_legalFixedSeqValue q m k hs ht α β hr hC hG
    hk hkb hp hpb t)).symm

end OTSelector.Reconstruction
