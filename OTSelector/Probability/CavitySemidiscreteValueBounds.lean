import OTSelector.Probability.CavitySemidiscretePrimal
import Mathlib.Analysis.Convex.Function

/-!
# Bounds, Lipschitz continuity and concavity of the full semidiscrete value

The physical semidiscrete primal is the infimum of the coupling objective over
every coupling to a probability target law.  On a bounded measurable cost its
value is bounded, it is Lipschitz in an added affine tilt with constant the probe
bound, and it is concave in that tilt because each coupling objective is affine.

The statements are first proved for an arbitrary probability target law, then
specialized to the weighted atomic cloud of the semidiscrete primal.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] {m : ℕ}

/-- The full coupling value for an arbitrary probability target law. -/
def fullCouplingValue (μ : Measure S) (ν : Measure T) (f : S → T → ℝ) : ℝ :=
  sInf ((fun γ : Measure (S × T) ↦ ∫ z, f z.1 z.2 ∂γ) ''
    {γ | Vlasov.IsCoupling γ μ ν})

theorem fullSemidiscreteValue_eq_fullCouplingValue
    (μ : Measure S) (Y : Fin (m + 1) → T) (f : S → T → ℝ) (p : Fin (m + 1) → ℝ) :
    fullSemidiscreteValue μ Y f p =
      fullCouplingValue μ ((semidiscreteLabelMeasure p).map Y) f := rfl

section Coupling

variable (μ : Measure S) [IsProbabilityMeasure μ]
  (ν : Measure T) [IsProbabilityMeasure ν]

/-- The coupling set is nonempty: the product coupling always exists. -/
theorem nonempty_couplings : ∃ γ : Measure (S × T), Vlasov.IsCoupling γ μ ν :=
  ⟨μ.prod ν, by simp [Vlasov.IsCoupling]⟩

/-- The coupling set is nonempty as a set. -/
theorem couplingSet_nonempty :
    ({γ : Measure (S × T) | Vlasov.IsCoupling γ μ ν} : Set (Measure (S × T))).Nonempty :=
  nonempty_couplings μ ν

/-- A coupling of two probability laws is a probability measure. -/
theorem isProbabilityMeasure_of_isCoupling {γ : Measure (S × T)}
    (hγ : Vlasov.IsCoupling γ μ ν) : IsProbabilityMeasure γ := by
  haveI : IsProbabilityMeasure (γ.map Prod.fst) := hγ.1.symm ▸ inferInstance
  exact Measure.isProbabilityMeasure_of_map Prod.fst

/-- A bounded measurable cost is integrable against every coupling. -/
theorem integrable_of_bounded_isCoupling {γ : Measure (S × T)}
    (hγ : Vlasov.IsCoupling γ μ ν) (f : S → T → ℝ)
    (hf : Measurable (Function.uncurry f)) {B : ℝ}
    (hB : ∀ x y, |f x y| ≤ B) :
    Integrable (Function.uncurry f) γ := by
  haveI : IsProbabilityMeasure γ := isProbabilityMeasure_of_isCoupling μ ν hγ
  refine (integrable_const B).mono' hf.aestronglyMeasurable ?_
  filter_upwards with z
  exact hB z.1 z.2

/-- Every feasible coupling objective bounds the full coupling value above. -/
theorem fullCouplingValue_le_coupling_integral (f : S → T → ℝ)
    (hf : Measurable (Function.uncurry f)) (γ : Measure (S × T))
    (hγ : Vlasov.IsCoupling γ μ ν) {B : ℝ} (hB : ∀ x y, |f x y| ≤ B) :
    fullCouplingValue μ ν f ≤ ∫ z, f z.1 z.2 ∂γ := by
  refine csInf_le ⟨-B, ?_⟩ (Set.mem_image_of_mem _ hγ)
  · rintro _ ⟨κ, hκ, rfl⟩
    haveI : IsProbabilityMeasure κ := isProbabilityMeasure_of_isCoupling μ ν hκ
    have hfi := integrable_of_bounded_isCoupling μ ν hκ f hf hB
    calc -B = ∫ _z : S × T, -B ∂κ := by simp
      _ ≤ ∫ z, f z.1 z.2 ∂κ :=
          integral_mono (integrable_const (-B)) hfi (fun z ↦ (abs_le.mp (hB z.1 z.2)).1)

/-- A pointwise bound on a bounded measurable cost bounds the full coupling
value below. -/
theorem le_fullCouplingValue_of_forall_le (f : S → T → ℝ)
    (hf : Measurable (Function.uncurry f)) {B : ℝ} (hB : ∀ x y, |f x y| ≤ B) :
    -B ≤ fullCouplingValue μ ν f := by
  unfold fullCouplingValue
  refine le_csInf ?_ ?_
  · exact (couplingSet_nonempty μ ν).image (fun γ ↦ (∫ z, f z.1 z.2 ∂γ))
  · rintro _ ⟨κ, hκ, rfl⟩
    haveI : IsProbabilityMeasure κ := isProbabilityMeasure_of_isCoupling μ ν hκ
    have hfi := integrable_of_bounded_isCoupling μ ν hκ f hf hB
    calc -B = ∫ _z : S × T, -B ∂κ := by simp
      _ ≤ ∫ z, f z.1 z.2 ∂κ :=
          integral_mono (integrable_const (-B)) hfi (fun z ↦ (abs_le.mp (hB z.1 z.2)).1)

/-- The value of a cost bounded by `B` in absolute value is bounded by `B`. -/
theorem abs_fullCouplingValue_le (f : S → T → ℝ)
    (hf : Measurable (Function.uncurry f)) {B : ℝ} (hB : ∀ x y, |f x y| ≤ B) :
    |fullCouplingValue μ ν f| ≤ B := by
  rw [abs_le]
  constructor
  · exact le_fullCouplingValue_of_forall_le μ ν f hf hB
  · obtain ⟨γ, hγ⟩ := nonempty_couplings μ ν
    refine (fullCouplingValue_le_coupling_integral μ ν f hf γ hγ hB).trans ?_
    haveI : IsProbabilityMeasure γ := isProbabilityMeasure_of_isCoupling μ ν hγ
    have hfi := integrable_of_bounded_isCoupling μ ν hγ f hf hB
    calc ∫ z, f z.1 z.2 ∂γ ≤ ∫ _z : S × T, B ∂γ :=
          integral_mono hfi (integrable_const B) (fun z ↦ (abs_le.mp (hB z.1 z.2)).2)
      _ = B := by simp

end Coupling

section Tilt

/-- The tilted cost. -/
def tiltCost {S T : Type*} (c g : S → T → ℝ) (t : ℝ) : S → T → ℝ :=
  fun x y ↦ c x y + t * g x y

variable {c g : S → T → ℝ}

theorem measurable_tiltCost (hc : Measurable (Function.uncurry c))
    (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (Function.uncurry (tiltCost c g t)) := by
  have h : Function.uncurry (tiltCost c g t) =
      fun z : S × T ↦ Function.uncurry c z + t * Function.uncurry g z := by
    funext z; rfl
  rw [h]
  exact hc.add (hg.const_mul t)

theorem abs_tiltCost_le {C G : ℝ} (hC : ∀ x y, |c x y| ≤ C)
    (hG : ∀ x y, |g x y| ≤ G) (t : ℝ) (x : S) (y : T) :
    |tiltCost c g t x y| ≤ C + |t| * G := by
  calc |tiltCost c g t x y| = |c x y + t * g x y| := rfl
    _ ≤ |c x y| + |t * g x y| := abs_add_le _ _
    _ = |c x y| + |t| * |g x y| := by rw [abs_mul]
    _ ≤ C + |t| * G :=
        add_le_add (hC x y) (mul_le_mul_of_nonneg_left (hG x y) (abs_nonneg t))

/-- The tilted full coupling value. -/
def tiltValue (μ : Measure S) (ν : Measure T) (c g : S → T → ℝ) (t : ℝ) : ℝ :=
  fullCouplingValue μ ν (tiltCost c g t)

theorem abs_tiltValue_le (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (hc : Measurable (Function.uncurry c)) (hg : Measurable (Function.uncurry g))
    {C G : ℝ} (hC : ∀ x y, |c x y| ≤ C) (hG : ∀ x y, |g x y| ≤ G) (t : ℝ) :
    |tiltValue μ ν c g t| ≤ C + |t| * G :=
  abs_fullCouplingValue_le μ ν _ (measurable_tiltCost hc hg t)
    (abs_tiltCost_le hC hG t)

/-- The objective integral is affine in the tilt parameter. -/
theorem integral_tiltCost (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (hc : Measurable (Function.uncurry c)) (hg : Measurable (Function.uncurry g))
    {C G : ℝ} (hC : ∀ x y, |c x y| ≤ C) (hG : ∀ x y, |g x y| ≤ G)
    (t u : ℝ) (a b : ℝ) (hab : a + b = 1) :
    ∀ γ : Measure (S × T), Vlasov.IsCoupling γ μ ν →
      ∫ z, tiltCost c g (a * t + b * u) z.1 z.2 ∂γ =
        a * (∫ z, tiltCost c g t z.1 z.2 ∂γ) +
          b * (∫ z, tiltCost c g u z.1 z.2 ∂γ) := by
  intro γ hγ
  haveI : IsProbabilityMeasure γ := isProbabilityMeasure_of_isCoupling μ ν hγ
  have hti := integrable_of_bounded_isCoupling μ ν hγ (tiltCost c g t)
    (measurable_tiltCost hc hg t) (abs_tiltCost_le hC hG t)
  have hui := integrable_of_bounded_isCoupling μ ν hγ (tiltCost c g u)
    (measurable_tiltCost hc hg u) (abs_tiltCost_le hC hG u)
  have hm : ∀ z : S × T, tiltCost c g (a * t + b * u) z.1 z.2 =
      a * tiltCost c g t z.1 z.2 + b * tiltCost c g u z.1 z.2 := by
    intro z
    simp only [tiltCost]
    linear_combination (-(c z.1 z.2)) * hab
  calc ∫ z, tiltCost c g (a * t + b * u) z.1 z.2 ∂γ
      = ∫ z, (a * tiltCost c g t z.1 z.2 + b * tiltCost c g u z.1 z.2) ∂γ :=
        integral_congr_ae (Filter.Eventually.of_forall hm)
    _ = (∫ z, a * tiltCost c g t z.1 z.2 ∂γ) +
          (∫ z, b * tiltCost c g u z.1 z.2 ∂γ) :=
        integral_add (hti.const_mul a) (hui.const_mul b)
    _ = a * (∫ z, tiltCost c g t z.1 z.2 ∂γ) +
          b * (∫ z, tiltCost c g u z.1 z.2 ∂γ) := by
        rw [integral_const_mul, integral_const_mul]

/-- One-sided Lipschitz comparison in the tilt. -/
theorem tiltValue_le_add_abs_sub_mul (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (hc : Measurable (Function.uncurry c)) (hg : Measurable (Function.uncurry g))
    {C G : ℝ} (hC : ∀ x y, |c x y| ≤ C) (hG : ∀ x y, |g x y| ≤ G) (t u : ℝ) :
    tiltValue μ ν c g t ≤ tiltValue μ ν c g u + |t - u| * G := by
  set ft := tiltCost c g t with hft
  set fu := tiltCost c g u with hfu
  have hne : ((fun γ : Measure (S × T) ↦ ∫ z, fu z.1 z.2 ∂γ) ''
      {γ | Vlasov.IsCoupling γ μ ν}).Nonempty :=
    (couplingSet_nonempty μ ν).image (fun γ ↦ (∫ z, fu z.1 z.2 ∂γ))
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hinf_lt : fullCouplingValue μ ν fu < fullCouplingValue μ ν fu + ε := by linarith
  obtain ⟨a, ⟨γ, hγ, rfl⟩, ha⟩ := exists_lt_of_csInf_lt hne hinf_lt
  haveI : IsProbabilityMeasure γ := isProbabilityMeasure_of_isCoupling μ ν hγ
  have hgi := integrable_of_bounded_isCoupling μ ν hγ g hg hG
  have hti := integrable_of_bounded_isCoupling μ ν hγ ft
    (measurable_tiltCost hc hg t) (abs_tiltCost_le hC hG t)
  have hui := integrable_of_bounded_isCoupling μ ν hγ fu
    (measurable_tiltCost hc hg u) (abs_tiltCost_le hC hG u)
  have hVt : tiltValue μ ν c g t ≤ ∫ z, ft z.1 z.2 ∂γ :=
    fullCouplingValue_le_coupling_integral μ ν ft
      (measurable_tiltCost hc hg t) γ hγ (abs_tiltCost_le hC hG t)
  have hdiff : ∫ z, ft z.1 z.2 ∂γ - ∫ z, fu z.1 z.2 ∂γ =
      (t - u) * ∫ z, g z.1 z.2 ∂γ := by
    have hsplit : ∀ z : S × T, ft z.1 z.2 - fu z.1 z.2 = (t - u) * g z.1 z.2 := by
      intro z; simp only [hft, hfu, tiltCost]; ring
    calc ∫ z, ft z.1 z.2 ∂γ - ∫ z, fu z.1 z.2 ∂γ
        = ∫ z, (ft z.1 z.2 - fu z.1 z.2) ∂γ := (integral_sub hti hui).symm
      _ = ∫ z, (t - u) * g z.1 z.2 ∂γ :=
          integral_congr_ae (Filter.Eventually.of_forall hsplit)
      _ = (t - u) * ∫ z, g z.1 z.2 ∂γ := integral_const_mul _ _
  have hgabs : |∫ z, g z.1 z.2 ∂γ| ≤ G := by
    have h := abs_integral_le_integral_abs (μ := γ) (f := fun z ↦ g z.1 z.2)
    refine h.trans ?_
    calc ∫ z, |g z.1 z.2| ∂γ ≤ ∫ _z : S × T, G ∂γ :=
          integral_mono hgi.abs (integrable_const G) (fun z ↦ hG z.1 z.2)
      _ = G := by simp
  have hft_eq : ∫ z, ft z.1 z.2 ∂γ =
      ∫ z, fu z.1 z.2 ∂γ + (t - u) * ∫ z, g z.1 z.2 ∂γ := by
    linarith [hdiff]
  have hmain : ∫ z, ft z.1 z.2 ∂γ ≤ ∫ z, fu z.1 z.2 ∂γ + |t - u| * G := by
    rw [hft_eq]
    have hscal : (t - u) * (∫ z, g z.1 z.2 ∂γ) ≤ |t - u| * G := by
      calc (t - u) * (∫ z, g z.1 z.2 ∂γ) ≤ |(t - u) * (∫ z, g z.1 z.2 ∂γ)| :=
            le_abs_self _
        _ = |t - u| * |∫ z, g z.1 z.2 ∂γ| := abs_mul _ _
        _ ≤ |t - u| * G := mul_le_mul_of_nonneg_left hgabs (abs_nonneg _)
    linarith
  have hchain : tiltValue μ ν c g t ≤
      fullCouplingValue μ ν (tiltCost c g u) + |t - u| * G + ε := by
    calc tiltValue μ ν c g t ≤ ∫ z, ft z.1 z.2 ∂γ := hVt
      _ ≤ ∫ z, fu z.1 z.2 ∂γ + |t - u| * G := hmain
      _ ≤ (fullCouplingValue μ ν fu + ε) + |t - u| * G := by linarith [ha.le]
      _ = fullCouplingValue μ ν (tiltCost c g u) + |t - u| * G + ε := by
          rw [hfu]; ring
  simpa only [tiltValue] using hchain

/-- The tilted value is Lipschitz in the tilt with the probe bound. -/
theorem abs_tiltValue_sub_le (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (hc : Measurable (Function.uncurry c)) (hg : Measurable (Function.uncurry g))
    {C G : ℝ} (hC : ∀ x y, |c x y| ≤ C) (hG : ∀ x y, |g x y| ≤ G) (t u : ℝ) :
    |tiltValue μ ν c g t - tiltValue μ ν c g u| ≤ |t - u| * G := by
  rw [abs_le]
  constructor
  · have h := tiltValue_le_add_abs_sub_mul μ ν hc hg hC hG u t
    rw [abs_sub_comm u t] at h
    linarith
  · have h := tiltValue_le_add_abs_sub_mul μ ν hc hg hC hG t u
    linarith

/-- The full coupling value is concave in the tilt. -/
theorem concaveOn_tiltValue (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    (hc : Measurable (Function.uncurry c)) (hg : Measurable (Function.uncurry g))
    {C G : ℝ} (hC : ∀ x y, |c x y| ≤ C) (hG : ∀ x y, |g x y| ≤ G) :
    ConcaveOn ℝ univ (fun t ↦ tiltValue μ ν c g t) := by
  refine ⟨convex_univ, ?_⟩
  intro t₁ _ t₂ _ a b ha hb hab
  change a * tiltValue μ ν c g t₁ + b * tiltValue μ ν c g t₂ ≤
    tiltValue μ ν c g (a * t₁ + b * t₂)
  have hne : ((fun γ : Measure (S × T) ↦
      ∫ z, tiltCost c g (a * t₁ + b * t₂) z.1 z.2 ∂γ) ''
      {γ | Vlasov.IsCoupling γ μ ν}).Nonempty :=
    (couplingSet_nonempty μ ν).image (fun γ ↦ (∫ z, tiltCost c g (a * t₁ + b * t₂) z.1 z.2 ∂γ))
  have hVm : tiltValue μ ν c g (a * t₁ + b * t₂) =
      sInf ((fun γ : Measure (S × T) ↦
        ∫ z, tiltCost c g (a * t₁ + b * t₂) z.1 z.2 ∂γ) ''
        {γ | Vlasov.IsCoupling γ μ ν}) := rfl
  rw [hVm]
  refine le_csInf hne ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have h1 : a * tiltValue μ ν c g t₁ ≤
      a * ∫ z, tiltCost c g t₁ z.1 z.2 ∂γ :=
    mul_le_mul_of_nonneg_left
      (fullCouplingValue_le_coupling_integral μ ν _
        (measurable_tiltCost hc hg t₁) γ hγ (abs_tiltCost_le hC hG t₁)) ha
  have h2 : b * tiltValue μ ν c g t₂ ≤
      b * ∫ z, tiltCost c g t₂ z.1 z.2 ∂γ :=
    mul_le_mul_of_nonneg_left
      (fullCouplingValue_le_coupling_integral μ ν _
        (measurable_tiltCost hc hg t₂) γ hγ (abs_tiltCost_le hC hG t₂)) hb
  have haff := integral_tiltCost μ ν hc hg hC hG t₁ t₂ a b hab γ hγ
  linarith

end Tilt

end OTSelector.Probability
