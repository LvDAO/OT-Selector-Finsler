import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Analysis.Convex.AffineInfimum

## Lemma skeleton

* **Conditions:** A nonempty admissible set of competitors, finite affine objectives bounded below at every tilt, and the stated bounded probe.

* **Objects:** An affine-infimum value, class monotonicity, lower bounds, concavity and Lipschitz tilt control.

* **Proof detail:** Compare the value with every competitor. Pass nonnegative convex combinations of endpoint lower bounds through the intermediate infimum; compare perturbed objectives pointwise in both directions for Lipschitz control.

## Mathematical sources

- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95): Section 3.2.3, pp. 80–81 (p. 81 also states the concave infimum version).
- [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18): Section C, Definitions 0.32 and 0.35, pp. 18–19.

Source relation (corollary): Abstract affine-infimum facts only. The names stationary/pressure do not assert any stationary stochastic construction or existence of a minimizer.
-/

/-!
# Abstract stationary pressure values

The weighted and second-moment pressures of the general selector are infima of
stationary energy functionals over classes of stationary forward matchings:
`I(v) = inf_c (K c + v * P c)`, where `K` is the kinetic energy and `P` the
bounded mark probe.  This module records the order, concavity and Lipschitz
properties that follow from the infimum representation alone, uniformly over the
admissible class.  The analytic content of the theory is the identification of
the weighted and second-moment values; these lemmas are its pointwise skeleton.
-/

noncomputable section
namespace OTSelector.Reconstruction

variable {C : Type*}

/-- The stationary value of a class: the infimum of kinetic energy plus tilt
times probe over the admissible candidates. -/
def stationaryValue (K P : C → ℝ) (admissible : Set C) (v : ℝ) : ℝ :=
  sInf ((fun c ↦ K c + v * P c) '' admissible)

theorem stationaryValue_le {K P : C → ℝ} {admissible : Set C} {v : ℝ} {c : C}
    (hbdd : BddBelow ((fun c ↦ K c + v * P c) '' admissible)) (hc : c ∈ admissible) :
    stationaryValue K P admissible v ≤ K c + v * P c :=
  csInf_le hbdd ⟨c, hc, rfl⟩

/-- Nonnegative kinetic energy and a bounded probe make the value set bounded
below at every tilt. -/
theorem bddBelow_stationaryValue {K P : C → ℝ} {admissible : Set C} {G v : ℝ}
    (hK : ∀ c ∈ admissible, 0 ≤ K c)
    (hP : ∀ c ∈ admissible, |P c| ≤ G) :
    BddBelow ((fun c ↦ K c + v * P c) '' admissible) := by
  refine ⟨-(|v| * G), ?_⟩
  rintro w ⟨c, hc, rfl⟩
  have h1 : 0 ≤ K c := hK c hc
  have h2 := abs_le.mp (hP c hc)
  rcases le_total 0 v with hv | hv
  · have hvabs : |v| = v := abs_of_nonneg hv
    have h3 : v * (-G) ≤ v * P c := mul_le_mul_of_nonneg_left h2.1 hv
    rw [hvabs]
    nlinarith
  · have hvabs : |v| = -v := abs_of_nonpos hv
    have h3 : v * G ≤ v * P c := by
      have := mul_le_mul_of_nonpos_left h2.2 hv
      linarith
    rw [hvabs]
    nlinarith

/-- A larger class has a smaller value. -/
theorem stationaryValue_mono_class {K P : C → ℝ} {admissible₁ admissible₂ : Set C}
    {v : ℝ} (hsub : admissible₂ ⊆ admissible₁)
    (hne : admissible₂.Nonempty)
    (hbdd : BddBelow ((fun c ↦ K c + v * P c) '' admissible₁)) :
    stationaryValue K P admissible₁ v ≤ stationaryValue K P admissible₂ v := by
  apply le_csInf (hne.image _)
  rintro w ⟨c, hc, rfl⟩
  exact csInf_le hbdd ⟨c, hsub hc, rfl⟩

/-- The value is at least minus the tilt times the uniform probe bound when the
kinetic energy is nonnegative. -/
theorem neg_abs_mul_le_stationaryValue {K P : C → ℝ} {admissible : Set C} {v G : ℝ}
    (hne : admissible.Nonempty)
    (hK : ∀ c ∈ admissible, 0 ≤ K c)
    (hP : ∀ c ∈ admissible, |P c| ≤ G) :
    -(|v| * G) ≤ stationaryValue K P admissible v := by
  obtain ⟨c, hc⟩ := hne
  apply le_csInf
  · exact ⟨_, c, hc, rfl⟩
  · rintro w ⟨d, hd, rfl⟩
    have h1 : 0 ≤ K d := hK d hd
    have h2 : v * P d ≥ -(|v| * G) := by
      have h3 : P d ≥ -G := (abs_le.mp (hP d hd)).1
      have h4 : P d ≤ G := (abs_le.mp (hP d hd)).2
      nlinarith [abs_nonneg v, neg_abs_le v, le_abs_self v]
    linarith

/-- The value is concave in the tilt: it is an infimum of affine functions. -/
theorem concaveOn_stationaryValue {K P : C → ℝ} {admissible : Set C}
    (hne : admissible.Nonempty)
    (hbdd : ∀ v : ℝ, BddBelow ((fun c ↦ K c + v * P c) '' admissible)) :
    ConcaveOn ℝ Set.univ (stationaryValue K P admissible) := by
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  simp only [smul_eq_mul]
  have hmixne : ((fun c ↦ K c + (a * t + b * u) * P c) '' admissible).Nonempty :=
    hne.image _
  have hlow : a * stationaryValue K P admissible t +
      b * stationaryValue K P admissible u ≤
      sInf ((fun c ↦ K c + (a * t + b * u) * P c) '' admissible) := by
    apply le_csInf hmixne
    rintro w ⟨d, hd, rfl⟩
    have h1 : stationaryValue K P admissible t ≤ K d + t * P d :=
      stationaryValue_le (hbdd t) hd
    have h2 : stationaryValue K P admissible u ≤ K d + u * P d :=
      stationaryValue_le (hbdd u) hd
    have h1' := mul_le_mul_of_nonneg_left h1 ha
    have h2' := mul_le_mul_of_nonneg_left h2 hb
    have hrearr : a * (K d + t * P d) + b * (K d + u * P d) =
        K d + (a * t + b * u) * P d := by
      have hab' : a + b = 1 := hab
      calc a * (K d + t * P d) + b * (K d + u * P d)
          = (a + b) * K d + (a * t + b * u) * P d := by ring
        _ = K d + (a * t + b * u) * P d := by rw [hab']; ring
    change a * stationaryValue K P admissible t + b * stationaryValue K P admissible u ≤
      K d + (a * t + b * u) * P d
    rw [← hrearr]
    linarith
  exact hlow

/-- The value is Lipschitz in the tilt with the uniform probe bound. -/
theorem abs_stationaryValue_sub_le {K P : C → ℝ} {admissible : Set C}
    (hne : admissible.Nonempty)
    (hbdd : ∀ v : ℝ, BddBelow ((fun c ↦ K c + v * P c) '' admissible))
    {G : ℝ} (hG : 0 ≤ G) (hP : ∀ c ∈ admissible, |P c| ≤ G) (t u : ℝ) :
    |stationaryValue K P admissible t - stationaryValue K P admissible u| ≤
      G * |t - u| := by
  have htu : stationaryValue K P admissible t ≤
      stationaryValue K P admissible u + G * |t - u| := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨w, hwmem, hwlt⟩ := exists_lt_of_csInf_lt (hne.image _)
      (show sInf ((fun c ↦ K c + u * P c) '' admissible) <
          sInf ((fun c ↦ K c + u * P c) '' admissible) + ε from
        lt_add_of_pos_right _ hε)
    obtain ⟨d, hd, rfl⟩ := hwmem
    have hpd := abs_le.mp (hP d hd)
    have h3 : (t - u) * P d ≤ |t - u| * G := by
      calc (t - u) * P d ≤ |t - u| * |P d| := by
            rw [← abs_mul]
            exact le_abs_self _
        _ ≤ |t - u| * G := mul_le_mul_of_nonneg_left (hP d hd) (abs_nonneg _)
    calc stationaryValue K P admissible t ≤ K d + t * P d :=
          stationaryValue_le (hbdd t) hd
      _ = (K d + u * P d) + (t - u) * P d := by ring
      _ ≤ (sInf ((fun c ↦ K c + u * P c) '' admissible) + ε) + G * |t - u| := by
          linarith
      _ = stationaryValue K P admissible u + G * |t - u| + ε := by
          simp only [stationaryValue]
          ring
  have hut : stationaryValue K P admissible u ≤
      stationaryValue K P admissible t + G * |u - t| := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨w, hwmem, hwlt⟩ := exists_lt_of_csInf_lt (hne.image _)
      (show sInf ((fun c ↦ K c + t * P c) '' admissible) <
          sInf ((fun c ↦ K c + t * P c) '' admissible) + ε from
        lt_add_of_pos_right _ hε)
    obtain ⟨d, hd, rfl⟩ := hwmem
    have h3 : (u - t) * P d ≤ |u - t| * G := by
      calc (u - t) * P d ≤ |u - t| * |P d| := by
            rw [← abs_mul]
            exact le_abs_self _
        _ ≤ |u - t| * G := mul_le_mul_of_nonneg_left (hP d hd) (abs_nonneg _)
    calc stationaryValue K P admissible u ≤ K d + u * P d :=
          stationaryValue_le (hbdd u) hd
      _ = (K d + t * P d) + (u - t) * P d := by ring
      _ ≤ (sInf ((fun c ↦ K c + t * P c) '' admissible) + ε) + G * |u - t| := by
          linarith
      _ = stationaryValue K P admissible t + G * |u - t| + ε := by
          simp only [stationaryValue]
          ring
  have htu' : stationaryValue K P admissible t - stationaryValue K P admissible u ≤
      G * |t - u| := by linarith
  have hut' : stationaryValue K P admissible u - stationaryValue K P admissible t ≤
      G * |t - u| := by
    have h := hut
    rw [abs_sub_comm u t] at h
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end OTSelector.Reconstruction
