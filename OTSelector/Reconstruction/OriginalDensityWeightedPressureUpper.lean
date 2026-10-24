import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! True pressure upper limits survive original moving tilts and the exact
Haar density scaling, including zero density without a positive lower bound. -/
open Filter
open scoped Topology NNReal
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- A convergent nonnegative original weight preserves an actual pressure
upper limit. The pressure sequence needs no assumed uniform bound. -/
theorem eventually_weighted_pressure_lt
    {J : Type*} (l : Filter J) [NeBot l] (a r : J → ℝ) (A pref : ℝ)
    (ha : Tendsto a l (𝓝 A)) (ha0 : ∀ j, 0 ≤ a j)
    (hr : ∀ ε > 0, ∀ᶠ j in l, r j < pref + ε) :
    ∀ ε > 0, ∀ᶠ j in l, a j * r j < A * pref + ε := by
  intro ε hε
  have hA : 0 ≤ A := ge_of_tendsto ha (Filter.Eventually.of_forall ha0)
  let d := ε / (2 * (A + 1))
  have hd : 0 < d := div_pos hε (by positivity)
  have hAd : A * d ≤ ε / 2 := by
    dsimp only [d]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2 * (A + 1) by positivity)).mpr
    nlinarith only [hε,hA]
  have ht := ha.mul_const (pref + d)
  have hevent : ∀ᶠ j in l, a j * (pref + d) < A * (pref + d) + ε / 2 :=
    (tendsto_order.mp ht).2 _ (by linarith only [hε])
  filter_upwards [hr d hd,hevent] with j hj hj'
  have hm := mul_le_mul_of_nonneg_left hj.le (ha0 j)
  nlinarith only [hm,hj',hAd]

/-- Uniform physical probe control transfers the original upper limit to
arbitrary converging original tilts. -/
theorem eventually_pressure_lt_of_lipschitz_tilts
    {J : Type*} (l : Filter J) (p : J → ℝ → ℝ) (pref : ℝ → ℝ) (G : ℝ≥0)
    (hLip : ∀ j, LipschitzWith G (p j))
    (hupper : ∀ t ε, 0 < ε → ∀ᶠ j in l, p j t < pref t + ε)
    (tn : J → ℝ) (t : ℝ) (htn : Tendsto tn l (𝓝 t)) :
    ∀ ε > 0, ∀ᶠ j in l, p j (tn j) < pref t + ε := by
  intro ε hε
  have herr : Tendsto (fun j ↦ (G : ℝ) * |tn j - t|) l (𝓝 0) := by
    have hh := ((htn.sub_const t).abs).const_mul (G : ℝ)
    change Tendsto (fun j ↦ (G : ℝ) * |tn j - t|) l (𝓝 ((G : ℝ) * |t - t|)) at hh
    simpa only [sub_self,abs_zero,mul_zero] using hh
  have hsmall : ∀ᶠ j in l, (G : ℝ) * |tn j - t| < ε / 2 :=
    (tendsto_order.mp herr).2 _ (half_pos hε)
  filter_upwards [hupper t (ε / 2) (half_pos hε),hsmall] with j hj hjerr
  have hdist := (hLip j).dist_le_mul (tn j) t
  simp only [Real.dist_eq] at hdist
  have hrel := (abs_le.mp hdist).2
  linarith only [hrel,hj,hjerr]

/-- The exact original Haar density pressure has the required upper limit
under changing original laws, original physical tilts and original density.
The positive density power also treats a null limiting density. -/
theorem eventually_density_weighted_pressure_lt
    {J : Type*} (l : Filter J) [NeBot l]
    {q : ℝ} (hq : 2 < q) (p : J → ℝ → ℝ) (pref : ℝ → ℝ) (G : ℝ≥0)
    (hLip : ∀ j, LipschitzWith G (p j))
    (hupper : ∀ t ε, 0 < ε → ∀ᶠ j in l, p j t < pref t + ε)
    (density : J → ℝ) (ρ : ℝ) (hdensity : Tendsto density l (𝓝 ρ))
    (hdensity0 : ∀ j, 0 ≤ density j) (t : ℝ) :
    ∀ ε > 0, ∀ᶠ j in l,
      density j ^ (1 - 2 / q) * p j (t * density j ^ (2 / q)) <
        ρ ^ (1 - 2 / q) * pref (t * ρ ^ (2 / q)) + ε := by
  have hqpos : 0 < q := by linarith only [hq]
  have hA : 0 ≤ 1 - 2 / q := (sub_pos.mpr ((div_lt_one hqpos).mpr hq)).le
  have hB : 0 ≤ 2 / q := div_nonneg (by norm_num) hqpos.le
  have ha : Tendsto (fun j ↦ density j ^ (1 - 2 / q)) l (𝓝 (ρ ^ (1 - 2 / q))) :=
    (Real.continuous_rpow_const hA).continuousAt.tendsto.comp hdensity
  have hb : Tendsto (fun j ↦ t * density j ^ (2 / q)) l (𝓝 (t * ρ ^ (2 / q))) :=
    ((Real.continuous_rpow_const hB).continuousAt.tendsto.comp hdensity).const_mul t
  have htilt := eventually_pressure_lt_of_lipschitz_tilts l p pref G hLip hupper
    (fun j ↦ t * density j ^ (2 / q)) (t * ρ ^ (2 / q)) hb
  exact eventually_weighted_pressure_lt l (fun j ↦ density j ^ (1 - 2 / q))
    (fun j ↦ p j (t * density j ^ (2 / q))) (ρ ^ (1 - 2 / q))
    (pref (t * ρ ^ (2 / q))) ha (fun j ↦ Real.rpow_nonneg (hdensity0 j) _) htilt

end OTSelector.Reconstruction
