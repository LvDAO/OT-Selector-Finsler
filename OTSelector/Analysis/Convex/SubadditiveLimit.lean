import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Analysis.Convex.SubadditiveLimit

Conditions: A bounded real scale/tilt family, continuous in positive scale and concave and uniformly Lipschitz in tilt, satisfies the stated block subadditivity with vanishing block errors.

Objects: An actual scale limit preserving tilt concavity and the Lipschitz constant.

Proof detail: Choose the integer block count floor(R/L0), set the corrected block size R/m, and compare limsup with a fixed-block value. Let the block size grow to force limsup=liminf, then pass the defining concavity/Lipschitz inequalities to the limit.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=62): Section 2.2, Lemma 2.2.3, p. 62; Section 2.3, Proposition 2.3.5, pp. 76–77.
- [Stephen Boyd, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=95): Section 3.2.3, pp. 80–81 (p. 81 also states the concave infimum version).

Source relation: Locally proved block-limit theorem assembled from limit/order and concavity tools. No claim that the scale-dependent error theorem is a verbatim Fekete lemma.
-/

/-!
# Pressure limits from block subadditivity

A scale-indexed family `f R t` converges as `R → ∞` whenever it is uniformly
bounded, concave and Lipschitz in the tilt, continuous in the scale at every
positive scale, and satisfies a crude block-subadditive comparison: for every
positive scale `L` in a compact interval and every `ε > 0`,

`f (m * L) t ≤ f L t + ε`

for all sufficiently large block counts `m`.

Unlike the self-similar comparison of `PressureSelfSimilarLimit`, no decay
factor multiplies the comparison scale.  The proof writes a large scale `R` as
`m * L` with `m = ⌊R / L₀⌋` and `L = R / m`, so that `L → L₀` as `R → ∞`.
The block comparison then bounds `limsup f (·) t` by `f L₀ t` for every
positive `L₀`; since low values of `f (·) t` are frequent near the liminf, the
two one-sided limits agree.  Concavity and the common Lipschitz bound pass to
the pointwise limit.
-/

open Filter Set Topology
open scoped Topology

namespace OTSelector

/-- If a scale-indexed family is uniformly bounded, concave and Lipschitz in the tilt,
continuous in the scale at every positive scale, and satisfies the block-subadditive
comparison `f (m * L) t ≤ f L t + ε` uniformly for block sides `L` in a compact interval
once `m` is large, then it converges at every tilt to a concave Lipschitz limit. -/
theorem exists_tendsto_of_block_subadditive
    {f : ℝ → ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hbdd : ∀ t, ∃ B : ℝ, ∀ R : ℝ, 1 ≤ R → |f R t| ≤ B)
    (hconcave : ∀ R, ConcaveOn ℝ univ (f R))
    (hlip : ∀ R t u, |f R t - f R u| ≤ G * |t - u|)
    (hcont : ∀ t L, 0 < L → Tendsto (fun R ↦ f R t) (𝓝 L) (𝓝 (f L t)))
    (hblock : ∀ t : ℝ, ∀ A B : ℝ, 0 < A → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ L ∈ Set.Icc A B, 0 < L → f ((m : ℝ) * L) t ≤ f L t + ε) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ f R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p := by
  -- Uniform one-sided boundedness of every tilt sequence.
  have hbdd_le : ∀ t, atTop.IsBoundedUnder (· ≤ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    exact ⟨B, eventually_atTop.2 ⟨1, fun R hR ↦ (abs_le.mp (hB R hR)).2⟩⟩
  have hbdd_ge : ∀ t, atTop.IsBoundedUnder (· ≥ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    exact ⟨-B, eventually_atTop.2 ⟨1, fun R hR ↦ (abs_le.mp (hB R hR)).1⟩⟩
  have hcobdd_ge : ∀ t, atTop.IsCoboundedUnder (· ≥ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    refine ⟨B, fun a ha ↦ ?_⟩
    obtain ⟨R, hRa, hRB⟩ := ((eventually_atTop.2 ⟨1, fun R hR ↦
      (abs_le.mp (hB R hR)).2⟩).and ha).exists
    exact le_trans hRB hRa
  have hcobdd_le : ∀ t, atTop.IsCoboundedUnder (· ≤ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    refine ⟨-B, fun a ha ↦ ?_⟩
    obtain ⟨R, hRa, hRB⟩ := ((eventually_atTop.2 ⟨1, fun R hR ↦
      (abs_le.mp (hB R hR)).1⟩).and ha).exists
    exact le_trans hRa hRB
  -- Step 1: the limsup at infinity is bounded by the value at every positive scale.
  have hle : ∀ t (L0 : ℝ), 0 < L0 →
      Filter.limsup (fun R ↦ f R t) atTop ≤ f L0 t := by
    intro t L0 hL0
    refine (Filter.limsup_le_iff (hcobdd_le t) (hbdd_le t)).2 ?_
    intro y hy
    -- Split the gap `y - f L₀ t` between the block error and the scale drift.
    set δ : ℝ := (y - f L0 t) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    obtain ⟨M, hM⟩ := eventually_atTop.1
      (hblock t (L0 / 2) (2 * L0) (by linarith) δ hδpos)
    -- Write a large scale as `n R * L R` with `L R` close to `L₀`.
    let n : ℝ → ℕ := fun R ↦ Nat.floor (R / L0)
    let L : ℝ → ℝ := fun R ↦ R / (n R : ℝ)
    have hn_atTop : Tendsto n atTop atTop := by
      rw [tendsto_atTop]
      intro N
      filter_upwards [eventually_ge_atTop (max ((N : ℝ) * (2 * L0)) (2 * L0))] with R hR
      have hRN : (N : ℝ) * (2 * L0) ≤ R := le_trans (le_max_left _ _) hR
      have hR2 : 2 * L0 ≤ R := le_trans (le_max_right _ _) hR
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hL0]
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    have hL_tendsto : Tendsto L atTop (𝓝 L0) := by
      have hn_real : Tendsto (fun R : ℝ ↦ (n R : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hn_atTop
      have hsmall : Tendsto (fun R : ℝ ↦ L0 / (n R : ℝ)) atTop (𝓝 0) :=
        hn_real.const_div_atTop L0
      have hn_ge_one : ∀ᶠ R : ℝ in atTop, 1 ≤ n R := by
        have hfloor : ∀ R : ℝ, 0 < R → 1 ≤ R / L0 → 1 ≤ n R := by
          intro R hR hR1
          have hpos : 0 < n R := Nat.floor_pos.2 hR1
          exact Nat.succ_le_of_lt hpos
        filter_upwards [eventually_ge_atTop (2 * L0)] with R hR
        exact hfloor R (by linarith) (by rw [one_le_div hL0]; linarith)
      have hdiff : Tendsto (fun R : ℝ ↦ L R - L0) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds hsmall ?_ ?_
        · filter_upwards [hn_ge_one, eventually_ge_atTop (2 * L0)] with R hn1 hR
          have hRpos : 0 < R := by linarith
          have hnpos : (0 : ℝ) < (n R : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
          have hfloor : (n R : ℝ) ≤ R / L0 :=
            Nat.floor_le (div_nonneg hRpos.le hL0.le)
          have hLR : L0 ≤ L R := by
            show L0 ≤ R / (n R : ℝ)
            rw [le_div_iff₀ hnpos]
            have hfloor_mul : (n R : ℝ) * L0 ≤ R := (le_div_iff₀ hL0).1 hfloor
            nlinarith
          linarith
        · filter_upwards [hn_ge_one, eventually_ge_atTop (2 * L0)] with R hn1 hR
          have hRpos : 0 < R := by linarith
          have hnpos : (0 : ℝ) < (n R : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
          have hnlt : R / L0 < (n R : ℝ) + 1 := Nat.lt_floor_add_one (R / L0)
          have hRlt : R < ((n R : ℝ) + 1) * L0 := by
            rw [div_lt_iff₀ hL0] at hnlt
            linarith
          show R / (n R : ℝ) - L0 ≤ L0 / (n R : ℝ)
          rw [sub_le_iff_le_add, div_le_iff₀ hnpos]
          have hrhs : (L0 / (n R : ℝ) + L0) * (n R : ℝ) = L0 * (n R : ℝ) + L0 := by
            rw [add_mul, div_mul_cancel₀ L0 (ne_of_gt hnpos)]
            ring
          rw [hrhs]
          nlinarith
      have hsum : Tendsto (fun R : ℝ ↦ (L R - L0) + L0) atTop (𝓝 (0 + L0)) :=
        hdiff.add tendsto_const_nhds
      simpa only [sub_add_cancel, zero_add] using hsum
    have hconv_lt : ∀ᶠ R : ℝ in atTop, f (L R) t < f L0 t + δ :=
      ((hcont t L0 hL0).comp hL_tendsto).eventually
        (Iio_mem_nhds (by linarith : f L0 t < f L0 t + δ))
    filter_upwards [hconv_lt,
      eventually_ge_atTop (max ((M : ℝ) * L0) (2 * L0))] with R hRlt hR
    have hRML : (M : ℝ) * L0 ≤ R := le_trans (le_max_left _ _) hR
    have hR2 : 2 * L0 ≤ R := le_trans (le_max_right _ _) hR
    have hRpos : 0 < R := by linarith
    have hnM : M ≤ n R := by
      refine Nat.le_floor ?_
      rw [le_div_iff₀ hL0]
      exact hRML
    have hn1 : 1 ≤ n R := by
      have hpos : 0 < n R := Nat.floor_pos.2 (by rw [one_le_div hL0]; linarith)
      exact Nat.succ_le_of_lt hpos
    have hnpos : (0 : ℝ) < (n R : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn1)
    have hfloor : (n R : ℝ) ≤ R / L0 :=
      Nat.floor_le (div_nonneg hRpos.le hL0.le)
    have hnlt : R / L0 < (n R : ℝ) + 1 := Nat.lt_floor_add_one (R / L0)
    have hLR_lower : L0 / 2 ≤ L R := by
      have hLR : L0 ≤ L R := by
        show L0 ≤ R / (n R : ℝ)
        rw [le_div_iff₀ hnpos]
        have hfloor_mul : (n R : ℝ) * L0 ≤ R := (le_div_iff₀ hL0).1 hfloor
        nlinarith
      linarith
    have hLR_upper : L R ≤ 2 * L0 := by
      show R / (n R : ℝ) ≤ 2 * L0
      rw [div_le_iff₀ hnpos]
      have hRlt : R < ((n R : ℝ) + 1) * L0 := by
        rw [div_lt_iff₀ hL0] at hnlt
        linarith
      have hn2 : (n R : ℝ) + 1 ≤ 2 * (n R : ℝ) := by
        have : (1 : ℝ) ≤ (n R : ℝ) := by exact_mod_cast hn1
        linarith
      nlinarith
    have hLRpos : 0 < L R := by linarith
    have hineq := hM (n R) hnM (L R) ⟨hLR_lower, hLR_upper⟩ hLRpos
    have hmul : (n R : ℝ) * L R = R := by
      show (n R : ℝ) * (R / (n R : ℝ)) = R
      exact mul_div_cancel₀ R (ne_of_gt hnpos)
    rw [hmul] at hineq
    linarith
  -- Step 2: the reverse inequality for the two one-sided limits.
  have hlimsup_le_liminf : ∀ t,
      Filter.limsup (fun R ↦ f R t) atTop ≤ Filter.liminf (fun R ↦ f R t) atTop := by
    intro t
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨y, hy_liminf, hy_limsup⟩ := exists_between hlt
    have hfreq : ∃ᶠ R : ℝ in atTop, f R t < y :=
      frequently_lt_of_liminf_lt (hcobdd_ge t) hy_liminf
    obtain ⟨R, hRy, hR1⟩ :=
      (hfreq.and_eventually (eventually_ge_atTop (1 : ℝ))).exists
    have hRpos : 0 < R := by linarith
    have hleR : Filter.limsup (fun R ↦ f R t) atTop ≤ f R t := hle t R hRpos
    linarith
  -- Step 3: the common value is the limit at every tilt.
  let p : ℝ → ℝ := fun t ↦ Filter.liminf (fun R ↦ f R t) atTop
  have hlim_eq : ∀ t, Filter.liminf (fun R ↦ f R t) atTop =
      Filter.limsup (fun R ↦ f R t) atTop := by
    intro t
    exact le_antisymm (Filter.liminf_le_limsup (hbdd_le t) (hbdd_ge t))
      (hlimsup_le_liminf t)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro t
    exact tendsto_of_liminf_eq_limsup rfl (hlim_eq t).symm (hbdd_le t) (hbdd_ge t)
  · -- Concavity passes to the pointwise limit.
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hx : Tendsto (fun R ↦ f R x) atTop (𝓝 (p x)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq x).symm (hbdd_le x) (hbdd_ge x)
    have hy : Tendsto (fun R ↦ f R y) atTop (𝓝 (p y)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq y).symm (hbdd_le y) (hbdd_ge y)
    have hxy : Tendsto (fun R ↦ f R (a * x + b * y)) atTop
        (𝓝 (p (a * x + b * y))) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq (a * x + b * y)).symm
        (hbdd_le _) (hbdd_ge _)
    have hlim : Tendsto (fun R ↦ a * f R x + b * f R y) atTop
        (𝓝 (a * p x + b * p y)) :=
      (hx.const_mul a).add (hy.const_mul b)
    have hev : ∀ᶠ R in atTop, a * f R x + b * f R y ≤ f R (a * x + b * y) :=
      Filter.Eventually.of_forall fun R ↦ (hconcave R).2 (mem_univ x) (mem_univ y) ha hb hab
    have hle' : a * p x + b * p y ≤ p (a * x + b * y) :=
      le_of_tendsto_of_tendsto hlim hxy hev
    simpa only [smul_eq_mul] using hle'
  · -- The Lipschitz bound passes to the pointwise limit.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hx : Tendsto (fun R ↦ f R x) atTop (𝓝 (p x)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq x).symm (hbdd_le x) (hbdd_ge x)
    have hy : Tendsto (fun R ↦ f R y) atTop (𝓝 (p y)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq y).symm (hbdd_le y) (hbdd_ge y)
    have hdiff : Tendsto (fun R ↦ f R x - f R y) atTop (𝓝 (p x - p y)) := hx.sub hy
    have hbound : Tendsto (fun R ↦ |f R x - f R y|) atTop (𝓝 (|p x - p y|)) :=
      hdiff.abs
    have hconst : Tendsto (fun _ : ℝ ↦ G * |x - y|) atTop (𝓝 (G * |x - y|)) :=
      tendsto_const_nhds
    have hev : ∀ᶠ R in atTop, |f R x - f R y| ≤ G * |x - y| :=
      Filter.Eventually.of_forall fun R ↦ hlip R x y
    have := le_of_tendsto_of_tendsto hbound hconst hev
    rw [Real.dist_eq, Real.dist_eq]
    exact this

/-- Convergence from a block-subadditive comparison whose side-dependent error is a
fixed continuous function tending to zero at infinity. -/
theorem exists_tendsto_of_block_subadditive_of_error
    {f : ℝ → ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hbdd : ∀ t, ∃ B : ℝ, ∀ R : ℝ, 1 ≤ R → |f R t| ≤ B)
    (hconcave : ∀ R, ConcaveOn ℝ univ (f R))
    (hlip : ∀ R t u, |f R t - f R u| ≤ G * |t - u|)
    (hcont : ∀ t L, 0 < L → Tendsto (fun R ↦ f R t) (𝓝 L) (𝓝 (f L t)))
    (ε : ℝ → ℝ)
    (hεcont : ∀ L, 0 < L → Tendsto ε (𝓝 L) (𝓝 (ε L)))
    (hε0 : Tendsto ε atTop (𝓝 0))
    (hblock : ∀ t L : ℝ, 0 < L → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m : ℕ in atTop, f ((m : ℝ) * L) t ≤ f L t + ε L + δ) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ f R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p := by
  -- Uniform one-sided boundedness of every tilt sequence.
  have hbdd_le : ∀ t, atTop.IsBoundedUnder (· ≤ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    exact ⟨B, eventually_atTop.2 ⟨1, fun R hR ↦ (abs_le.mp (hB R hR)).2⟩⟩
  have hbdd_ge : ∀ t, atTop.IsBoundedUnder (· ≥ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    exact ⟨-B, eventually_atTop.2 ⟨1, fun R hR ↦ (abs_le.mp (hB R hR)).1⟩⟩
  have hcobdd_ge : ∀ t, atTop.IsCoboundedUnder (· ≥ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    refine ⟨B, fun a ha ↦ ?_⟩
    obtain ⟨R, hRa, hRB⟩ := ((eventually_atTop.2 ⟨1, fun R hR ↦
      (abs_le.mp (hB R hR)).2⟩).and ha).exists
    exact le_trans hRB hRa
  have hcobdd_le : ∀ t, atTop.IsCoboundedUnder (· ≤ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    refine ⟨-B, fun a ha ↦ ?_⟩
    obtain ⟨R, hRa, hRB⟩ := ((eventually_atTop.2 ⟨1, fun R hR ↦
      (abs_le.mp (hB R hR)).1⟩).and ha).exists
    exact le_trans hRa hRB
  -- Step 1: the limsup at infinity is bounded by the value at every positive scale,
  -- up to the side-dependent error.
  have hle : ∀ t (L0 : ℝ), 0 < L0 →
      Filter.limsup (fun R ↦ f R t) atTop ≤ f L0 t + ε L0 := by
    intro t L0 hL0
    apply le_of_forall_pos_le_add
    intro η hη
    apply le_of_forall_lt
    intro h hh
    have hmain : h ≤ f L0 t + ε L0 := by
      apply le_of_forall_pos_le_add
      intro θ hθ
      have hcore : ∀ δ1 δ2 : ℝ, 0 < δ1 → 0 < δ2 →
          h - δ1 - δ2 ≤ f L0 t + ε L0 := by
        intro δ1 δ2 hδ1 hδ2
        let u : ℝ → ℝ := fun R ↦ f R t
        -- High values are frequent below the limsup.
        have hfreq : ∃ᶠ R : ℝ in atTop, h < u R :=
          frequently_lt_of_lt_limsup (hcobdd_le t) hh
        -- Build a sequence of high scales growing by a factor of four, with
        -- disjoint neighbourhoods on which `u` stays within `δ₁` of the spike.
        have hstep : ∀ x : ℝ, ∃ y : ℝ, 4 * x < y ∧ 0 < y ∧ h < u y := by
          intro x
          obtain ⟨y, hy, hhy⟩ :=
            (hfreq.and_eventually (eventually_ge_atTop (max (4 * x + 1) 1))).exists
          refine ⟨y, ?_, ?_, hy⟩
          · have : 4 * x + 1 ≤ y := le_trans (le_max_left _ _) hhy
            linarith
          · have : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hhy
            linarith
        let next : ℝ → ℝ := fun x ↦ Classical.choose (hstep x)
        have hnext : ∀ x : ℝ,
            4 * x < next x ∧ 0 < next x ∧ h < u (next x) :=
          fun x ↦ Classical.choose_spec (hstep x)
        let S : ℕ → ℝ := fun n ↦ next^[n + 1] 0
        have hS_succ : ∀ n : ℕ, S (n + 1) = next (S n) := by
          intro n
          simp only [S, Function.iterate_succ_apply']
        have hS_pos : ∀ n : ℕ, 0 < S n := by
          intro n
          rw [show S n = next (next^[n] 0) from by
            simp only [S, Function.iterate_succ_apply']]
          exact (hnext _).2.1
        have hS_high : ∀ n : ℕ, h < u (S n) := by
          intro n
          rw [show S n = next (next^[n] 0) from by
            simp only [S, Function.iterate_succ_apply']]
          exact (hnext _).2.2
        have hS_growth : ∀ n : ℕ, 4 * S n < S (n + 1) := by
          intro n
          rw [hS_succ n]
          exact (hnext (S n)).1
        have hS_lower : ∀ n : ℕ, (4 : ℝ) ^ n * S 0 ≤ S n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            rw [pow_succ]
            nlinarith [hS_growth n, hS_pos n]
        have hS_atTop : Tendsto S atTop atTop := by
          have hpow : Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n) atTop atTop :=
            tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)
          have hmul : Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n * S 0) atTop atTop := by
            simpa only [mul_comm] using
              (Tendsto.const_mul_atTop (hS_pos 0) hpow :
                Tendsto (fun n : ℕ ↦ S 0 * (4 : ℝ) ^ n) atTop atTop)
          exact tendsto_atTop_mono hS_lower hmul
        have hS_mono : Monotone S := by
          refine monotone_nat_of_le_succ fun n ↦ ?_
          have := hS_growth n
          have := hS_pos n
          linarith
        -- Continuity gives an interval around each spike.
        have hr : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ r ≤ S n / 8 ∧
            ∀ x : ℝ, |x - S n| < r → h - δ1 < u x := by
          intro n
          have hSnpos : 0 < S n := hS_pos n
          have hmem : {x : ℝ | h - δ1 < u x} ∈ 𝓝 (S n) :=
            (hcont t (S n) hSnpos).eventually
              (Ioi_mem_nhds (by linarith [hS_high n] : h - δ1 < u (S n)))
          obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.1 hmem
          refine ⟨min ρ (S n / 8), lt_min hρpos (by linarith), min_le_right _ _, ?_⟩
          intro x hx
          refine hρsub ?_
          rw [Metric.mem_ball, Real.dist_eq]
          exact lt_of_lt_of_le hx (min_le_left _ _)
        let r : ℕ → ℝ := fun n ↦ Classical.choose (hr n)
        have hr_spec : ∀ n : ℕ, 0 < r n ∧ r n ≤ S n / 8 ∧
            ∀ x : ℝ, |x - S n| < r n → h - δ1 < u x :=
          fun n ↦ Classical.choose_spec (hr n)
        let I : ℕ → Set ℝ := fun n ↦ Set.Ioo (S n - r n) (S n + r n)
        have hI_high : ∀ n : ℕ, ∀ x : ℝ, x ∈ I n → h - δ1 < u x := by
          intro n x hx
          apply (hr_spec n).2.2 x
          exact abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hI_pos : ∀ n : ℕ, ∀ x : ℝ, x ∈ I n → 0 < x := by
          intro n x hx
          have hr1 := (hr_spec n).1
          have hrle := (hr_spec n).2.1
          have hSp := hS_pos n
          have hx' : S n - r n < x := hx.1
          nlinarith
        have hI_sub : ∀ n : ℕ, I n ⊆ Set.Ioo (S n / 2) (2 * S n) := by
          intro n x hx
          have hrle := (hr_spec n).2.1
          have hSp := hS_pos n
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
        -- Side sets whose rays hit a spike.
        let B : ℕ → Set ℝ := fun n ↦ ⋃ m : ℕ, {L : ℝ | (m : ℝ) * L ∈ I n}
        let U : ℕ → Set ℝ := fun N ↦ ⋃ j : ℕ, B (N + j)
        have hB_open : ∀ n : ℕ, IsOpen (B n) := by
          intro n
          exact isOpen_iUnion fun m : ℕ ↦
            (continuous_const.mul continuous_id :
              Continuous (fun L : ℝ ↦ (m : ℝ) * L)).isOpen_preimage (I n) (isOpen_Ioo)
        have hU_open : ∀ N : ℕ, IsOpen (U N) := fun N ↦
          isOpen_iUnion fun j : ℕ ↦ hB_open (N + j)
        -- Every interval contains a scale whose ray hits a spike.
        have hinter : ∀ (N : ℕ) (a b : ℝ), 0 < a → a < b →
            ∃ L : ℝ, a < L ∧ L < b ∧ L ∈ U N := by
          intro N a b ha hab
          have hbpos : 0 < b := by linarith
          have hbma : 0 < b - a := by linarith
          set c : ℝ := max (2 * b ^ 2 / (b - a)) b with hc
          have hev : ∀ᶠ n : ℕ in atTop, c < S n :=
            hS_atTop.eventually (eventually_gt_atTop c)
          obtain ⟨n, hnlarge, hnge⟩ := (hev.and (eventually_ge_atTop N)).exists
          have hSnpos : 0 < S n := hS_pos n
          let m : ℕ := Nat.ceil (S n / b) + 1
          let L : ℝ := S n / (m : ℝ)
          have hmpos_nat : 0 < m := Nat.succ_pos _
          have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
          have hmul : (m : ℝ) * L = S n := by
            show (m : ℝ) * (S n / (m : ℝ)) = S n
            exact mul_div_cancel₀ (S n) (ne_of_gt hmpos)
          have hSnI : S n ∈ I n := by
            exact ⟨by linarith [(hr_spec n).1], by linarith [(hr_spec n).1]⟩
          have hLmemB : L ∈ B n := by
            refine Set.mem_iUnion.2 ⟨m, ?_⟩
            change (m : ℝ) * L ∈ I n
            rwa [hmul]
          have hLU : L ∈ U N := by
            refine Set.mem_iUnion.2 ⟨n - N, ?_⟩
            rwa [Nat.add_sub_of_le hnge]
          have hm_gt : S n / b < (m : ℝ) := by
            have h1 : (Nat.ceil (S n / b) : ℝ) ≥ S n / b := Nat.le_ceil _
            have hm : (m : ℝ) = (Nat.ceil (S n / b) : ℝ) + 1 := by
              simp only [m, Nat.cast_add, Nat.cast_one]
            rw [hm]
            linarith
          have hLb : L < b := by
            show S n / (m : ℝ) < b
            rw [div_lt_iff₀ hmpos]
            have h1 : S n < (m : ℝ) * b := by
              rw [← div_lt_iff₀ hbpos]
              exact hm_gt
            linarith
          have hm_lt : (m : ℝ) < S n / b + 2 := by
            have h1 : (Nat.ceil (S n / b) : ℝ) < S n / b + 1 :=
              Nat.ceil_lt_add_one (le_of_lt (div_pos hSnpos hbpos))
            have hm : (m : ℝ) = (Nat.ceil (S n / b) : ℝ) + 1 := by
              simp only [m, Nat.cast_add, Nat.cast_one]
            rw [hm]
            linarith
          have hkey : a * (S n / b + 2) ≤ S n := by
            have hrewrite : a * (S n / b + 2) = a * (S n + 2 * b) / b := by
              field_simp
            rw [hrewrite, div_le_iff₀ hbpos]
            have hlarge : 2 * b ^ 2 < S n * (b - a) := by
              have h1 : 2 * b ^ 2 / (b - a) < S n :=
                lt_of_le_of_lt (le_max_left _ _) hnlarge
              exact (div_lt_iff₀ hbma).1 h1
            have hab' : a * b ≤ b ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_right ha.le hbpos.le]
            nlinarith
          have hLa : a < L := by
            show a < S n / (m : ℝ)
            rw [lt_div_iff₀ hmpos]
            have h1 : a * (m : ℝ) < a * (S n / b + 2) :=
              mul_lt_mul_of_pos_left hm_lt ha
            linarith
          exact ⟨L, hLa, hLb, hLU⟩
        -- The union sets are dense in the positive half-line.
        let P : Set ℝ := Set.Ioi 0
        let V : ℕ → Set P := fun N ↦ {x : P | (x : ℝ) ∈ U N}
        have hV_open : ∀ N : ℕ, IsOpen (V N) := by
          intro N
          exact continuous_subtype_val.isOpen_preimage (U N) (hU_open N)
        have hV_dense : ∀ N : ℕ, Dense (V N) := by
          intro N
          rw [dense_iff_inter_open]
          intro O hO hOne
          obtain ⟨x, hxO⟩ := hOne
          obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.1 (hO.mem_nhds hxO)
          have hxpos : (0 : ℝ) < (x : ℝ) := x.2
          set d : ℝ := min (ρ / 2) ((x : ℝ) / 2) with hd
          have hdpos : 0 < d := lt_min (by linarith) (by linarith)
          have hdρ : d ≤ ρ := by
            have h1 : d ≤ ρ / 2 := min_le_left _ _
            linarith
          have hdx : d ≤ (x : ℝ) / 2 := min_le_right _ _
          have ha : 0 < (x : ℝ) - d := by linarith
          have hab : (x : ℝ) - d < (x : ℝ) + d := by linarith
          obtain ⟨L, hLa, hLb, hLU⟩ := hinter N ((x : ℝ) - d) ((x : ℝ) + d) ha hab
          have hLpos : 0 < L := by linarith
          let x' : P := ⟨L, by simpa [P] using hLpos⟩
          have hx'ball : x' ∈ Metric.ball x ρ := by
            rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
            exact abs_lt.2 ⟨by linarith, by linarith⟩
          have hx'O : x' ∈ O := hρsub hx'ball
          have hx'V : x' ∈ V N := hLU
          exact ⟨x', hx'O, hx'V⟩
        -- Baire: the scales whose rays hit infinitely many spikes are dense.
        have hBaire : Dense (⋂ N : ℕ, V N) :=
          @dense_iInter_of_isOpen_nat P _ (isOpen_Ioi.baireSpace) V hV_open hV_dense
        let x0 : P := ⟨L0, by simpa [P] using hL0⟩
        have hnear : ∀ n : ℕ, ∃ y : P, y ∈ (⋂ N : ℕ, V N) ∧
            dist y x0 < 1 / ((n : ℝ) + 1) := by
          intro n
          have hεpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
          have hball_open : IsOpen (Metric.ball x0 (1 / ((n : ℝ) + 1))) :=
            Metric.isOpen_ball
          have hball_ne : (Metric.ball x0 (1 / ((n : ℝ) + 1))).Nonempty :=
            ⟨x0, Metric.mem_ball_self hεpos⟩
          obtain ⟨y, hyball, hyB⟩ :=
            (dense_iff_inter_open.1 hBaire) _ hball_open hball_ne
          exact ⟨y, hyB, by rwa [Metric.mem_ball] at hyball⟩
        let y : ℕ → P := fun n ↦ Classical.choose (hnear n)
        have hy_spec : ∀ n : ℕ, y n ∈ (⋂ N : ℕ, V N) ∧
            dist (y n) x0 < 1 / ((n : ℝ) + 1) :=
          fun n ↦ Classical.choose_spec (hnear n)
        let Lseq : ℕ → ℝ := fun n ↦ (y n : ℝ)
        have hLseq_pos : ∀ n : ℕ, 0 < Lseq n := fun n ↦ (y n).2
        have hLseq_dist : ∀ n : ℕ, |Lseq n - L0| < 1 / ((n : ℝ) + 1) := by
          intro n
          have h := (hy_spec n).2
          rwa [Subtype.dist_eq, Real.dist_eq] at h
        have hLseq_tendsto : Tendsto Lseq atTop (𝓝 L0) := by
          refine tendsto_iff_dist_tendsto_zero.2 ?_
          have hdist_eq : ∀ n : ℕ, dist (Lseq n) L0 = |Lseq n - L0| :=
            fun n ↦ Real.dist_eq _ _
          refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
            (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat)
          rw [hdist_eq n]
          exact le_of_lt (hLseq_dist n)
        -- Each limit scale has rays hitting spikes at arbitrarily large multipliers.
        have hupper : ∀ n : ℕ, h - δ1 - δ2 ≤ u (Lseq n) + ε (Lseq n) := by
          intro n
          have hyB : ∀ N : ℕ, Lseq n ∈ U N := by
            intro N
            exact (Set.mem_iInter.1 (hy_spec n).1 N : Lseq n ∈ U N)
          have hhit_inf : ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ ∃ m : ℕ,
              (m : ℝ) * Lseq n ∈ I j := by
            intro N
            have hmemU : Lseq n ∈ U N := hyB N
            change Lseq n ∈ ⋃ j : ℕ, B (N + j) at hmemU
            rw [Set.mem_iUnion] at hmemU
            obtain ⟨j, hj⟩ := hmemU
            change Lseq n ∈ ⋃ m : ℕ, {L : ℝ | (m : ℝ) * L ∈ I (N + j)} at hj
            rw [Set.mem_iUnion] at hj
            obtain ⟨m, hm⟩ := hj
            change (m : ℝ) * Lseq n ∈ I (N + j) at hm
            exact ⟨N + j, Nat.le_add_right N j, m, hm⟩
          obtain ⟨M, hM⟩ := eventually_atTop.1
            (hblock t (Lseq n) (hLseq_pos n) δ2 hδ2)
          -- Choose a hit far enough out that its multiplier exceeds the threshold.
          obtain ⟨N, hN⟩ : ∃ N : ℕ, (M : ℝ) * (2 * Lseq n) ≤ S N :=
            (hS_atTop.eventually (eventually_ge_atTop ((M : ℝ) * (2 * Lseq n)))).exists
          obtain ⟨j, hjN, m, hm⟩ := hhit_inf N
          have hm_gt : (M : ℝ) < (m : ℝ) := by
            have hsub := hI_sub j hm
            have hSNle : S N ≤ S j := hS_mono hjN
            have hML : (M : ℝ) * Lseq n ≤ S N / 2 := by
              nlinarith [hN, hLseq_pos n]
            have h1 : (M : ℝ) * Lseq n < (m : ℝ) * Lseq n := by
              have h2 : S N / 2 ≤ S j / 2 := by linarith
              linarith [hsub.1, hML, h2]
            exact lt_of_mul_lt_mul_right h1 (le_of_lt (hLseq_pos n))
          have hmM : M ≤ m := by exact_mod_cast le_of_lt hm_gt
          have hineq := hM m hmM
          have hhigh : h - δ1 < u ((m : ℝ) * Lseq n) := hI_high j _ hm
          show h - δ1 - δ2 ≤ u (Lseq n) + ε (Lseq n)
          linarith
        have hsum : Tendsto (fun n : ℕ ↦ u (Lseq n) + ε (Lseq n)) atTop
            (𝓝 (u L0 + ε L0)) :=
          ((hcont t L0 hL0).comp hLseq_tendsto).add
            ((hεcont L0 hL0).comp hLseq_tendsto)
        exact le_of_tendsto_of_tendsto tendsto_const_nhds hsum
          (Filter.Eventually.of_forall hupper)
      have hcore' := hcore (θ / 4) (θ / 4) (by linarith) (by linarith)
      linarith
    linarith
  -- Step 2: limsup is at most liminf.
  have hlimsup_le_liminf : ∀ t,
      Filter.limsup (fun R ↦ f R t) atTop ≤ Filter.liminf (fun R ↦ f R t) atTop := by
    intro t
    apply le_of_forall_pos_le_add
    intro η hη
    have hη2 : 0 < η / 2 := by linarith
    have hfreq : ∃ᶠ R : ℝ in atTop,
        f R t < Filter.liminf (fun R ↦ f R t) atTop + η / 2 :=
      frequently_lt_of_liminf_lt (hcobdd_ge t) (by linarith)
    have hεsmall : ∀ᶠ R : ℝ in atTop, ε R < η / 2 :=
      hε0.eventually (Iio_mem_nhds hη2)
    obtain ⟨R, hRlow, hR1, hRsmall⟩ :=
      (hfreq.and_eventually ((eventually_ge_atTop (1 : ℝ)).and hεsmall)).exists
    have hRpos : 0 < R := by linarith
    have hleR : Filter.limsup (fun R ↦ f R t) atTop ≤ f R t + ε R := hle t R hRpos
    linarith
  -- Step 3: the common value is the limit at every tilt.
  let p : ℝ → ℝ := fun t ↦ Filter.liminf (fun R ↦ f R t) atTop
  have hlim_eq : ∀ t, Filter.liminf (fun R ↦ f R t) atTop =
      Filter.limsup (fun R ↦ f R t) atTop := by
    intro t
    exact le_antisymm (Filter.liminf_le_limsup (hbdd_le t) (hbdd_ge t))
      (hlimsup_le_liminf t)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro t
    exact tendsto_of_liminf_eq_limsup rfl (hlim_eq t).symm (hbdd_le t) (hbdd_ge t)
  · -- Concavity passes to the pointwise limit.
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hx : Tendsto (fun R ↦ f R x) atTop (𝓝 (p x)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq x).symm (hbdd_le x) (hbdd_ge x)
    have hy : Tendsto (fun R ↦ f R y) atTop (𝓝 (p y)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq y).symm (hbdd_le y) (hbdd_ge y)
    have hxy : Tendsto (fun R ↦ f R (a * x + b * y)) atTop
        (𝓝 (p (a * x + b * y))) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq (a * x + b * y)).symm
        (hbdd_le _) (hbdd_ge _)
    have hlim : Tendsto (fun R ↦ a * f R x + b * f R y) atTop
        (𝓝 (a * p x + b * p y)) :=
      (hx.const_mul a).add (hy.const_mul b)
    have hev : ∀ᶠ R in atTop, a * f R x + b * f R y ≤ f R (a * x + b * y) :=
      Filter.Eventually.of_forall fun R ↦ (hconcave R).2 (mem_univ x) (mem_univ y) ha hb hab
    have hle' : a * p x + b * p y ≤ p (a * x + b * y) :=
      le_of_tendsto_of_tendsto hlim hxy hev
    simpa only [smul_eq_mul] using hle'
  · -- The Lipschitz bound passes to the pointwise limit.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hx : Tendsto (fun R ↦ f R x) atTop (𝓝 (p x)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq x).symm (hbdd_le x) (hbdd_ge x)
    have hy : Tendsto (fun R ↦ f R y) atTop (𝓝 (p y)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq y).symm (hbdd_le y) (hbdd_ge y)
    have hdiff : Tendsto (fun R ↦ f R x - f R y) atTop (𝓝 (p x - p y)) := hx.sub hy
    have hbound : Tendsto (fun R ↦ |f R x - f R y|) atTop (𝓝 (|p x - p y|)) :=
      hdiff.abs
    have hconst : Tendsto (fun _ : ℝ ↦ G * |x - y|) atTop (𝓝 (G * |x - y|)) :=
      tendsto_const_nhds
    have hev : ∀ᶠ R in atTop, |f R x - f R y| ≤ G * |x - y| :=
      Filter.Eventually.of_forall fun R ↦ hlip R x y
    have := le_of_tendsto_of_tendsto hbound hconst hev
    rw [Real.dist_eq, Real.dist_eq]
    exact this


theorem exists_tendsto_of_block_subadditive_of_tiltError
    {f : ℝ → ℝ → ℝ} {G : ℝ} (hG : 0 ≤ G)
    (hbdd : ∀ t, ∃ B : ℝ, ∀ R : ℝ, 1 ≤ R → |f R t| ≤ B)
    (hconcave : ∀ R, ConcaveOn ℝ univ (f R))
    (hlip : ∀ R t u, |f R t - f R u| ≤ G * |t - u|)
    (hcont : ∀ t L, 0 < L → Tendsto (fun R ↦ f R t) (𝓝 L) (𝓝 (f L t)))
    (ε : ℝ → ℝ → ℝ)
    (hεcont : ∀ t L, 0 < L → Tendsto (fun L' => ε t L') (𝓝 L) (𝓝 (ε t L)))
    (hε0 : ∀ t, Tendsto (fun L => ε t L) atTop (𝓝 0))
    (hblock : ∀ t L : ℝ, 0 < L → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m : ℕ in atTop, f ((m : ℝ) * L) t ≤ f L t + ε t L + δ) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (fun R ↦ f R t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ univ p ∧ LipschitzWith ⟨G, hG⟩ p := by
  -- Uniform one-sided boundedness of every tilt sequence.
  have hbdd_le : ∀ t, atTop.IsBoundedUnder (· ≤ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    exact ⟨B, eventually_atTop.2 ⟨1, fun R hR ↦ (abs_le.mp (hB R hR)).2⟩⟩
  have hbdd_ge : ∀ t, atTop.IsBoundedUnder (· ≥ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    exact ⟨-B, eventually_atTop.2 ⟨1, fun R hR ↦ (abs_le.mp (hB R hR)).1⟩⟩
  have hcobdd_ge : ∀ t, atTop.IsCoboundedUnder (· ≥ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    refine ⟨B, fun a ha ↦ ?_⟩
    obtain ⟨R, hRa, hRB⟩ := ((eventually_atTop.2 ⟨1, fun R hR ↦
      (abs_le.mp (hB R hR)).2⟩).and ha).exists
    exact le_trans hRB hRa
  have hcobdd_le : ∀ t, atTop.IsCoboundedUnder (· ≤ ·) (fun R ↦ f R t) := by
    intro t
    obtain ⟨B, hB⟩ := hbdd t
    refine ⟨-B, fun a ha ↦ ?_⟩
    obtain ⟨R, hRa, hRB⟩ := ((eventually_atTop.2 ⟨1, fun R hR ↦
      (abs_le.mp (hB R hR)).1⟩).and ha).exists
    exact le_trans hRa hRB
  -- Step 1: the limsup at infinity is bounded by the value at every positive scale,
  -- up to the side-dependent error.
  have hle : ∀ t (L0 : ℝ), 0 < L0 →
      Filter.limsup (fun R ↦ f R t) atTop ≤ f L0 t + ε t L0 := by
    intro t L0 hL0
    apply le_of_forall_pos_le_add
    intro η hη
    apply le_of_forall_lt
    intro h hh
    have hmain : h ≤ f L0 t + ε t L0 := by
      apply le_of_forall_pos_le_add
      intro θ hθ
      have hcore : ∀ δ1 δ2 : ℝ, 0 < δ1 → 0 < δ2 →
          h - δ1 - δ2 ≤ f L0 t + ε t L0 := by
        intro δ1 δ2 hδ1 hδ2
        let u : ℝ → ℝ := fun R ↦ f R t
        -- High values are frequent below the limsup.
        have hfreq : ∃ᶠ R : ℝ in atTop, h < u R :=
          frequently_lt_of_lt_limsup (hcobdd_le t) hh
        -- Build a sequence of high scales growing by a factor of four, with
        -- disjoint neighbourhoods on which `u` stays within `δ₁` of the spike.
        have hstep : ∀ x : ℝ, ∃ y : ℝ, 4 * x < y ∧ 0 < y ∧ h < u y := by
          intro x
          obtain ⟨y, hy, hhy⟩ :=
            (hfreq.and_eventually (eventually_ge_atTop (max (4 * x + 1) 1))).exists
          refine ⟨y, ?_, ?_, hy⟩
          · have : 4 * x + 1 ≤ y := le_trans (le_max_left _ _) hhy
            linarith
          · have : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hhy
            linarith
        let next : ℝ → ℝ := fun x ↦ Classical.choose (hstep x)
        have hnext : ∀ x : ℝ,
            4 * x < next x ∧ 0 < next x ∧ h < u (next x) :=
          fun x ↦ Classical.choose_spec (hstep x)
        let S : ℕ → ℝ := fun n ↦ next^[n + 1] 0
        have hS_succ : ∀ n : ℕ, S (n + 1) = next (S n) := by
          intro n
          simp only [S, Function.iterate_succ_apply']
        have hS_pos : ∀ n : ℕ, 0 < S n := by
          intro n
          rw [show S n = next (next^[n] 0) from by
            simp only [S, Function.iterate_succ_apply']]
          exact (hnext _).2.1
        have hS_high : ∀ n : ℕ, h < u (S n) := by
          intro n
          rw [show S n = next (next^[n] 0) from by
            simp only [S, Function.iterate_succ_apply']]
          exact (hnext _).2.2
        have hS_growth : ∀ n : ℕ, 4 * S n < S (n + 1) := by
          intro n
          rw [hS_succ n]
          exact (hnext (S n)).1
        have hS_lower : ∀ n : ℕ, (4 : ℝ) ^ n * S 0 ≤ S n := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
            rw [pow_succ]
            nlinarith [hS_growth n, hS_pos n]
        have hS_atTop : Tendsto S atTop atTop := by
          have hpow : Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n) atTop atTop :=
            tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)
          have hmul : Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n * S 0) atTop atTop := by
            simpa only [mul_comm] using
              (Tendsto.const_mul_atTop (hS_pos 0) hpow :
                Tendsto (fun n : ℕ ↦ S 0 * (4 : ℝ) ^ n) atTop atTop)
          exact tendsto_atTop_mono hS_lower hmul
        have hS_mono : Monotone S := by
          refine monotone_nat_of_le_succ fun n ↦ ?_
          have := hS_growth n
          have := hS_pos n
          linarith
        -- Continuity gives an interval around each spike.
        have hr : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ r ≤ S n / 8 ∧
            ∀ x : ℝ, |x - S n| < r → h - δ1 < u x := by
          intro n
          have hSnpos : 0 < S n := hS_pos n
          have hmem : {x : ℝ | h - δ1 < u x} ∈ 𝓝 (S n) :=
            (hcont t (S n) hSnpos).eventually
              (Ioi_mem_nhds (by linarith [hS_high n] : h - δ1 < u (S n)))
          obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.1 hmem
          refine ⟨min ρ (S n / 8), lt_min hρpos (by linarith), min_le_right _ _, ?_⟩
          intro x hx
          refine hρsub ?_
          rw [Metric.mem_ball, Real.dist_eq]
          exact lt_of_lt_of_le hx (min_le_left _ _)
        let r : ℕ → ℝ := fun n ↦ Classical.choose (hr n)
        have hr_spec : ∀ n : ℕ, 0 < r n ∧ r n ≤ S n / 8 ∧
            ∀ x : ℝ, |x - S n| < r n → h - δ1 < u x :=
          fun n ↦ Classical.choose_spec (hr n)
        let I : ℕ → Set ℝ := fun n ↦ Set.Ioo (S n - r n) (S n + r n)
        have hI_high : ∀ n : ℕ, ∀ x : ℝ, x ∈ I n → h - δ1 < u x := by
          intro n x hx
          apply (hr_spec n).2.2 x
          exact abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hI_pos : ∀ n : ℕ, ∀ x : ℝ, x ∈ I n → 0 < x := by
          intro n x hx
          have hr1 := (hr_spec n).1
          have hrle := (hr_spec n).2.1
          have hSp := hS_pos n
          have hx' : S n - r n < x := hx.1
          nlinarith
        have hI_sub : ∀ n : ℕ, I n ⊆ Set.Ioo (S n / 2) (2 * S n) := by
          intro n x hx
          have hrle := (hr_spec n).2.1
          have hSp := hS_pos n
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
        -- Side sets whose rays hit a spike.
        let B : ℕ → Set ℝ := fun n ↦ ⋃ m : ℕ, {L : ℝ | (m : ℝ) * L ∈ I n}
        let U : ℕ → Set ℝ := fun N ↦ ⋃ j : ℕ, B (N + j)
        have hB_open : ∀ n : ℕ, IsOpen (B n) := by
          intro n
          exact isOpen_iUnion fun m : ℕ ↦
            (continuous_const.mul continuous_id :
              Continuous (fun L : ℝ ↦ (m : ℝ) * L)).isOpen_preimage (I n) (isOpen_Ioo)
        have hU_open : ∀ N : ℕ, IsOpen (U N) := fun N ↦
          isOpen_iUnion fun j : ℕ ↦ hB_open (N + j)
        -- Every interval contains a scale whose ray hits a spike.
        have hinter : ∀ (N : ℕ) (a b : ℝ), 0 < a → a < b →
            ∃ L : ℝ, a < L ∧ L < b ∧ L ∈ U N := by
          intro N a b ha hab
          have hbpos : 0 < b := by linarith
          have hbma : 0 < b - a := by linarith
          set c : ℝ := max (2 * b ^ 2 / (b - a)) b with hc
          have hev : ∀ᶠ n : ℕ in atTop, c < S n :=
            hS_atTop.eventually (eventually_gt_atTop c)
          obtain ⟨n, hnlarge, hnge⟩ := (hev.and (eventually_ge_atTop N)).exists
          have hSnpos : 0 < S n := hS_pos n
          let m : ℕ := Nat.ceil (S n / b) + 1
          let L : ℝ := S n / (m : ℝ)
          have hmpos_nat : 0 < m := Nat.succ_pos _
          have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos_nat
          have hmul : (m : ℝ) * L = S n := by
            show (m : ℝ) * (S n / (m : ℝ)) = S n
            exact mul_div_cancel₀ (S n) (ne_of_gt hmpos)
          have hSnI : S n ∈ I n := by
            exact ⟨by linarith [(hr_spec n).1], by linarith [(hr_spec n).1]⟩
          have hLmemB : L ∈ B n := by
            refine Set.mem_iUnion.2 ⟨m, ?_⟩
            change (m : ℝ) * L ∈ I n
            rwa [hmul]
          have hLU : L ∈ U N := by
            refine Set.mem_iUnion.2 ⟨n - N, ?_⟩
            rwa [Nat.add_sub_of_le hnge]
          have hm_gt : S n / b < (m : ℝ) := by
            have h1 : (Nat.ceil (S n / b) : ℝ) ≥ S n / b := Nat.le_ceil _
            have hm : (m : ℝ) = (Nat.ceil (S n / b) : ℝ) + 1 := by
              simp only [m, Nat.cast_add, Nat.cast_one]
            rw [hm]
            linarith
          have hLb : L < b := by
            show S n / (m : ℝ) < b
            rw [div_lt_iff₀ hmpos]
            have h1 : S n < (m : ℝ) * b := by
              rw [← div_lt_iff₀ hbpos]
              exact hm_gt
            linarith
          have hm_lt : (m : ℝ) < S n / b + 2 := by
            have h1 : (Nat.ceil (S n / b) : ℝ) < S n / b + 1 :=
              Nat.ceil_lt_add_one (le_of_lt (div_pos hSnpos hbpos))
            have hm : (m : ℝ) = (Nat.ceil (S n / b) : ℝ) + 1 := by
              simp only [m, Nat.cast_add, Nat.cast_one]
            rw [hm]
            linarith
          have hkey : a * (S n / b + 2) ≤ S n := by
            have hrewrite : a * (S n / b + 2) = a * (S n + 2 * b) / b := by
              field_simp
            rw [hrewrite, div_le_iff₀ hbpos]
            have hlarge : 2 * b ^ 2 < S n * (b - a) := by
              have h1 : 2 * b ^ 2 / (b - a) < S n :=
                lt_of_le_of_lt (le_max_left _ _) hnlarge
              exact (div_lt_iff₀ hbma).1 h1
            have hab' : a * b ≤ b ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_right ha.le hbpos.le]
            nlinarith
          have hLa : a < L := by
            show a < S n / (m : ℝ)
            rw [lt_div_iff₀ hmpos]
            have h1 : a * (m : ℝ) < a * (S n / b + 2) :=
              mul_lt_mul_of_pos_left hm_lt ha
            linarith
          exact ⟨L, hLa, hLb, hLU⟩
        -- The union sets are dense in the positive half-line.
        let P : Set ℝ := Set.Ioi 0
        let V : ℕ → Set P := fun N ↦ {x : P | (x : ℝ) ∈ U N}
        have hV_open : ∀ N : ℕ, IsOpen (V N) := by
          intro N
          exact continuous_subtype_val.isOpen_preimage (U N) (hU_open N)
        have hV_dense : ∀ N : ℕ, Dense (V N) := by
          intro N
          rw [dense_iff_inter_open]
          intro O hO hOne
          obtain ⟨x, hxO⟩ := hOne
          obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.1 (hO.mem_nhds hxO)
          have hxpos : (0 : ℝ) < (x : ℝ) := x.2
          set d : ℝ := min (ρ / 2) ((x : ℝ) / 2) with hd
          have hdpos : 0 < d := lt_min (by linarith) (by linarith)
          have hdρ : d ≤ ρ := by
            have h1 : d ≤ ρ / 2 := min_le_left _ _
            linarith
          have hdx : d ≤ (x : ℝ) / 2 := min_le_right _ _
          have ha : 0 < (x : ℝ) - d := by linarith
          have hab : (x : ℝ) - d < (x : ℝ) + d := by linarith
          obtain ⟨L, hLa, hLb, hLU⟩ := hinter N ((x : ℝ) - d) ((x : ℝ) + d) ha hab
          have hLpos : 0 < L := by linarith
          let x' : P := ⟨L, by simpa [P] using hLpos⟩
          have hx'ball : x' ∈ Metric.ball x ρ := by
            rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
            exact abs_lt.2 ⟨by linarith, by linarith⟩
          have hx'O : x' ∈ O := hρsub hx'ball
          have hx'V : x' ∈ V N := hLU
          exact ⟨x', hx'O, hx'V⟩
        -- Baire: the scales whose rays hit infinitely many spikes are dense.
        have hBaire : Dense (⋂ N : ℕ, V N) :=
          @dense_iInter_of_isOpen_nat P _ (isOpen_Ioi.baireSpace) V hV_open hV_dense
        let x0 : P := ⟨L0, by simpa [P] using hL0⟩
        have hnear : ∀ n : ℕ, ∃ y : P, y ∈ (⋂ N : ℕ, V N) ∧
            dist y x0 < 1 / ((n : ℝ) + 1) := by
          intro n
          have hεpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
          have hball_open : IsOpen (Metric.ball x0 (1 / ((n : ℝ) + 1))) :=
            Metric.isOpen_ball
          have hball_ne : (Metric.ball x0 (1 / ((n : ℝ) + 1))).Nonempty :=
            ⟨x0, Metric.mem_ball_self hεpos⟩
          obtain ⟨y, hyball, hyB⟩ :=
            (dense_iff_inter_open.1 hBaire) _ hball_open hball_ne
          exact ⟨y, hyB, by rwa [Metric.mem_ball] at hyball⟩
        let y : ℕ → P := fun n ↦ Classical.choose (hnear n)
        have hy_spec : ∀ n : ℕ, y n ∈ (⋂ N : ℕ, V N) ∧
            dist (y n) x0 < 1 / ((n : ℝ) + 1) :=
          fun n ↦ Classical.choose_spec (hnear n)
        let Lseq : ℕ → ℝ := fun n ↦ (y n : ℝ)
        have hLseq_pos : ∀ n : ℕ, 0 < Lseq n := fun n ↦ (y n).2
        have hLseq_dist : ∀ n : ℕ, |Lseq n - L0| < 1 / ((n : ℝ) + 1) := by
          intro n
          have h := (hy_spec n).2
          rwa [Subtype.dist_eq, Real.dist_eq] at h
        have hLseq_tendsto : Tendsto Lseq atTop (𝓝 L0) := by
          refine tendsto_iff_dist_tendsto_zero.2 ?_
          have hdist_eq : ∀ n : ℕ, dist (Lseq n) L0 = |Lseq n - L0| :=
            fun n ↦ Real.dist_eq _ _
          refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_)
            (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat)
          rw [hdist_eq n]
          exact le_of_lt (hLseq_dist n)
        -- Each limit scale has rays hitting spikes at arbitrarily large multipliers.
        have hupper : ∀ n : ℕ, h - δ1 - δ2 ≤ u (Lseq n) + ε t (Lseq n) := by
          intro n
          have hyB : ∀ N : ℕ, Lseq n ∈ U N := by
            intro N
            exact (Set.mem_iInter.1 (hy_spec n).1 N : Lseq n ∈ U N)
          have hhit_inf : ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ ∃ m : ℕ,
              (m : ℝ) * Lseq n ∈ I j := by
            intro N
            have hmemU : Lseq n ∈ U N := hyB N
            change Lseq n ∈ ⋃ j : ℕ, B (N + j) at hmemU
            rw [Set.mem_iUnion] at hmemU
            obtain ⟨j, hj⟩ := hmemU
            change Lseq n ∈ ⋃ m : ℕ, {L : ℝ | (m : ℝ) * L ∈ I (N + j)} at hj
            rw [Set.mem_iUnion] at hj
            obtain ⟨m, hm⟩ := hj
            change (m : ℝ) * Lseq n ∈ I (N + j) at hm
            exact ⟨N + j, Nat.le_add_right N j, m, hm⟩
          obtain ⟨M, hM⟩ := eventually_atTop.1
            (hblock t (Lseq n) (hLseq_pos n) δ2 hδ2)
          -- Choose a hit far enough out that its multiplier exceeds the threshold.
          obtain ⟨N, hN⟩ : ∃ N : ℕ, (M : ℝ) * (2 * Lseq n) ≤ S N :=
            (hS_atTop.eventually (eventually_ge_atTop ((M : ℝ) * (2 * Lseq n)))).exists
          obtain ⟨j, hjN, m, hm⟩ := hhit_inf N
          have hm_gt : (M : ℝ) < (m : ℝ) := by
            have hsub := hI_sub j hm
            have hSNle : S N ≤ S j := hS_mono hjN
            have hML : (M : ℝ) * Lseq n ≤ S N / 2 := by
              nlinarith [hN, hLseq_pos n]
            have h1 : (M : ℝ) * Lseq n < (m : ℝ) * Lseq n := by
              have h2 : S N / 2 ≤ S j / 2 := by linarith
              linarith [hsub.1, hML, h2]
            exact lt_of_mul_lt_mul_right h1 (le_of_lt (hLseq_pos n))
          have hmM : M ≤ m := by exact_mod_cast le_of_lt hm_gt
          have hineq := hM m hmM
          have hhigh : h - δ1 < u ((m : ℝ) * Lseq n) := hI_high j _ hm
          show h - δ1 - δ2 ≤ u (Lseq n) + ε t (Lseq n)
          linarith
        have hsum : Tendsto (fun n : ℕ ↦ u (Lseq n) + ε t (Lseq n)) atTop
            (𝓝 (u L0 + ε t L0)) :=
          ((hcont t L0 hL0).comp hLseq_tendsto).add
            ((hεcont t L0 hL0).comp hLseq_tendsto)
        exact le_of_tendsto_of_tendsto tendsto_const_nhds hsum
          (Filter.Eventually.of_forall hupper)
      have hcore' := hcore (θ / 4) (θ / 4) (by linarith) (by linarith)
      linarith
    linarith
  -- Step 2: limsup is at most liminf.
  have hlimsup_le_liminf : ∀ t,
      Filter.limsup (fun R ↦ f R t) atTop ≤ Filter.liminf (fun R ↦ f R t) atTop := by
    intro t
    apply le_of_forall_pos_le_add
    intro η hη
    have hη2 : 0 < η / 2 := by linarith
    have hfreq : ∃ᶠ R : ℝ in atTop,
        f R t < Filter.liminf (fun R ↦ f R t) atTop + η / 2 :=
      frequently_lt_of_liminf_lt (hcobdd_ge t) (by linarith)
    have hεsmall : ∀ᶠ R : ℝ in atTop, ε t R < η / 2 :=
      (hε0 t).eventually (Iio_mem_nhds hη2)
    obtain ⟨R, hRlow, hR1, hRsmall⟩ :=
      (hfreq.and_eventually ((eventually_ge_atTop (1 : ℝ)).and hεsmall)).exists
    have hRpos : 0 < R := by linarith
    have hleR : Filter.limsup (fun R ↦ f R t) atTop ≤ f R t + ε t R := hle t R hRpos
    linarith
  -- Step 3: the common value is the limit at every tilt.
  let p : ℝ → ℝ := fun t ↦ Filter.liminf (fun R ↦ f R t) atTop
  have hlim_eq : ∀ t, Filter.liminf (fun R ↦ f R t) atTop =
      Filter.limsup (fun R ↦ f R t) atTop := by
    intro t
    exact le_antisymm (Filter.liminf_le_limsup (hbdd_le t) (hbdd_ge t))
      (hlimsup_le_liminf t)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro t
    exact tendsto_of_liminf_eq_limsup rfl (hlim_eq t).symm (hbdd_le t) (hbdd_ge t)
  · -- Concavity passes to the pointwise limit.
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hx : Tendsto (fun R ↦ f R x) atTop (𝓝 (p x)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq x).symm (hbdd_le x) (hbdd_ge x)
    have hy : Tendsto (fun R ↦ f R y) atTop (𝓝 (p y)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq y).symm (hbdd_le y) (hbdd_ge y)
    have hxy : Tendsto (fun R ↦ f R (a * x + b * y)) atTop
        (𝓝 (p (a * x + b * y))) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq (a * x + b * y)).symm
        (hbdd_le _) (hbdd_ge _)
    have hlim : Tendsto (fun R ↦ a * f R x + b * f R y) atTop
        (𝓝 (a * p x + b * p y)) :=
      (hx.const_mul a).add (hy.const_mul b)
    have hev : ∀ᶠ R in atTop, a * f R x + b * f R y ≤ f R (a * x + b * y) :=
      Filter.Eventually.of_forall fun R ↦ (hconcave R).2 (mem_univ x) (mem_univ y) ha hb hab
    have hle' : a * p x + b * p y ≤ p (a * x + b * y) :=
      le_of_tendsto_of_tendsto hlim hxy hev
    simpa only [smul_eq_mul] using hle'
  · -- The Lipschitz bound passes to the pointwise limit.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hx : Tendsto (fun R ↦ f R x) atTop (𝓝 (p x)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq x).symm (hbdd_le x) (hbdd_ge x)
    have hy : Tendsto (fun R ↦ f R y) atTop (𝓝 (p y)) :=
      tendsto_of_liminf_eq_limsup rfl (hlim_eq y).symm (hbdd_le y) (hbdd_ge y)
    have hdiff : Tendsto (fun R ↦ f R x - f R y) atTop (𝓝 (p x - p y)) := hx.sub hy
    have hbound : Tendsto (fun R ↦ |f R x - f R y|) atTop (𝓝 (|p x - p y|)) :=
      hdiff.abs
    have hconst : Tendsto (fun _ : ℝ ↦ G * |x - y|) atTop (𝓝 (G * |x - y|)) :=
      tendsto_const_nhds
    have hev : ∀ᶠ R in atTop, |f R x - f R y| ≤ G * |x - y| :=
      Filter.Eventually.of_forall fun R ↦ hlip R x y
    have := le_of_tendsto_of_tendsto hbound hconst hev
    rw [Real.dist_eq, Real.dist_eq]
    exact this


end OTSelector
