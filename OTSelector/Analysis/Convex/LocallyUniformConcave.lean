import OTSelector.Analysis.Convex.ConcaveDifferentiability
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Limit.LocallyUniformConcave.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Limit.LocallyUniformConcave`; the selected original proof blocks follow. -/
section

/-!
# Limit.LocallyUniformConcave

**Conditions:** A sequence of real concave functions converges pointwise on an open interval; the target compact subinterval lies strictly inside it.

**Objects:** Uniform compact-subinterval convergence and a nonnegative vanishing supremum-error sequence.

**Proof detail:** Three fixed evaluations bound each concave function on a larger interval, which gives a common interior Lipschitz bound; a finite net transfers pointwise convergence to the supremum norm.

**Sources:** [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83), Sections 3.1.3–3.1.4, pp. 69–71, first-order support inequality (3.2) and positive-semidefinite Hessian criterion; [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110), Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products); [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=235), Section 6.2.1, Theorem 6.2.2, p. 235.

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Local uniform convergence of concave functions

A pointwise convergent sequence of concave functions on an open interval converges
uniformly on compact subintervals.  The paper's differentiability argument needs
this quantitatively: the finite-level pressures `pₙ` converge to the limiting
pressure `p`, and the error `sup |pₙ - p|` must vanish faster than the chosen tilt.

The proof here follows the classical route.

* Concavity gives a *two-sided affine bound* for a concave `f` on `[a, b]` in terms
  of three evaluations: an upper bound by extrapolating from a point `u < a`, and a
  lower bound by interpolating between `a` and `b`.
* Consequently `sup |pₙ|` on a closed subinterval is bounded by a fixed linear
  combination of three convergent values, so the `pₙ` are eventually uniformly
  bounded there.
* Uniform boundedness on a slightly larger interval gives a common Lipschitz
  constant on the target interval (`ConcaveOn.lipschitzOnWith_of_abs_le`).
* A uniformly Lipschitz pointwise-convergent sequence converges uniformly on a
  compact interval (finite `η`-net argument, `tendsto_sSup_abs_sub_of_lipschitz`).

The final statement `tendsto_sSup_abs_sub_of_pointwise_tendsto_concave` is the
`δₙ → 0` producer consumed by `hasDerivAt_of_concave_supergradient_sequence`.
-/

open Filter Set Topology
open scoped Topology

noncomputable section
namespace OTSelector

/-- **Upper affine bound for a concave function.**  If `f` is concave on `s` and
`u < a ≤ x`, then `f x` is at most the affine extrapolation of the chord through
`(u, f u)` and `(a, f a)` evaluated at `x`. -/
theorem concave_le_extrapolation {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {u a x : ℝ} (hu : u ∈ s) (ha : a ∈ s) (hx : x ∈ s) (hua : u < a) (hax : a ≤ x) :
    f x ≤ ((x - u) * f a - (x - a) * f u) / (a - u) := by
  have hux : u < x := lt_of_lt_of_le hua hax
  have hxu : 0 < x - u := sub_pos.mpr hux
  have hden : 0 < a - u := sub_pos.mpr hua
  have hlam0 : 0 ≤ (x - a) / (x - u) := div_nonneg (by linarith) hxu.le
  have hmu0 : 0 ≤ (a - u) / (x - u) := div_nonneg (by linarith) hxu.le
  have hsum : (x - a) / (x - u) + (a - u) / (x - u) = 1 := by
    field_simp
    ring
  have key := hf.2 hu hx hlam0 hmu0 hsum
  have harg : (x - a) / (x - u) * u + (a - u) / (x - u) * x = a := by
    field_simp
    ring
  simp only [smul_eq_mul] at key
  rw [harg] at key
  rw [le_div_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_right key hxu.le
  field_simp at hmul
  nlinarith

/-- **Lower affine bound for a concave function.**  If `f` is concave on `s` and
`a ≤ x ≤ b`, then `f x` is at least the chord through `(a, f a)` and `(b, f b)`
evaluated at `x`. -/
theorem concave_ge_interpolation {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {a b x : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hx : x ∈ s)
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    ((b - x) * f a + (x - a) * f b) / (b - a) ≤ f x := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hlam0 : 0 ≤ (b - x) / (b - a) := div_nonneg (by linarith) hden.le
  have hmu0 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith) hden.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp
    ring
  have key := hf.2 ha hb hlam0 hmu0 hsum
  have harg : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp
    ring
  simp only [smul_eq_mul] at key
  rw [harg] at key
  rw [div_le_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_right key hden.le
  field_simp at hmul
  nlinarith

/-- **Three-point bound for a concave function.**  On `[a, b]`, a concave `f` is
bounded by a constant (depending only on the positions) times the sum of `|f|` at
`u`, `a`, `b`, where `u < a`. -/
theorem abs_le_of_concaveOn_three_points {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f)
    {u a b x : ℝ} (hu : u ∈ s) (ha : a ∈ s) (hb : b ∈ s) (hx : x ∈ s)
    (hua : u < a) (hab : a < b) (hb0 : 0 ≤ b) (hax : a ≤ x) (hxb : x ≤ b) :
    |f x| ≤ (((b + |u|) + (b + |a|)) / (a - u) + 1) * (|f u| + |f a| + |f b|) := by
  have hden : 0 < a - u := sub_pos.mpr hua
  have hxub : x - u ≤ b + |u| := by
    have := neg_le_abs u
    linarith
  have hxab : x - a ≤ b + |a| := by
    have := neg_le_abs a
    linarith
  have hxu0 : 0 ≤ x - u := by linarith
  have hxa0 : 0 ≤ x - a := by linarith
  have hupp := concave_le_extrapolation hf hu ha hx hua hax
  have hlow := concave_ge_interpolation hf ha hb hx hab hax hxb
  -- Upper bound by the extrapolated affine function.
  have hnum : (x - u) * f a - (x - a) * f u ≤
      (b + |u|) * |f a| + (b + |a|) * |f u| := by
    have e1 : (x - u) * f a ≤ (b + |u|) * |f a| := by
      calc (x - u) * f a ≤ |(x - u) * f a| := le_abs_self _
        _ = (x - u) * |f a| := by rw [abs_mul, abs_of_nonneg hxu0]
        _ ≤ (b + |u|) * |f a| := by gcongr
    have e2 : -((x - a) * f u) ≤ (b + |a|) * |f u| := by
      calc -((x - a) * f u) ≤ |(x - a) * f u| := neg_le_abs _
        _ = (x - a) * |f u| := by rw [abs_mul, abs_of_nonneg hxa0]
        _ ≤ (b + |a|) * |f u| := by gcongr
    linarith
  have hupper : f x ≤
      ((b + |u|) * |f a| + (b + |a|) * |f u|) / (a - u) := by
    refine hupp.trans ?_
    gcongr
  -- The constant is at least one, and the sum dominates the two upper terms.
  have hS0 : 0 ≤ |f u| + |f a| + |f b| := by positivity
  have hC1 : (1 : ℝ) ≤ ((b + |u|) + (b + |a|)) / (a - u) + 1 := by
    have hnonneg : 0 ≤ ((b + |u|) + (b + |a|)) / (a - u) :=
      div_nonneg (by linarith [abs_nonneg u, abs_nonneg a]) hden.le
    linarith
  have hupperC : f x ≤
      (((b + |u|) + (b + |a|)) / (a - u) + 1) * (|f u| + |f a| + |f b|) := by
    refine hupper.trans ?_
    have hfac : ((b + |u|) * |f a| + (b + |a|) * |f u|) / (a - u) ≤
        ((b + |u|) + (b + |a|)) / (a - u) * (|f u| + |f a| + |f b|) := by
      have h1 : 0 ≤ b + |u| := by linarith [abs_nonneg u]
      have h2 : 0 ≤ b + |a| := by linarith [abs_nonneg a]
      have hS : 0 ≤ |f u| + |f a| + |f b| := by positivity
      have hfa : |f a| ≤ |f u| + |f a| + |f b| := by linarith [abs_nonneg (f u), abs_nonneg (f b)]
      have hfu : |f u| ≤ |f u| + |f a| + |f b| := by linarith [abs_nonneg (f a), abs_nonneg (f b)]
      have hnumineq : (b + |u|) * |f a| + (b + |a|) * |f u| ≤
          ((b + |u|) + (b + |a|)) * (|f u| + |f a| + |f b|) := by
        have h1' := mul_le_mul_of_nonneg_left hfa h1
        have h2' := mul_le_mul_of_nonneg_left hfu h2
        have hprod1 : 0 ≤ (b + |u|) * |f a| := mul_nonneg h1 (abs_nonneg (f a))
        have hprod2 : 0 ≤ (b + |a|) * |f u| := mul_nonneg h2 (abs_nonneg (f u))
        nlinarith [h1', h2', hprod1, hprod2]
      calc ((b + |u|) * |f a| + (b + |a|) * |f u|) / (a - u)
          ≤ (((b + |u|) + (b + |a|)) * (|f u| + |f a| + |f b|)) / (a - u) := by
            gcongr
        _ = ((b + |u|) + (b + |a|)) / (a - u) * (|f u| + |f a| + |f b|) := by
            field_simp
    calc ((b + |u|) * |f a| + (b + |a|) * |f u|) / (a - u)
        ≤ ((b + |u|) + (b + |a|)) / (a - u) * (|f u| + |f a| + |f b|) := hfac
      _ = (((b + |u|) + (b + |a|)) / (a - u) + 1) * (|f u| + |f a| + |f b|)
          - (|f u| + |f a| + |f b|) := by ring
      _ ≤ (((b + |u|) + (b + |a|)) / (a - u) + 1) * (|f u| + |f a| + |f b|) := by
          linarith
  -- Lower bound by the interpolated affine function.
  have hlowAbs : -(|f a| + |f b|) ≤ ((b - x) * f a + (x - a) * f b) / (b - a) := by
    have hbxa : 0 ≤ b - x := by linarith
    have hbxa' : b - x ≤ b - a := by linarith
    have hxab' : x - a ≤ b - a := by linarith
    have hfrac : ((b - x) * f a + (x - a) * f b) / (b - a) ≥
        -(((b - x) * |f a| + (x - a) * |f b|) / (b - a)) := by
      have h1 : -((b - x) * f a) ≤ (b - x) * |f a| := by
        calc -((b - x) * f a) ≤ |(b - x) * f a| := neg_le_abs _
          _ = (b - x) * |f a| := by rw [abs_mul, abs_of_nonneg hbxa]
      have h2 : -((x - a) * f b) ≤ (x - a) * |f b| := by
        calc -((x - a) * f b) ≤ |(x - a) * f b| := neg_le_abs _
          _ = (x - a) * |f b| := by rw [abs_mul, abs_of_nonneg hxa0]
      have hsum' : -(((b - x) * f a + (x - a) * f b)) ≤
          (b - x) * |f a| + (x - a) * |f b| := by linarith
      rw [neg_div']
      gcongr
      linarith
    have hbd : ((b - x) * |f a| + (x - a) * |f b|) / (b - a) ≤ |f a| + |f b| := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < b - a)]
      nlinarith [abs_nonneg (f a), abs_nonneg (f b), hbxa, hbxa', hxab']
    linarith
  have hlowerC : -((((b + |u|) + (b + |a|)) / (a - u) + 1) * (|f u| + |f a| + |f b|)) ≤ f x := by
    have hsumle : |f a| + |f b| ≤ |f u| + |f a| + |f b| := by linarith [abs_nonneg (f u)]
    have hSle : |f a| + |f b| ≤
        (((b + |u|) + (b + |a|)) / (a - u) + 1) * (|f u| + |f a| + |f b|) := by
      calc |f a| + |f b| ≤ 1 * (|f u| + |f a| + |f b|) := by linarith
        _ ≤ _ := by gcongr
    linarith [hlowAbs, hlow]
  rw [abs_le]
  exact ⟨hlowerC, hupperC⟩

/-- **Uniform convergence from pointwise convergence and a common Lipschitz bound.**
On a compact interval, a pointwise convergent sequence of uniformly Lipschitz
functions converges uniformly, and the supremum of the pointwise errors tends to
zero. -/
theorem tendsto_sSup_abs_sub_of_lipschitz {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K)
    {f : ℝ → ℝ} {fn : ℕ → ℝ → ℝ}
    (hlipn : ∀ᶠ n in atTop, ∀ x ∈ Icc (-ρ) ρ, ∀ y ∈ Icc (-ρ) ρ,
      |fn n x - fn n y| ≤ K * |x - y|)
    (hlip : ∀ x ∈ Icc (-ρ) ρ, ∀ y ∈ Icc (-ρ) ρ, |f x - f y| ≤ K * |x - y|)
    (hpt : ∀ x ∈ Icc (-ρ) ρ, Tendsto (fun n => fn n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => sSup ((fun x => |fn n x - f x|) '' Icc (-ρ) ρ)) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  set step : ℝ := η / (8 * (K + 1)) with hstep
  have hsteppos : 0 < step := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * ρ) / step)
  have hNpos : 0 < N := by
    have h : 0 < (N : ℝ) := lt_trans (div_pos (by linarith) hsteppos) hN
    exact_mod_cast h
  set g : ℕ → ℝ := fun k => -ρ + (k : ℝ) * (2 * ρ / N) with hg
  have hg0 : g 0 = -ρ := by simp [g]
  have hgN : g N = ρ := by
    simp only [g]
    have hNne : (N : ℝ) ≠ 0 := by positivity
    field_simp [hNne]
    norm_num
  have hrat : 2 * ρ / (N : ℝ) ≤ step := by
    rw [div_le_iff₀ (by exact_mod_cast hNpos)]
    rw [div_lt_iff₀ hsteppos] at hN
    nlinarith
  have hgmem : ∀ k ≤ N, g k ∈ Icc (-ρ) ρ := by
    intro k hk
    have hstepnonneg : 0 ≤ 2 * ρ / (N : ℝ) := by positivity
    have hkcast : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    constructor
    · simp only [g]
      have : 0 ≤ (k : ℝ) * (2 * ρ / (N : ℝ)) := mul_nonneg (by positivity) hstepnonneg
      linarith
    · have hmul : (k : ℝ) * (2 * ρ / (N : ℝ)) ≤ (N : ℝ) * (2 * ρ / (N : ℝ)) := by
        gcongr
      have hNmul : (N : ℝ) * (2 * ρ / (N : ℝ)) = 2 * ρ := by
        have hNne : (N : ℝ) ≠ 0 := by positivity
        field_simp [hNne]
      calc g k = -ρ + (k : ℝ) * (2 * ρ / (N : ℝ)) := rfl
        _ ≤ -ρ + (N : ℝ) * (2 * ρ / (N : ℝ)) := by linarith
        _ = ρ := by rw [hNmul]; ring
  -- Eventually the grid values are accurate.
  have hgrid : ∀ᶠ n in atTop, ∀ k ∈ Finset.range (N + 1),
      |fn n (g k) - f (g k)| ≤ η / 2 := by
    rw [Finset.eventually_all]
    intro k hk
    have hk_le : k ≤ N := by
      rw [Finset.mem_range] at hk
      omega
    obtain ⟨Nk, hNk⟩ := (Metric.tendsto_atTop.1 (hpt (g k) (hgmem k hk_le))) (η / 2) hη2
    exact eventually_atTop.2 ⟨Nk, fun n hn => by
      have := hNk n hn
      rw [Real.dist_eq] at this
      linarith⟩
  have hbound : ∀ᶠ n in atTop, ∀ x ∈ Icc (-ρ) ρ, |fn n x - f x| ≤ 3 * η / 4 := by
    filter_upwards [hgrid, hlipn] with n hgridn hlipnn
    intro x hx
    -- Choose the left grid point nearest to `x`.
    have hPne : ∃ k : ℕ, x ≤ g k := ⟨N, by rw [hgN]; exact hx.2⟩
    let k := Nat.find hPne
    have hk_le : k ≤ N := Nat.find_min' hPne (by rw [hgN]; exact hx.2)
    have hxk : x ≤ g k := Nat.find_spec hPne
    have hgk : g k ∈ Icc (-ρ) ρ := hgmem k hk_le
    have hkgrid : |fn n (g k) - f (g k)| ≤ η / 2 :=
      hgridn k (Finset.mem_range.2 (Nat.lt_succ_of_le hk_le))
    have hdist : |x - g k| ≤ step := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · have hx0 : x ≤ -ρ := by
          simpa only [hg0] using (show x ≤ g 0 from hk0 ▸ hxk)
        have hxeq : x = -ρ := le_antisymm hx0 hx.1
        rw [hxeq, hk0, hg0]
        simp
        linarith [hsteppos]
      · have hprev : ¬ x ≤ g (k - 1) := Nat.find_min hPne (Nat.sub_one_lt hkpos.ne')
        have hxprev : g (k - 1) < x := not_le.1 hprev
        have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_of_lt hkpos)]
          norm_num
        have hstepk : g k - g (k - 1) = 2 * ρ / (N : ℝ) := by
          simp only [g]
          rw [hkcast]
          ring
        have hnonneg : 0 ≤ g k - x := by linarith
        rw [abs_sub_comm, abs_of_nonneg hnonneg]
        linarith
    have h1 : |fn n x - fn n (g k)| ≤ K * |x - g k| := hlipnn x hx (g k) hgk
    have h3 : |f (g k) - f x| ≤ K * |(g k) - x| := hlip (g k) hgk x hx
    have htri : |fn n x - f x| ≤
        |fn n x - fn n (g k)| + |fn n (g k) - f (g k)| + |f (g k) - f x| := by
      have hsplit : fn n x - f x =
          (fn n x - fn n (g k)) + (fn n (g k) - f (g k)) + (f (g k) - f x) := by ring
      rw [hsplit]
      exact abs_add_three _ _ _
    have hKstep : K * |x - g k| + η / 2 + K * |(g k) - x| ≤ 3 * η / 4 := by
      have hsym : |(g k) - x| = |x - g k| := abs_sub_comm _ _
      rw [hsym]
      have hKδ : K * |x - g k| ≤ K * step := mul_le_mul_of_nonneg_left hdist hK
      have hstepval : 2 * K * step ≤ η / 4 := by
        have hKle : K ≤ K + 1 := by linarith
        have hstep' : step = η / (8 * (K + 1)) := hstep
        rw [hstep']
        have hden : 0 < 8 * (K + 1) := by positivity
        rw [mul_div_assoc', div_le_iff₀ hden]
        nlinarith [mul_le_mul_of_nonneg_left hKle (by linarith : (0:ℝ) ≤ 2 * K),
          mul_nonneg (by linarith : (0:ℝ) ≤ 2 * K) hη.le]
      nlinarith [hKδ]
    linarith [h1, h3, htri, hKstep]
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hbound
  refine ⟨N₀, fun n hn => ?_⟩
  have hn' := hN₀ n hn
  -- The supremum over the interval is at most `3η/4 < η`.
  set S : Set ℝ := (fun x => |fn n x - f x|) '' Icc (-ρ) ρ with hS
  have hne : S.Nonempty := ⟨_, ⟨-ρ, by simp [hρ.le], rfl⟩⟩
  have hbdd : BddAbove S := by
    refine ⟨3 * η / 4, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hn' y hy
  have hsup_le : sSup S ≤ 3 * η / 4 := csSup_le hne fun y hy => by
    obtain ⟨z, hz, rfl⟩ := hy
    exact hn' z hz
  have hsup_nonneg : 0 ≤ sSup S := by
    have hmem : |fn n (-ρ) - f (-ρ)| ∈ S := ⟨-ρ, by simp [hρ.le], rfl⟩
    exact (abs_nonneg _).trans (le_csSup hbdd hmem)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nonneg]
  linarith

/-- **Local uniform convergence of concave functions.**  A sequence of concave
functions on `Ioo (-ε) ε` that converges pointwise there converges uniformly on
every closed subinterval `Icc (-ρ) ρ`, and the supremum of the pointwise errors
tends to zero. -/
theorem tendsto_sSup_abs_sub_of_pointwise_tendsto_concave
    {ε : ℝ} (hε : 0 < ε) {p : ℝ → ℝ} {pn : ℕ → ℝ → ℝ}
    (hconc : ∀ n, ConcaveOn ℝ (Ioo (-ε) ε) (pn n))
    (hpt : ∀ x ∈ Ioo (-ε) ε, Tendsto (fun n => pn n x) atTop (𝓝 (p x)))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ < ε) :
    Tendsto (fun n => sSup ((fun x => |pn n x - p x|) '' Icc (-ρ) ρ)) atTop (𝓝 0) := by
  have hplim : ConcaveOn ℝ (Ioo (-ε) ε) p := concaveOn_of_pointwise_tendsto hpt hconc
  set r₁ : ℝ := (ρ + ε) / 2 with hr₁
  set r₂ : ℝ := (ρ + r₁) / 2 with hr₂
  have hr₁ε : r₁ < ε := by rw [hr₁]; linarith
  have hρr₁ : ρ < r₁ := by rw [hr₁]; linarith
  have hr₂r₁ : r₂ < r₁ := by rw [hr₂]; linarith
  have hρr₂ : ρ < r₂ := by rw [hr₂]; linarith
  have hr₁pos : 0 < r₁ := lt_trans hρ0 hρr₁
  have hr₂pos : 0 < r₂ := lt_trans hρ0 hρr₂
  set u : ℝ := -(ε + r₁) / 2 with hu_def
  have hu_mem : u ∈ Ioo (-ε) ε := by
    constructor
    · rw [hu_def]; linarith
    · rw [hu_def]; linarith
  have hu_lt : u < -r₁ := by rw [hu_def]; linarith
  set C : ℝ := ((r₁ + |u|) + (r₁ + |-r₁|)) / ((-r₁) - u) + 1 with hC
  have hCpos : 0 < C := by
    rw [hC]
    have hden : 0 < (-r₁) - u := by linarith
    have hnum : 0 ≤ (r₁ + |u|) + (r₁ + |-r₁|) := by positivity
    have hquot : 0 ≤ ((r₁ + |u|) + (r₁ + |-r₁|)) / ((-r₁) - u) :=
      div_nonneg hnum hden.le
    linarith
  have hvalue : ∀ (f : ℝ → ℝ), ConcaveOn ℝ (Ioo (-ε) ε) f →
      ∀ x ∈ Icc (-r₁) r₁, |f x| ≤ C * (|f u| + |f (-r₁)| + |f r₁|) := by
    intro f hf x hx
    have hxI : x ∈ Ioo (-ε) ε := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have ham : (-r₁ : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    have hbm : (r₁ : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    have hthree := abs_le_of_concaveOn_three_points hf hu_mem ham hbm hxI hu_lt
      (by linarith) hr₁pos.le (by linarith [hx.1]) (by linarith [hx.2])
    simpa [C] using hthree
  set M : ℝ := C * ((|p u| + 1) + (|p (-r₁)| + 1) + (|p r₁| + 1)) + 1 with hM
  have hMpos : 0 < M := by
    rw [hM]
    have : 0 ≤ C * ((|p u| + 1) + (|p (-r₁)| + 1) + (|p r₁| + 1)) := by positivity
    linarith
  have hev1 (x : ℝ) (hx : x ∈ Ioo (-ε) ε) :
      ∀ᶠ n in atTop, |pn n x - p x| < 1 := by
    obtain ⟨Nx, hNx⟩ := (Metric.tendsto_atTop.1 (hpt x hx)) 1 one_pos
    exact eventually_atTop.2 ⟨Nx, fun n hn => by
      have h := hNx n hn
      rwa [Real.dist_eq] at h
      ⟩
  have hu1 := hev1 u hu_mem
  have ha1 := hev1 (-r₁) ⟨by linarith, by linarith⟩
  have hb1 := hev1 r₁ ⟨by linarith, by linarith⟩
  have hMpn : ∀ᶠ n in atTop, ∀ x ∈ Icc (-r₁) r₁, |pn n x| ≤ M := by
    filter_upwards [hu1, ha1, hb1] with n hnu hna hnb
    intro x hx
    have hu_bound : |pn n u| ≤ |p u| + 1 := by
      have := abs_add_le (pn n u - p u) (p u)
      have hsub : pn n u - p u + p u = pn n u := by ring
      rw [hsub] at this
      linarith
    have ha_bound : |pn n (-r₁)| ≤ |p (-r₁)| + 1 := by
      have := abs_add_le (pn n (-r₁) - p (-r₁)) (p (-r₁))
      have hsub : pn n (-r₁) - p (-r₁) + p (-r₁) = pn n (-r₁) := by ring
      rw [hsub] at this
      linarith
    have hb_bound : |pn n r₁| ≤ |p r₁| + 1 := by
      have := abs_add_le (pn n r₁ - p r₁) (p r₁)
      have hsub : pn n r₁ - p r₁ + p r₁ = pn n r₁ := by ring
      rw [hsub] at this
      linarith
    have hv := hvalue (pn n) (hconc n) x hx
    have hSle : |pn n u| + |pn n (-r₁)| + |pn n r₁| ≤
        (|p u| + 1) + (|p (-r₁)| + 1) + (|p r₁| + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hSle hCpos.le
    rw [hM]
    linarith
  have hMp : ∀ x ∈ Icc (-r₁) r₁, |p x| ≤ M := by
    intro x hx
    have hv := hvalue p hplim x hx
    have hSle : |p u| + |p (-r₁)| + |p r₁| ≤
        (|p u| + 1) + (|p (-r₁)| + 1) + (|p r₁| + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hSle hCpos.le
    rw [hM]
    linarith
  set K : ℝ := 2 * M / (r₁ - r₂) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have hden : 0 < r₁ - r₂ := by linarith
    positivity
  have hLip_of : ∀ (f : ℝ → ℝ), ConcaveOn ℝ (Ioo (-ε) ε) f →
      (∀ x ∈ Icc (-r₁) r₁, |f x| ≤ M) →
      ∀ x ∈ Icc (-ρ) ρ, ∀ y ∈ Icc (-ρ) ρ, |f x - f y| ≤ K * |x - y| := by
    intro f hf hMf
    have hball_sub : Metric.ball (0 : ℝ) r₁ ⊆ Ioo (-ε) ε := by
      rw [Real.ball_eq_Ioo]
      intro z hz
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hfball : ConcaveOn ℝ (Metric.ball (0 : ℝ) r₁) f :=
      hf.subset hball_sub (convex_ball 0 r₁)
    have hM' : ∀ a : ℝ, dist a 0 < r₁ → |f a| ≤ M := by
      intro a ha
      rw [Real.dist_eq, sub_zero, abs_lt] at ha
      exact hMf a ⟨ha.1.le, ha.2.le⟩
    have hLip := hfball.lipschitzOnWith_of_abs_le (x₀ := (0 : ℝ)) (r := r₁)
      (ε := r₁ - r₂) (M := M) (by linarith) hM'
    have hrad : r₁ - (r₁ - r₂) = r₂ := by ring
    rw [hrad] at hLip
    have hsub : Icc (-ρ) ρ ⊆ Metric.ball (0 : ℝ) r₂ := by
      intro z hz
      rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hLip' := hLip.mono hsub
    have hco : ((2 * M / (r₁ - r₂)).toNNReal : ℝ) = 2 * M / (r₁ - r₂) :=
      Real.coe_toNNReal _ (by positivity)
    intro x hx y hy
    have hd := hLip'.dist_le_mul x hx y hy
    rw [Real.dist_eq, Real.dist_eq, hco] at hd
    rw [hK]
    exact hd
  have hlipn_ev : ∀ᶠ n in atTop, ∀ x ∈ Icc (-ρ) ρ, ∀ y ∈ Icc (-ρ) ρ,
      |pn n x - pn n y| ≤ K * |x - y| :=
    hMpn.mono fun n hn => hLip_of (pn n) (hconc n) hn
  have hlipP : ∀ x ∈ Icc (-ρ) ρ, ∀ y ∈ Icc (-ρ) ρ, |p x - p y| ≤ K * |x - y| :=
    hLip_of p hplim hMp
  have hptI : ∀ x ∈ Icc (-ρ) ρ, Tendsto (fun n => pn n x) atTop (𝓝 (p x)) := by
    intro x hx
    exact hpt x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact tendsto_sSup_abs_sub_of_lipschitz hρ0 hKpos.le hlipn_ev hlipP hptI

/-- **A usable uniform-error sequence.**  Under the hypotheses of
`tendsto_sSup_abs_sub_of_pointwise_tendsto_concave`, the suprema themselves form a
nonnegative sequence tending to zero that bounds the pointwise errors on the open
interval. -/
theorem exists_delta_of_pointwise_tendsto_concave
    {ε : ℝ} (hε : 0 < ε) {p : ℝ → ℝ} {pn : ℕ → ℝ → ℝ}
    (hconc : ∀ n, ConcaveOn ℝ (Ioo (-ε) ε) (pn n))
    (hpt : ∀ x ∈ Ioo (-ε) ε, Tendsto (fun n => pn n x) atTop (𝓝 (p x)))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n, ∀ s ∈ Ioo (-ρ) ρ, |pn n s - p s| ≤ δ n := by
  have hplim : ConcaveOn ℝ (Ioo (-ε) ε) p := concaveOn_of_pointwise_tendsto hpt hconc
  have hsub : Icc (-ρ) ρ ⊆ Ioo (-ε) ε := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcont : ∀ n, ContinuousOn (fun s => |pn n s - p s|) (Icc (-ρ) ρ) := by
    intro n
    have hpn : ContinuousOn (pn n) (Icc (-ρ) ρ) :=
      ((hconc n).continuousOn isOpen_Ioo).mono hsub
    have hp : ContinuousOn p (Icc (-ρ) ρ) :=
      (hplim.continuousOn isOpen_Ioo).mono hsub
    exact (hpn.sub hp).abs
  let δ : ℕ → ℝ := fun n => sSup ((fun x => |pn n x - p x|) '' Icc (-ρ) ρ)
  have hbdd : ∀ n, BddAbove ((fun x => |pn n x - p x|) '' Icc (-ρ) ρ) :=
    fun n => isCompact_Icc.bddAbove_image (hcont n)
  have hmem : ∀ n, (fun x => |pn n x - p x|) (-ρ) ∈
      ((fun x => |pn n x - p x|) '' Icc (-ρ) ρ) := fun n =>
    ⟨-ρ, ⟨le_rfl, by linarith [hρ0]⟩, rfl⟩
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro n
    exact (abs_nonneg _).trans (le_csSup (hbdd n) (hmem n))
  · exact tendsto_sSup_abs_sub_of_pointwise_tendsto_concave hε hconc hpt hρ0 hρε
  · intro n s hs
    exact le_csSup (hbdd n) ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩, rfl⟩

end OTSelector

end
end
