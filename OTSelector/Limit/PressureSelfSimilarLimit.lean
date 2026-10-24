import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Self-similar pressure limits

A scale-indexed family `f R t` converges as `R → ∞` whenever it is uniformly
bounded, concave and Lipschitz in the tilt, and satisfies the self-similar
block comparison of the finite-volume pressure theorem: for every small
reserve fraction `ρ > 0`, with `lam = 1 - ρ`,

`limsup_R f R t ≤ lam^(1 - 2/q) liminf_L f L (t lam^(2/q)) + C ρ^s + |t| G ρ`.

The proof is the paper's argument.  The extra terms are sent to zero with `ρ`;
the tilt `t lam^(2/q)` tends to `t`, and the common Lipschitz bound identifies
the two liminf values.  This isolates the analytic limiting argument from the
stochastic matching comparison that must produce the displayed inequality.
-/

open Filter Set Topology
open scoped Topology

namespace OTSelector

/-- If a scale-indexed pressure is uniformly bounded, concave and Lipschitz in
the tilt, and satisfies the self-similar block comparison, then it converges at
every tilt; the limit is concave and has the same Lipschitz constant. -/
theorem exists_tendsto_of_selfSimilar_block
    {f : ℝ → ℝ → ℝ} {q s G C : ℝ}
    (hq : 2 < q) (hs : s = 1 - 2 / q) (hs0 : 0 < s)
    (hG : 0 ≤ G) (hC : 0 ≤ C)
    (hbdd : ∀ t, ∃ B : ℝ, ∀ R : ℝ, 1 ≤ R → |f R t| ≤ B)
    (hconcave : ∀ R, ConcaveOn ℝ univ (f R))
    (hlip : ∀ R t u, |f R t - f R u| ≤ G * |t - u|)
    (hblock : ∀ t ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
      let lam : ℝ := 1 - ρ
      Filter.limsup (fun R ↦ f R t) atTop ≤
        lam ^ s * Filter.liminf (fun R ↦ f R (t * lam ^ (2 / q))) atTop +
          C * ρ ^ s + |t| * G * ρ) :
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
  -- The limit candidate.
  let p : ℝ → ℝ := fun t ↦ Filter.liminf (fun R ↦ f R t) atTop
  have hle : ∀ t, Filter.limsup (fun R ↦ f R t) atTop ≤ p t := by
    intro t
    -- For each reserve fraction the block comparison bounds `limsup` by
    -- `lam^s p t + o(1)`; then send `ρ` to zero.
    have hstep : ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
        Filter.limsup (fun R ↦ f R t) atTop ≤
          (1 - ρ) ^ s * p t +
            ((1 - ρ) ^ s * (G * |t| * (1 - (1 - ρ) ^ (2 / q))) +
              C * ρ ^ s + |t| * G * ρ) := by
      intro ρ hρ hρ2
      let lam : ℝ := 1 - ρ
      have hlampos : 0 < lam := by dsimp only [lam]; linarith
      have hlamle : lam ≤ 1 := by dsimp only [lam]; linarith
      -- Lipschitz transfer between the two tilt liminf values.
      have hclose : p (t * lam ^ (2 / q)) ≤ p t + G * |t * lam ^ (2 / q) - t| := by
        have hpoint : ∀ R : ℝ,
            f R (t * lam ^ (2 / q)) ≤ f R t + G * |t * lam ^ (2 / q) - t| := by
          intro R
          have h := (abs_le.mp (hlip R (t * lam ^ (2 / q)) t)).2
          linarith
        have hcobdd_shift : atTop.IsCoboundedUnder (· ≥ ·)
            (fun R ↦ f R t + G * |t * lam ^ (2 / q) - t|) := by
          obtain ⟨B, hB⟩ := hbdd t
          refine ⟨B + G * |t * lam ^ (2 / q) - t|, fun a ha ↦ ?_⟩
          have hupper : ∀ᶠ R in atTop,
              f R t + G * |t * lam ^ (2 / q) - t| ≤
                B + G * |t * lam ^ (2 / q) - t| := by
            filter_upwards [eventually_atTop.2 ⟨1, fun R hR ↦
              (abs_le.mp (hB R hR)).2⟩] with R hR
            linarith [mul_nonneg hG (abs_nonneg (t * lam ^ (2 / q) - t))]
          have hlower : ∀ᶠ R in atTop,
              a ≤ f R t + G * |t * lam ^ (2 / q) - t| :=
            Filter.mem_map.mp ha
          obtain ⟨R, h1, h2⟩ := (hupper.and hlower).exists
          exact le_trans h2 h1
        have hmono : Filter.liminf (fun R ↦ f R (t * lam ^ (2 / q))) atTop ≤
            Filter.liminf (fun R ↦ f R t + G * |t * lam ^ (2 / q) - t|) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hpoint)
            (hbdd_ge _) hcobdd_shift
        rwa [liminf_add_const (F := atTop) (f := fun R ↦ f R t)
          (c := G * |t * lam ^ (2 / q) - t|) (hcobdd_ge t) (hbdd_ge t)] at hmono
      have hdist : |t * lam ^ (2 / q) - t| = |t| * (1 - lam ^ (2 / q)) := by
        have h2q : 0 ≤ 2 / q := by positivity
        have hpow_le : lam ^ (2 / q) ≤ 1 := Real.rpow_le_one hlampos.le hlamle h2q
        rw [show t * lam ^ (2 / q) - t = t * (lam ^ (2 / q) - 1) by ring]
        rw [abs_mul, abs_of_nonpos (by linarith : lam ^ (2 / q) - 1 ≤ 0)]
        ring
      have hfirst : Filter.limsup (fun R ↦ f R t) atTop ≤
          lam ^ s * p (t * lam ^ (2 / q)) + C * ρ ^ s + |t| * G * ρ := by
        simpa only [lam] using hblock t ρ hρ hρ2
      have hsecond : lam ^ s * p (t * lam ^ (2 / q)) ≤
          lam ^ s * (p t + G * |t| * (1 - lam ^ (2 / q))) := by
        have hlams : 0 ≤ lam ^ s := Real.rpow_nonneg hlampos.le _
        rw [hdist] at hclose
        have := mul_le_mul_of_nonneg_left hclose hlams
        simpa only [mul_assoc] using this
      calc
        Filter.limsup (fun R ↦ f R t) atTop ≤
            lam ^ s * p (t * lam ^ (2 / q)) + C * ρ ^ s + |t| * G * ρ := hfirst
        _ ≤ lam ^ s * (p t + G * |t| * (1 - lam ^ (2 / q))) +
              C * ρ ^ s + |t| * G * ρ := by linarith
        _ = lam ^ s * p t +
              (lam ^ s * (G * |t| * (1 - lam ^ (2 / q))) + C * ρ ^ s + |t| * G * ρ) := by
          ring
    -- Send the reserve fraction to zero.
    apply le_of_forall_pos_le_add
    intro ε hε
    have hlim : Tendsto (fun ρ : ℝ ↦ (1 - ρ) ^ s * p t +
        ((1 - ρ) ^ s * (G * |t| * (1 - (1 - ρ) ^ (2 / q))) +
          C * ρ ^ s + |t| * G * ρ)) (𝓝[>] (0 : ℝ)) (𝓝 (p t)) := by
      have hρbase : Tendsto (fun ρ : ℝ ↦ ρ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      have hbase : Tendsto (fun ρ : ℝ ↦ 1 - ρ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        simpa using (tendsto_const_nhds.sub hρbase :
          Tendsto (fun ρ : ℝ ↦ (1 : ℝ) - ρ) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 0)))
      have hpow : Tendsto (fun ρ : ℝ ↦ (1 - ρ) ^ s) (𝓝[>] (0 : ℝ)) (𝓝 (1 ^ s)) :=
        (Real.continuousAt_rpow_const (1 : ℝ) s (Or.inl one_ne_zero)).tendsto.comp hbase
      have hpow2 : Tendsto (fun ρ : ℝ ↦ (1 - ρ) ^ (2 / q)) (𝓝[>] (0 : ℝ))
          (𝓝 (1 ^ (2 / q))) :=
        (Real.continuousAt_rpow_const (1 : ℝ) (2 / q) (Or.inl one_ne_zero)).tendsto.comp hbase
      have hρs : Tendsto (fun ρ : ℝ ↦ ρ ^ s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hneg : Tendsto (fun ρ : ℝ ↦ ρ ^ (-s)) (𝓝[>] (0 : ℝ)) atTop :=
          tendsto_rpow_neg_nhdsGT_zero (by linarith)
        have hinv : Tendsto (fun ρ : ℝ ↦ (ρ ^ (-s))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
          hneg.inv_tendsto_atTop
        refine hinv.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ρ hρ
        rw [Real.rpow_neg hρ.le, inv_inv]
      have h1 : Tendsto (fun ρ : ℝ ↦ (1 - ρ) ^ s * p t) (𝓝[>] (0 : ℝ)) (𝓝 (1 ^ s * p t)) :=
        hpow.mul tendsto_const_nhds
      have h2 : Tendsto (fun ρ : ℝ ↦ (1 - ρ) ^ s * (G * |t| * (1 - (1 - ρ) ^ (2 / q))))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 ^ s * (G * |t| * (1 - 1 ^ (2 / q))))) :=
        hpow.mul ((tendsto_const_nhds.sub hpow2).const_mul (G * |t|))
      have h3 : Tendsto (fun ρ : ℝ ↦ C * ρ ^ s) (𝓝[>] (0 : ℝ)) (𝓝 (C * 0)) :=
        hρs.const_mul C
      have h4 : Tendsto (fun ρ : ℝ ↦ |t| * G * ρ) (𝓝[>] (0 : ℝ)) (𝓝 (|t| * G * 0)) :=
        hρbase.const_mul (|t| * G)
      have hsum := h1.add (h2.add (h3.add h4))
      simpa only [Real.one_rpow, sub_self, mul_zero, add_zero, mul_one, one_mul, add_assoc] using hsum
    have hsmall : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ), σ < 1 / 2 := by
      have h0 : ∀ᶠ σ : ℝ in 𝓝 (0 : ℝ), σ < 1 / 2 :=
        Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      exact h0.filter_mono nhdsWithin_le_nhds
    have hposmem : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ), 0 < σ := self_mem_nhdsWithin
    have hgood : ∀ᶠ σ : ℝ in 𝓝[>] (0 : ℝ),
        ((1 - σ) ^ s * p t +
          ((1 - σ) ^ s * (G * |t| * (1 - (1 - σ) ^ (2 / q))) +
            C * σ ^ s + |t| * G * σ)) < p t + ε ∧ 0 < σ ∧ σ < 1 / 2 :=
      (hlim.eventually (Iio_mem_nhds (by linarith : p t < p t + ε))).and
        (hposmem.and hsmall)
    obtain ⟨σ, hσlt, hσpos, hσsmall⟩ := hgood.exists
    exact (hstep σ hσpos hσsmall).trans (le_of_lt hσlt)
  -- Liminf is always at most limsup; the block comparison gives the reverse.
  have hlim_eq : ∀ t, Filter.liminf (fun R ↦ f R t) atTop =
      Filter.limsup (fun R ↦ f R t) atTop := by
    intro t
    exact le_antisymm (Filter.liminf_le_limsup (hbdd_le t) (hbdd_ge t)) (hle t)
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
