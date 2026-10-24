import OTSelector.Analysis.Calculus.Whitney.Lusin
import OTSelector.MeasureTheory.LusinCompactCore
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformAmbientSecondJet.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformAmbientSecondJet`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual first and second jets exist almost everywhere, with the given compact continuity and local regularity hypotheses.

Objects: Large compact sets carrying uniform ambient first-order and scalar second-order remainder radii.

Proof detail: Make closed error-radius predicates measurable, apply Lusin and compact selection, and derive uniform Taylor estimates; the Lipschitz derivative variant first uses Rademacher.

Sources: Hassler Whitney, Section 2, Theorem 1 and proof, pp. 144–147, especially uniform first-order compatibility (2.8) (https://msp.org/pjm/1951/1-1/pjm-v1-n1-p15-s.pdf#page=3); D. H. Fremlin, Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416 (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110); D. H. Fremlin, Section 262P, p. 17 (measurability of derivative); Theorem 262Q, pp. 18–20 (Rademacher) (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=17); Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html).
Relation: Derived quantitative Lusin/jet selection, not a claim that a measurable field is globally a Hessian.
-/

/-!
# Uniform ambient second jets on large compact cores

The original C1,1 extension retains its actual Hessian on a compact set of
arbitrarily large original mass. Lusin uniformizes derivative radii for every
ambient displacement; a segment estimate gives the scalar second remainder.
-/

open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem isClosed_uniform_ambient_first_order_set
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E → V} {D : E → E →L[ℝ] V} {H : Set E} (hH : IsClosed H)
    (hf : ContinuousOn f H) (hD : ContinuousOn D H) (η δ : ℝ) :
    IsClosed (H ∩ {x | ∀ y : E, dist y x < δ →
      ‖f y - f x - D x (y - x)‖ ≤ η * ‖y - x‖}) := by
  apply hH.inter_preimage_val_iff.mp
  have hf' : Continuous (fun x : H ↦ f x) := continuousOn_iff_continuous_domRestrict.mp hf
  have hD' : Continuous (fun x : H ↦ D x) := continuousOn_iff_continuous_domRestrict.mp hD
  change IsClosed {x : H | ∀ y : E, dist y x < δ →
    ‖f y - f x - D x (y - x)‖ ≤ η * ‖y - x‖}
  have hi : IsClosed (⋂ y : E, {x : H | dist (y : E) x < δ →
      ‖f y - f x - D x (y - x)‖ ≤ η * ‖(y : E) - x‖}) := by
    apply isClosed_iInter
    intro y
    have hleft : IsClosed {x : H | δ ≤ dist (y : E) x} :=
      isClosed_le continuous_const (continuous_const.dist continuous_subtype_val)
    have hright : IsClosed {x : H |
        ‖f y - f x - D x (y - x)‖ ≤ η * ‖(y : E) - x‖} :=
      isClosed_le ((continuous_const.sub hf').sub
        (hD'.clm_apply (continuous_const.sub continuous_subtype_val))).norm
        (continuous_const.mul (continuous_const.sub continuous_subtype_val).norm)
    convert hleft.union hright using 1
    ext x
    simp only [mem_union, mem_ofPred_eq, not_lt, imp_iff_not_or]
  convert hi using 1
  ext x
  simp only [mem_ofPred_eq, mem_iInter]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A uniform ambient first-derivative remainder controls the scalar quadratic
remainder along the original straight segment, without symmetry of the bilinear map. -/
private theorem uniform_scalar_second_remainder_of_fderiv_bound
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {x : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ} {η r : ℝ} (hη : 0 ≤ η) (_hr : 0 < r)
    (hfirst : ∀ k : E, ‖k‖ < r →
      ‖fderiv ℝ G (x + k) - fderiv ℝ G x - B k‖ ≤ η * ‖k‖)
    {h : E} (hh : ‖h‖ < r) :
    ‖G (x + h) - G x - fderiv ℝ G x h - (1 / 2 : ℝ) * B h h‖ ≤
      η * ‖h‖ ^ 2 := by
  let γ : ℝ → E := fun s ↦ x + s • h
  have hγ (s : ℝ) : HasDerivAt γ h s := by
    simpa only [γ, Pi.add_apply, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const h)
  let R : ℝ → ℝ := fun s ↦
    G (γ s) - G x - s * fderiv ℝ G x h - (1 / 2 : ℝ) * s ^ 2 * B h h
  let R' : ℝ → ℝ := fun s ↦
    fderiv ℝ G (γ s) h - fderiv ℝ G x h - s * B h h
  have hR (s : ℝ) : HasDerivAt R (R' s) s := by
    have h₀ : HasDerivAt (fun t ↦ G (γ t)) (fderiv ℝ G (γ s) h) s :=
      (hG.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hγ s)
    have hd := (((h₀.sub_const (G x)).sub
      ((hasDerivAt_id s).mul_const (fderiv ℝ G x h))).sub
      ((((hasDerivAt_id s).pow 2).const_mul (1 / 2 : ℝ)).mul_const (B h h)))
    convert hd using 1 <;> try dsimp only [R, R']
    all_goals first | rfl | (simp only [id_eq]; ring)
  have hbound (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) : ‖R' s‖ ≤ η * ‖h‖ ^ 2 := by
    have hnorm : ‖s • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2.le
    have heq : R' s = (fderiv ℝ G (x + s • h) - fderiv ℝ G x - B (s • h)) h := by
      simp only [R', γ, sub_apply, map_smul,
        smul_apply, smul_eq_mul]
    rw [heq]
    calc
      ‖(fderiv ℝ G (x + s • h) - fderiv ℝ G x - B (s • h)) h‖ ≤
          ‖fderiv ℝ G (x + s • h) - fderiv ℝ G x - B (s • h)‖ * ‖h‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (η * ‖s • h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (hfirst _ (hnorm.trans_lt hh)) (norm_nonneg _)
      _ ≤ (η * ‖h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hη) (norm_nonneg _)
      _ = η * ‖h‖ ^ 2 := by ring
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s _ ↦ (hR s).hasDerivWithinAt) hbound
  simpa only [R, γ, one_smul, zero_smul, add_zero, one_mul, one_pow, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, zero_mul,
    sub_self, sub_zero, mul_one] using hMVT


/-- A compact set with continuous actual second jets admits a large compact
subcore with first- and second-order remainders uniform in all ambient increments. -/
theorem exists_compact_uniform_ambient_secondJet
    {ν : Measure E} {H : Set E} (hH : IsCompact H) (hνH : ν H ≠ ⊤)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hsecond : ∀ x ∈ H, DifferentiableAt ℝ (fderiv ℝ G) x)
    (hHess : ContinuousOn (fderiv ℝ (fderiv ℝ G)) H)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ ν (H \ K) < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
          ‖fderiv ℝ G (x + h) - fderiv ℝ G x -
            fderiv ℝ (fderiv ℝ G) x h‖ ≤ η * ‖h‖ ∧
          ‖G (x + h) - G x - fderiv ℝ G x h -
            (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ G) x h h‖ ≤ η * ‖h‖ ^ 2 := by
  classical
  let f := fderiv ℝ G
  let a : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let R : ℕ → ℕ → Set E := fun n m ↦ H ∩ {x | ∀ y : E, dist y x < a m →
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ a n * ‖y - x‖}
  have hf : Continuous f := hG.continuous_fderiv one_ne_zero
  have hR (n m : ℕ) : IsClosed (R n m) :=
    isClosed_uniform_ambient_first_order_set hH.isClosed hf.continuousOn hHess _ _
  have hex (n : ℕ) (x : E) : ∃ m, x ∉ H ∨ x ∈ R n m := by
    by_cases hx : x ∈ H
    · obtain ⟨r, hr, hbound⟩ := Metric.mem_nhds_iff.mp
        ((hsecond x hx).hasFDerivAt.isLittleO.def (ha n))
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
      refine ⟨m, Or.inr ⟨hx, ?_⟩⟩
      intro y hdist
      exact hbound (lt_trans hdist hm)
    · exact ⟨0, Or.inl hx⟩
  let index : E → ℕ → ℕ := fun x n ↦ Nat.find (hex n x)
  have hindex : Measurable index := by
    apply measurable_pi_lambda
    intro n
    exact measurable_find (hex n) (fun m ↦ hH.isClosed.measurableSet.compl.union
      (hR n m).measurableSet)
  obtain ⟨K, hKH, hK, hsmall, hcont⟩ := exists_lusin_compact_core hH.measurableSet
    hνH hindex hε
  refine ⟨K, hKH, hK, hsmall, hHess.mono hKH, ?_⟩
  intro η hη
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  have hc : ContinuousOn (fun x ↦ index x n) K :=
    (continuous_apply n).comp_continuousOn hcont
  obtain ⟨N, hN⟩ := hK.bddAbove_image hc
  refine ⟨a N, ha N, ?_⟩
  intro x hx h hh
  have hxR : x ∈ R n (index x n) :=
    (Nat.find_spec (hex n x)).resolve_left (not_not.mpr (hKH hx))
  have hNx : index x n ≤ N := hN (mem_image_of_mem _ hx)
  have hrad : a N ≤ a (index x n) := by
    dsimp [a]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hNx 1
  have hfirst (k : E) (hk : ‖k‖ < a N) :
      ‖fderiv ℝ G (x + k) - fderiv ℝ G x -
        fderiv ℝ (fderiv ℝ G) x k‖ ≤ η * ‖k‖ := by
    have hdist : dist (x + k) x < a (index x n) := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hk.trans_le hrad
    have hrem : ‖f (x + k) - f x - fderiv ℝ f x k‖ ≤ a n * ‖k‖ := by
      simpa only [add_sub_cancel_left] using hxR.2 (x + k) hdist
    exact hrem.trans (mul_le_mul_of_nonneg_right hn.le (norm_nonneg _))
  exact ⟨hfirst h hh,
    uniform_scalar_second_remainder_of_fderiv_bound hG hη.le (ha N) hfirst hh⟩

/-- The same original C1,1 function has large compact cores with continuous actual
Hessian and uniform ambient remainders for any original law absolutely continuous
with respect to Haar measure. Neither a Hessian nor its modulus is supplied. -/
theorem exists_compact_uniform_ambient_secondJet_of_lipschitz_fderiv
    {m ν : Measure E} [m.IsAddHaarMeasure] (hν : ν ≪ m)
    {s : Set E} (hs : MeasurableSet s) (hνs : ν s ≠ ⊤)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ s, IsCompact K ∧ ν (s \ K) < ε ∧
      (∀ x ∈ K, HasFDerivAt (fderiv ℝ G)
        (fderiv ℝ (fderiv ℝ G) x) x) ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K ∧
      ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
          ‖fderiv ℝ G (x + h) - fderiv ℝ G x -
            fderiv ℝ (fderiv ℝ G) x h‖ ≤ η * ‖h‖ ∧
          ‖G (x + h) - G x - fderiv ℝ G x h -
            (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ G) x h h‖ ≤ η * ‖h‖ ^ 2 := by
  obtain ⟨H, hHs, hH, hsmallH, hdiffH, _hfH, hDH⟩ :=
    exists_differential_lusin_compact_core_of_lipschitz_absolutelyContinuous
      hν hs hνs hLip (ENNReal.half_pos hε).ne'
  obtain ⟨K, hKH, hK, hsmallK, hDK, hrem⟩ :=
    exists_compact_uniform_ambient_secondJet hH
      (ne_top_of_le_ne_top hνs (measure_mono hHs)) hG hdiffH hDH
      (ENNReal.half_pos hε).ne'
  refine ⟨K, hKH.trans hHs, hK, ?_,
    fun x hx ↦ (hdiffH x (hKH hx)).hasFDerivAt, hDK, hrem⟩
  calc
    ν (s \ K) ≤ ν (s \ H ∪ (H \ K)) := measure_mono (by
      intro x hx
      by_cases hxH : x ∈ H
      · exact Or.inr ⟨hxH, hx.2⟩
      · exact Or.inl ⟨hx.1, hxH⟩)
    _ ≤ ν (s \ H) + ν (H \ K) := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hsmallH hsmallK
    _ = ε := ENNReal.add_halves ε

end OTSelector.Geometry

end
