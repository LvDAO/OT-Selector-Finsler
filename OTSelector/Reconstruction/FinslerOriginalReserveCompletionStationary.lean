import OTSelector.Reconstruction.FinslerOriginalDegenerateScreeningApproximation

/-!
# Stationary reserve lifting and the normalized box limit

This module isolates the two remaining analytic links between the finite Poisson
reserve completion and the value identification I_w = I_2.

1. **The normalized box limit.**  The paper's finite-value comparison bounds the
   actual legal pressure limit p by c_rho * I(t c_rho) + v_rho with c_rho -> 1
   and v_rho -> 0 (c_rho = (1-rho)^{1-2/q}, v_rho = C rho^{1-2/q} + C|t|G rho).
   The abstract limit step is proved (le_of_tendsto_reserveNormalization): the
   comparison at every small rho forces p(t) <= I(t).  Combined with the legal
   pressure upper comparison this identifies the two stationary legal values
   (weightedInf_eq_secondMomentInf_of_finiteValueComparison).

2. **Vanishing reserve budgets are the stationary reserve lifting.**  The named
   input StationaryReserveLifting asks that every weighted stationary matching be
   replaceable, at every positive value budget, by a collar-supported weighted
   stationary matching with value larger by at most the budget.  If it holds for
   every budget, then the second-moment legal pressure is at most the weighted
   one (legalSecondMomentInf_le_legalWeightedInf_of_stationaryReserveLifting),
   and with the unconditional class order the two values coincide
   (legalWeightedInf_eq_legalSecondMomentInf_of_stationaryReserveLifting).  The
   collar coercivity converting collar support into a finite second moment is
   proved here (secondMomentSubclass_of_collar_general).

## Remaining gap

The two named inputs are exactly the measurable stationary lifting of the finite
reserve completion (Palm of the pushed law: probability, original scalar
marginals, finite kinetic and probe integrals) and the finite-value comparison
with the explicit reserve cost C rho^{1-2/q} + o.  The finite scene-level
completion and its cost bound are in FinslerOriginalCollarValueDensity; the
integration over the Poisson scene law and the Palm limit remain.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

/-! ## 1. The normalized reserve limit -/

section NormalizedLimit

/-- **The normalized box limit.**  If the legal pressure limit p is bounded at a
fixed tilt by c_rho * I(t c_rho) + v_rho for every small positive rho, where the
normalization c_rho tends to one and the reserve remainder v_rho tends to zero,
and I is continuous at t, then p is at most I(t).  This is the abstract form of
the paper's passage from the finite-value comparison to p_A <= I_w. -/
theorem le_of_tendsto_reserveNormalization
    {p I : ℝ → ℝ} {t : ℝ}
    (hI : ContinuousAt I t)
    {a c v : ℝ → ℝ}
    (ha : Tendsto a (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hc : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hv : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hcompare : ∀ rho : ℝ, 0 < rho → rho < 1 →
      p t ≤ a rho * I (t * c rho) + v rho) :
    p t ≤ I t := by
  have harg : Tendsto (fun rho : ℝ => t * c rho) (𝓝[>] (0 : ℝ)) (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t)).mul hc
    simpa only [mul_one] using h
  have hIarg : Tendsto (fun rho : ℝ => I (t * c rho)) (𝓝[>] (0 : ℝ)) (𝓝 (I t)) :=
    hI.tendsto.comp harg
  have hprod : Tendsto (fun rho : ℝ => a rho * I (t * c rho))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 * I t)) := ha.mul hIarg
  have hlim : Tendsto (fun rho : ℝ => a rho * I (t * c rho) + v rho)
      (𝓝[>] (0 : ℝ)) (𝓝 (I t)) := by
    have hsum := hprod.add hv
    simpa only [one_mul, add_zero] using hsum
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with rho hrho hlt
  exact hcompare rho hrho hlt

end NormalizedLimit

/-- The normalization factors tend to one. -/
theorem tendsto_one_sub_rpow (e : ℝ) :
    Tendsto (fun rho : ℝ => (1 - rho) ^ e) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hbase : Tendsto (fun rho : ℝ => 1 - rho) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hrho : Tendsto (fun rho : ℝ => rho) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hrho
    simpa using h
  have hcont : ContinuousAt (fun y : ℝ => y ^ e) (1 : ℝ) :=
    (continuousAt_id (x := (1 : ℝ))).rpow_const (Or.inl one_ne_zero)
  have hcomp := hcont.tendsto.comp hbase
  simpa only [Function.comp_def, Real.one_rpow] using hcomp

/-! ## 2. The finite-value comparison gives the value identification -/

section FiniteValueComparison

open Module Manifold OTSelector.Geometry ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- **The finite-value comparison, after the reserve normalization, gives the
weighted value identification.**  The paper's comparison p <= c_rho I_w(t c_rho)
+ v_rho with c_rho -> 1, v_rho -> 0 and I_w continuous at t yields
p(t) <= I_w(t); the legal pressure upper comparison of
FinslerOriginalCollarValueDensity then gives I_w(t) = I_2(t). -/
theorem weightedInf_eq_secondMomentInf_of_finiteValueComparison
    {I : Set ℝ} {δ : ℝ} (Dbins : FiniteScalarBins I δ) (hδ : 0 < δ)
    (hIm : MeasurableSet I)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hpi : Vlasov.IsCoupling pi α β)
    (hI : ∀ᵐ z ∂pi, z.1 ∈ I ∧ z.2 ∈ I) (hgap : ∀ᵐ z ∂pi, δ ≤ z.2 - z.1)
    (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|)
    (qq : ℕ) (hqq : 4 < qq)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin qq → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ => kin z.1 z.2)))
    (hkn : ∀ a b (v : Fin qq → ℝ), 0 ≤ kin a b v)
    (hkb : ∀ a b (v : Fin qq → ℝ), |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin qq → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hα : α Aᶜ = 0) (hβ : β Bᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin qq) (Fin qq) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ B, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hgc : ContinuousOn (Function.uncurry g) K)
    {p : ℝ → ℝ}
    (hp : ∀ t : ℝ, Tendsto (fun R : ℝ =>
      legalMarkedScalePressure qq id id α β kin g R t) atTop (𝓝 (p t)))
    (t : ℝ)
    (hcont : ContinuousAt (fun s : ℝ => legalWeightedInf qq α β kin g s) t)
    (hcompare : ∀ rho : ℝ, 0 < rho → rho < 1 →
      p t ≤ (1 - rho) ^ (1 - 2 / (qq : ℝ)) *
          legalWeightedInf qq α β kin g (t * (1 - rho) ^ (2 / (qq : ℝ))) +
        (C * rho ^ (1 - 2 / (qq : ℝ)) + C * |t| * G * rho)) :
    legalWeightedInf qq α β kin g t = legalSecondMomentInf qq α β kin g t := by
  have hqq2 : (2 : ℝ) < (qq : ℝ) := by exact_mod_cast (by omega : 2 < qq)
  have ha := tendsto_one_sub_rpow (1 - 2 / (qq : ℝ))
  have hc := tendsto_one_sub_rpow (2 / (qq : ℝ))
  have hv : Tendsto (fun rho : ℝ =>
      C * rho ^ (1 - 2 / (qq : ℝ)) + C * |t| * G * rho) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hexp : (0 : ℝ) < 1 - 2 / (qq : ℝ) := by
      have hq0 : (0 : ℝ) < (qq : ℝ) := by linarith
      rw [sub_pos, div_lt_one hq0]
      linarith
    have hrho : Tendsto (fun rho : ℝ => rho) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h1 : Tendsto (fun rho : ℝ => rho ^ (1 - 2 / (qq : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (tendsto_rpow_neg_nhdsGT_zero (y := -(1 - 2 / (qq : ℝ)))
        (by linarith)).inv_tendsto_atTop
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with rho hrho
      change (rho ^ (-(1 - 2 / (qq : ℝ))))⁻¹ = rho ^ (1 - 2 / (qq : ℝ))
      rw [Real.rpow_neg hrho.le]
      simp
    have h2 : Tendsto (fun rho : ℝ => C * rho ^ (1 - 2 / (qq : ℝ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (h1.const_mul C)
    have h3 : Tendsto (fun rho : ℝ => C * |t| * G * rho) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hrho.const_mul (C * |t| * G))
    simpa using h2.add h3
  have hcle : p t ≤ legalWeightedInf qq α β kin g t :=
    le_of_tendsto_reserveNormalization
      (a := fun rho : ℝ => (1 - rho) ^ (1 - 2 / (qq : ℝ)))
      (c := fun rho : ℝ => (1 - rho) ^ (2 / (qq : ℝ)))
      (v := fun rho : ℝ => C * rho ^ (1 - 2 / (qq : ℝ)) + C * |t| * G * rho)
      hcont ha hc hv hcompare
  obtain ⟨p₀, hp₀, hbounds⟩ :=
    exists_legalPressureLimit_ge_weighted_le_secondMoment Dbins hδ hIm pi α β hpi
      hI hgap hsep qq hqq hC hG hk hkn hkb hhom hg hgb hA hB hα hβ hK matrix
      hmatrix hpos hlegal hactual hgc
  have hp_eq : p₀ = p := funext fun s => tendsto_nhds_unique (hp₀ s) (hp s)
  have hlow : legalWeightedInf qq α β kin g t ≤ legalSecondMomentInf qq α β kin g t :=
    (hbounds t).1
  have hup : legalSecondMomentInf qq α β kin g t ≤ p₀ t := (hbounds t).2
  rw [hp_eq] at hup
  exact le_antisymm hlow (hup.trans hcle)

end FiniteValueComparison

/-! ## 3. Vanishing reserve budgets are the value identification -/

section StationaryReserveLifting

variable {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
  {g : ℝ → ℝ → ℝ} {t : ℝ}

/-- **The named stationary lifting input.**  For every positive value budget, any
weighted stationary matching can be replaced by a weighted stationary matching
which is collar-supported and whose signed value is larger by at most that
budget.  This is the paper's reserve construction after the finite completion,
with the reserve density sent to zero. -/
def StationaryReserveLifting (q : ℕ) (α β : Measure ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ B : ℝ, 0 < B →
    ∀ Q : LegalWeightedStationaryPoissonMatching q α β kin g,
      ∃ Q' : LegalWeightedStationaryPoissonMatching q α β kin g,
        Q'.value t ≤ Q.value t + B ∧
        ∃ (C : Set (ℝ × ℝ)) (c : ℝ), 0 < c ∧
          (∀ p ∈ C, p.1 < p.2 → ∀ v : Fin q → ℝ, c * ‖v‖ ^ 2 ≤ kin p.1 p.2 v) ∧
          (∀ᵐ m ∂legalMarkedJointPalm q Q'.law, m.1 ∈ C)

/-- A collar-supported weighted stationary matching has a finite unweighted
second moment. -/
theorem secondMomentSubclass_of_collar_general
    {C : Set (ℝ × ℝ)} {c : ℝ} (hc : 0 < c)
    (hLB : ∀ p ∈ C, p.1 < p.2 → ∀ v : Fin q → ℝ, c * ‖v‖ ^ 2 ≤ kin p.1 p.2 v)
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hQ : ∀ᵐ m ∂legalMarkedJointPalm q Q.law, m.1 ∈ C) :
    Q.secondMomentSubclass := by
  change Integrable (fun m => ‖m.2‖ ^ 2) (legalMarkedJointPalm q Q.law)
  have hdom : Integrable (fun m : PhysicalPairPalmMark (Fin q) =>
      (1 / c) * kin m.1.1 m.1.2 m.2) (legalMarkedJointPalm q Q.law) :=
    Q.kinetic_integrable.const_mul (1 / c)
  have hmeas : AEStronglyMeasurable
      (fun m : PhysicalPairPalmMark (Fin q) => ‖m.2‖ ^ 2)
      (legalMarkedJointPalm q Q.law) :=
    ((measurable_norm.comp measurable_snd).pow_const 2).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards [hQ, Q.ae_palm_forward] with m hm hforward
  have hkin := hLB m.1 hm hforward m.2
  have hnonneg : 0 ≤ ‖m.2‖ ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [show (1 / c) * kin m.1.1 m.1.2 m.2 = kin m.1.1 m.1.2 m.2 / c from by ring]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hkin)

/-- Vanishing stationary reserve budgets give the second-moment pressure bound
I_2 <= I_w. -/
theorem legalSecondMomentInf_le_legalWeightedInf_of_stationaryReserveLifting
    (hkn : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G)
    (hne : Nonempty (LegalWeightedStationaryPoissonMatching q α β kin g))
    (hlift : StationaryReserveLifting q α β kin g t) :
    legalSecondMomentInf q α β kin g t ≤ legalWeightedInf q α β kin g t := by
  refine le_of_forall_pos_le_add (fun eps heps => ?_)
  have hB0 : 0 < eps / 2 := by linarith
  have hbdd : BddBelow (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
      q α β kin g => Q.value t)) := by
    refine ⟨-(|t| * G), ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact Q.value_lower_bound hkn hgb t
  have hneR : (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
      q α β kin g => Q.value t)).Nonempty :=
    hne.elim fun Q => ⟨Q.value t, Q, rfl⟩
  obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hneR
    (show sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g =>
        Q.value t)) < sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
        q α β kin g => Q.value t)) + eps / 2 from lt_add_of_pos_right _ hB0)
  obtain ⟨Q, rfl⟩ := hy
  obtain ⟨Q', hQ'le, C, c, hc, hLB, hsupp⟩ := hlift (eps / 2) hB0 Q
  have hsub : Q'.secondMomentSubclass :=
    secondMomentSubclass_of_collar_general hc hLB Q' hsupp
  have hI2 : legalSecondMomentInf q α β kin g t ≤ Q'.value t := by
    have hbdd2 : BddBelow ((fun Q : LegalWeightedStationaryPoissonMatching q α β kin g =>
        Q.value t) '' {Q : LegalWeightedStationaryPoissonMatching q α β kin g |
          Q.secondMomentSubclass}) := by
      refine ⟨-(|t| * G), ?_⟩
      rintro _ ⟨Q, _hQ, rfl⟩
      exact Q.value_lower_bound hkn hgb t
    exact csInf_le hbdd2 ⟨Q', hsub, rfl⟩
  have hIw : legalWeightedInf q α β kin g t ≤ Q.value t := by
    have hdef : legalWeightedInf q α β kin g t = sInf (Set.range
        (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)) := rfl
    rw [hdef]
    exact csInf_le hbdd ⟨Q, rfl⟩
  have hylt' : Q.value t < sInf (Set.range (fun Q : LegalWeightedStationaryPoissonMatching
      q α β kin g => Q.value t)) + eps / 2 := hylt
  have hIwlt : Q.value t < legalWeightedInf q α β kin g t + eps / 2 := by
    have hdef : legalWeightedInf q α β kin g t = sInf (Set.range
        (fun Q : LegalWeightedStationaryPoissonMatching q α β kin g => Q.value t)) := rfl
    rw [hdef]
    exact hylt'
  linarith

/-- **Vanishing stationary reserve budgets give the value identification
I_w = I_2.** -/
theorem legalWeightedInf_eq_legalSecondMomentInf_of_stationaryReserveLifting
    (hkn : ∀ a b (v : Fin q → ℝ), 0 ≤ kin a b v) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G)
    (hne : Nonempty (LegalWeightedStationaryPoissonMatching q α β kin g))
    (hne2 : {Q : LegalWeightedStationaryPoissonMatching q α β kin g |
      Q.secondMomentSubclass}.Nonempty)
    (hlift : StationaryReserveLifting q α β kin g t) :
    legalWeightedInf q α β kin g t = legalSecondMomentInf q α β kin g t := by
  have hle := legalSecondMomentInf_le_legalWeightedInf_of_stationaryReserveLifting
    (q := q) (α := α) (β := β) (kin := kin) (g := g) (t := t) hkn hgb hne hlift
  have hge := legalWeightedInf_le_legalSecondMomentInf (q := q) (α := α) (β := β)
    (kin := kin) (g := g) hkn hgb hne2 t
  exact le_antisymm hge hle

end StationaryReserveLifting

end OTSelector.Reconstruction
