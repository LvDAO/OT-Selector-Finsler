import OTSelector.Reconstruction.FinslerCoefficientPressureFreezing

/-!
# Matching moment bound from on-diagonal Hessian positivity

The blockwise stabilization error of the hupper lane is controlled by the
*matching moment* of the optimal matching: the total squared matched
displacement of the block marked cloud.  This module produces that estimate from
the on-diagonal Hessian positivity of the frozen physical cost.

Near the diagonal the frozen physical cost `frozenPhysicalCost` is the quadratic
form `matrixQuadratic (C.matrix z p) v` of the positive definite frozen inverse
compliance, and `OriginalPopulationCoefficientCore.exists_quadratic_lower_bound`
produces a uniform strictly positive constant `m` with

  m * ‖v‖ ^ 2 ≤ matrixQuadratic (C.matrix z p) v.

That is the Taylor lower bound of the physical cost: a small average matching
cost forces a small total squared displacement.  The main theorem of the module
is the resulting matching moment bound

  sum (squared matched displacement) ≤ (dim / ((1 - ε) * m)) * sum (matching cost),

and its per-pair average form: if the average matching cost per pair is at most
`eta`, then the average squared matched displacement is at most
`(dim / ((1 - ε) * m)) * eta`.  These are the constants supplied to the refined
edge-error estimate of `FinslerOriginalBlockwiseStabilization`.

The finite-dimensional arithmetic (`sqDisplacement_le_card_mul_norm_sq`) passes
between the coordinate squared displacement of the lane (`sum v l ^ 2`) and the
fixed vector norm of the frozen quadratic bound (`‖v‖ ^ 2`).  The last theorem
derives the moment constant directly from the actual positive definite
coefficient field of an `OriginalPopulationCoefficientCore`; the true-cost form
follows by composing with `relative_cost_of_quadratic_remainder`.

The exact remaining sub-gap is only the choice of the true-cost remainder: the
moment estimate here is stated for the frozen quadratic cost (or for a cost array
together with the Taylor remainder comparison), while the pressure lane enters
through the actual distance cost, for which the remainder is the input already
isolated in `FinslerCoefficientPressureFreezing`.  No analysis input is assumed
silently here: both the quadratic lower bound and the remainder comparison are
explicit hypotheses, and both are available from the frozen coefficient modules.
-/

open Set Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-! ## Squared coordinate displacement of a finite vector family -/

/-- The total squared coordinate displacement of a finite family of vectors. -/
def sqDisplacement {n : Type*} [Fintype n] (v : n → ℝ) : ℝ := ∑ i, v i ^ 2

@[simp] theorem sqDisplacement_zero {n : Type*} [Fintype n] :
    sqDisplacement (0 : n → ℝ) = 0 := by
  simp [sqDisplacement]

theorem sqDisplacement_nonneg {n : Type*} [Fintype n] (v : n → ℝ) :
    0 ≤ sqDisplacement v := by
  simp only [sqDisplacement]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The coordinate squared displacement is controlled by the dimension times the
fixed vector norm squared. -/
theorem sqDisplacement_le_card_mul_norm_sq {n : Type*} [Fintype n] (v : n → ℝ) :
    sqDisplacement v ≤ (Fintype.card n : ℝ) * ‖v‖ ^ 2 := by
  have hterm : ∀ i : n, v i ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    have hle : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm (f := v) i
    have habs : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using hle
    have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 2
    simpa [sq_abs] using hpow
  calc sqDisplacement v = ∑ i : n, v i ^ 2 := rfl
    _ ≤ ∑ _i : n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card n : ℝ) * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## Per-pair quadratic lower bounds control the matching moment -/

/-- A per-pair lower quadratic bound on the frozen cost controls the squared
displacement with constant `m / card`. -/
theorem sqDisplacement_le_card_mul_of_quadratic_lower {n : Type*} [Fintype n]
    {v : n → ℝ} {Q m : ℝ} (hm : 0 < m) (hcard : 0 < Fintype.card n)
    (hQ : m * ‖v‖ ^ 2 ≤ Q) :
    (m / (Fintype.card n : ℝ)) * sqDisplacement v ≤ Q := by
  have hcardpos : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast hcard
  have hmul : (m / (Fintype.card n : ℝ)) * sqDisplacement v ≤
      (m / (Fintype.card n : ℝ)) * ((Fintype.card n : ℝ) * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (sqDisplacement_le_card_mul_norm_sq v) (by positivity)
  have hcancel : (m / (Fintype.card n : ℝ)) * ((Fintype.card n : ℝ) * ‖v‖ ^ 2) =
      m * ‖v‖ ^ 2 := by
    field_simp
  linarith

/-- **Matching moment bound.**  If every matched pair has frozen cost at least a
positive multiple of its squared displacement, and the actual cost array is
within a relative `ε` Taylor remainder of the frozen cost, then the total squared
matched displacement is bounded by the total matching cost. -/
theorem sum_sqDisplacement_le_of_pairwise_lower {N : ℕ} {n : Type*} [Fintype n]
    (hcard : 0 < Fintype.card n) {v : Fin N → n → ℝ} {Q cost : Fin N → ℝ}
    {m ε : ℝ} (hm : 0 < m) (_hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hQ : ∀ i, m * ‖v i‖ ^ 2 ≤ Q i)
    (hcost : ∀ i, |cost i - Q i| ≤ ε * m * ‖v i‖ ^ 2) :
    ∑ i, sqDisplacement (v i) ≤
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i := by
  have hcardpos : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast hcard
  have hc : 0 < (1 - ε) * m := mul_pos (by linarith) hm
  have hc0 : 0 < ((1 - ε) * m) / (Fintype.card n : ℝ) := div_pos hc hcardpos
  have hnonneg : (0 : ℝ) ≤ 1 - ε := by linarith
  have hpair : ∀ i : Fin N,
      (((1 - ε) * m) / (Fintype.card n : ℝ)) * sqDisplacement (v i) ≤ cost i := by
    intro i
    have hbase : m * ‖v i‖ ^ 2 - ε * m * ‖v i‖ ^ 2 ≤ cost i := by
      have h := (abs_le.mp (hcost i)).1
      nlinarith [hQ i]
    have hsq : (m / (Fintype.card n : ℝ)) * sqDisplacement (v i) ≤ m * ‖v i‖ ^ 2 := by
      have hmul : (m / (Fintype.card n : ℝ)) * sqDisplacement (v i) ≤
          (m / (Fintype.card n : ℝ)) * ((Fintype.card n : ℝ) * ‖v i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sqDisplacement_le_card_mul_norm_sq (v i)) (by positivity)
      have hcancel :
          (m / (Fintype.card n : ℝ)) * ((Fintype.card n : ℝ) * ‖v i‖ ^ 2) =
            m * ‖v i‖ ^ 2 := by
        field_simp
      linarith
    have hstep : (((1 - ε) * m) / (Fintype.card n : ℝ)) * sqDisplacement (v i) =
        (1 - ε) * ((m / (Fintype.card n : ℝ)) * sqDisplacement (v i)) := by ring
    rw [hstep]
    nlinarith [mul_le_mul_of_nonneg_left hsq hnonneg]
  have hsum : (((1 - ε) * m) / (Fintype.card n : ℝ)) *
      ∑ i, sqDisplacement (v i) ≤ ∑ i, cost i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hpair i
  have hkey : ∑ i, sqDisplacement (v i) ≤
      (∑ i, cost i) / (((1 - ε) * m) / (Fintype.card n : ℝ)) := by
    refine (le_div_iff₀ hc0).mpr ?_
    rwa [mul_comm]
  have hconst : (∑ i, cost i) / (((1 - ε) * m) / (Fintype.card n : ℝ)) =
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i := by
    field_simp
  rwa [hconst] at hkey

/-- **Average matching moment bound.**  If the average matching cost per pair is
at most `eta`, the average squared matched displacement is at most
`(dim / ((1 - ε) * m)) * eta`. -/
theorem average_sqDisplacement_le_of_average_cost {N : ℕ} {n : Type*} [Fintype n]
    (hcard : 0 < Fintype.card n) {v : Fin N → n → ℝ} {Q cost : Fin N → ℝ}
    {m ε eta : ℝ} (hm : 0 < m) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hN : 0 < N)
    (hQ : ∀ i, m * ‖v i‖ ^ 2 ≤ Q i)
    (hcost : ∀ i, |cost i - Q i| ≤ ε * m * ‖v i‖ ^ 2)
    (havg : (1 / (N : ℝ)) * ∑ i, cost i ≤ eta) :
    (1 / (N : ℝ)) * ∑ i, sqDisplacement (v i) ≤
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * eta := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcardpos : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast hcard
  have hK : 0 ≤ (Fintype.card n : ℝ) / ((1 - ε) * m) := by positivity
  have hsum := sum_sqDisplacement_le_of_pairwise_lower hcard hm hε0 hε1 hQ hcost
  have h1 : (1 / (N : ℝ)) * ∑ i, sqDisplacement (v i) ≤
      (1 / (N : ℝ)) * (((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have h2 : (1 / (N : ℝ)) * (((Fintype.card n : ℝ) / ((1 - ε) * m)) * ∑ i, cost i) =
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ((1 / (N : ℝ)) * ∑ i, cost i) := by
    ring
  have h3 : ((Fintype.card n : ℝ) / ((1 - ε) * m)) * ((1 / (N : ℝ)) * ∑ i, cost i) ≤
      ((Fintype.card n : ℝ) / ((1 - ε) * m)) * eta :=
    mul_le_mul_of_nonneg_left havg hK
  linarith

/-- **Matching moment bound with a bounded probe term.**  In the marked lane a
matched edge cost is the kinetic cost plus `t` times a probe value bounded by
`G`.  The bounded probe is compensated by the budget term `|t| * G * count`. -/
theorem sum_sqDisplacement_le_of_cost_sub_probe {N : ℕ} {n : Type*} [Fintype n]
    {v : Fin N → n → ℝ} {cost : Fin N → ℝ} {c t G : ℝ} (hc : 0 < c)
    (h : ∀ i, c * sqDisplacement (v i) - |t| * G ≤ cost i) :
    ∑ i, sqDisplacement (v i) ≤
      (∑ i, cost i + |t| * G * (N : ℝ)) / c := by
  have hpoint : ∀ i : Fin N, c * sqDisplacement (v i) ≤ cost i + |t| * G := by
    intro i
    linarith [h i]
  have hsum : c * ∑ i, sqDisplacement (v i) ≤
      ∑ i, cost i + |t| * G * (N : ℝ) := by
    calc c * ∑ i, sqDisplacement (v i) = ∑ i, c * sqDisplacement (v i) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ i, (cost i + |t| * G) := Finset.sum_le_sum fun i _ => hpoint i
      _ = ∑ i, cost i + |t| * G * (N : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  refine (le_div_iff₀ hc).mpr ?_
  rwa [mul_comm]

/-! ## The moment constant from the actual frozen coefficient field -/

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

omit [BorelSpace E] in
/-- **Matching moment constant from on-diagonal Hessian positivity.**  The
positive definite frozen coefficient of an original population coefficient core
supplies one strictly positive constant such that, for every finite matching and
every displacement array in the retained roots, the total squared matched
displacement is bounded by the total frozen quadratic cost. -/
theorem OriginalPopulationCoefficientCore.exists_matching_moment_constant
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hdim : 0 < finrank ℝ (P C.seedIndex).seed.covector.ker) :
    ∃ c > 0, ∀ (N : ℕ) (z : Fin N → Fin N → Z) (p : Fin N → Fin N → ℝ × ℝ)
        (v : Fin N → Fin N →
          Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
        (σ : Fin N → Fin N),
      (∀ i j, z i j ∈ C.roots) → (∀ i j, p i j ∈ C.window.region) →
      c * ∑ i, sqDisplacement (v i (σ i)) ≤
        ∑ i, matrixQuadratic (C.matrix (z i (σ i)) (p i (σ i))) (v i (σ i)) := by
  obtain ⟨m, hm, hbound⟩ := C.exists_quadratic_lower_bound
  refine ⟨m / (finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ), by positivity, ?_⟩
  intro N z p v σ hz hp
  have hcard : 0 < Fintype.card (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) := by
    simpa using hdim
  have hpair : ∀ i : Fin N,
      (m / (finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ)) *
          sqDisplacement (v i (σ i)) ≤
        matrixQuadratic (C.matrix (z i (σ i)) (p i (σ i))) (v i (σ i)) := by
    intro i
    have hQ := hbound (z i (σ i)) (hz i (σ i)) (p i (σ i)) (hp i (σ i)) (v i (σ i))
    have h := sqDisplacement_le_card_mul_of_quadratic_lower (n := Fin (finrank ℝ
      (P C.seedIndex).seed.covector.ker)) (v := v i (σ i))
      (Q := matrixQuadratic (C.matrix (z i (σ i)) (p i (σ i))) (v i (σ i)))
      (m := m) hm hcard hQ
    simpa using h
  calc (m / (finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ)) *
        ∑ i, sqDisplacement (v i (σ i))
      = ∑ i, (m / (finrank ℝ (P C.seedIndex).seed.covector.ker : ℝ)) *
          sqDisplacement (v i (σ i)) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, matrixQuadratic (C.matrix (z i (σ i)) (p i (σ i))) (v i (σ i)) :=
        Finset.sum_le_sum fun i _ => hpair i

end OTSelector.Reconstruction
