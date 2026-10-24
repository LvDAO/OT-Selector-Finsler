import OTSelector.Reconstruction.FinslerOriginalReserveLiftingMeasurable

/-!
# Reserve value assembly: from retained-core boundary loss to I_w = I_2

This module is the assembly point of the hvalue lane.  The dilation and
boundary-loss estimates of FinslerOriginalRetainedCoreDilation say that the
retained core pressure is the dilated weighted stationary value
(1 - rho)^(1 - 2/q) I_w(t (1 - rho)^(2/q)) plus a boundary loss of the form
(1 - rho)^(1 - 2/q) * B * delta, where B is the uniform pressure bound and delta
is the mass of the part of the population that is not retained.

1. **Boundary loss is covered by the explicit reserve cost**
   (boundaryLoss_le_reserveCost): if the boundary mass delta is at most rho and
   the uniform bound B is at most C + |t| G, then the boundary loss is at most
   the explicit reserve cost C rho^(1 - 2/q) + C |t| G rho of the paper.  So the
   "up to boundary losses" of the dilation step is exactly the reserve term of
   the finite-value comparison.

2. **The finite-value comparison with explicit reserve cost**
   (finiteValueComparisonWithReserveCost_of_boundaryLoss): the retained-core
   dilation inequality with a boundary loss satisfying those two estimates
   yields FiniteValueComparisonWithReserveCost.

3. **The pressure comparison**
   (legalPressureLimit_le_weightedInf_of_boundaryLoss): the actual legal
   pressure limit is at most the weighted stationary value.

4. **The value identification I_w = I_2**
   (weightedInf_eq_secondMomentInf_of_boundaryLoss): the full assembly, reducing
   the value identification to the retained-core dilation inequality with
   boundary loss.  The remaining input is only the Palm identification: that the
   marked Poisson legal pressure limit is bounded by the dilated weighted
   stationary value plus the boundary loss (the measurable-selection and Palm
   construction both live in the imported modules).

## Remaining sub-gap

The theorem (4) is conditional on hcore, the retained-core dilation inequality
with boundary loss.  Its dilation part is proved in
FinslerOriginalRetainedCoreDilation (constant-density and retained-region forms,
together with the boundary-loss bound B * mu.real S^c).  What (4) still assumes
is the Palm identification: that the population measure of that statement is the
Palm law of the candidate weighted stationary matching and that the local legal
pressure function is its pressure functional.  That identification is a modeling
step; no statement about the reserve algebra is missing.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-- **Boundary loss is covered by the explicit reserve cost.**  The dilation
boundary loss lam^(1 - 2/q) * (B * delta), with lam = 1 - rho, retained mass
deficit delta <= rho and uniform pressure bound B <= C + |t| G, is at most the
reserve cost C rho^(1 - 2/q) + C |t| G rho of the finite-value comparison. -/
theorem boundaryLoss_le_reserveCost
    {q : ℕ} (hq : 2 < q) (t rho C G B delta : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hC0 : 0 ≤ C) (hC1 : 1 ≤ C) (hG0 : 0 ≤ G)
    (hB : B ≤ C + |t| * G) (hBnn : 0 ≤ B) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ rho) :
    (1 - rho) ^ (1 - 2 / (q : ℝ)) * (B * delta) ≤
      C * rho ^ (1 - 2 / (q : ℝ)) + C * |t| * G * rho := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hs0 : 0 ≤ 1 - 2 / (q : ℝ) := by
    have h : 2 / (q : ℝ) ≤ 1 :=
      (div_le_one hq0).mpr (by exact_mod_cast hq.le)
    linarith
  have hs1 : 1 - 2 / (q : ℝ) ≤ 1 := by
    have h : 0 ≤ 2 / (q : ℝ) := le_of_lt (div_pos (by norm_num) hq0)
    linarith
  have hlam0 : 0 < 1 - rho := by linarith
  have hlam1 : 1 - rho ≤ 1 := by linarith
  have hpw : (1 - rho) ^ (1 - 2 / (q : ℝ)) ≤ 1 :=
    Real.rpow_le_one hlam0.le hlam1 hs0
  have hCG0 : 0 ≤ C + |t| * G := by
    have h1 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
    linarith
  have hprod : B * delta ≤ (C + |t| * G) * rho :=
    mul_le_mul hB hdelta hdelta0 hCG0
  have hprod0 : 0 ≤ B * delta := mul_nonneg hBnn hdelta0
  have hstep : (1 - rho) ^ (1 - 2 / (q : ℝ)) * (B * delta) ≤
      1 * ((C + |t| * G) * rho) :=
    mul_le_mul hpw hprod hprod0 (by norm_num)
  have hrho_le : rho ≤ rho ^ (1 - 2 / (q : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hrho0 hrho1.le hs1
    rwa [Real.rpow_one] at h
  have hCterm : C * rho ^ (1 - 2 / (q : ℝ)) + C * |t| * G * rho ≥
      (C + |t| * G) * rho := by
    have h1 : 0 ≤ C * (rho ^ (1 - 2 / (q : ℝ)) - rho) :=
      mul_nonneg hC0 (sub_nonneg.mpr hrho_le)
    have h2 : 0 ≤ (C - 1) * (|t| * G * rho) :=
      mul_nonneg (sub_nonneg.mpr hC1)
        (mul_nonneg (mul_nonneg (abs_nonneg t) hG0) hrho0.le)
    nlinarith [h1, h2]
  nlinarith [hstep, hCterm]

/-- **The finite-value comparison with explicit reserve cost from the
retained-core dilation inequality with boundary loss.** -/
theorem finiteValueComparisonWithReserveCost_of_boundaryLoss
    {q : ℕ} (hq : 2 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {p : ℝ → ℝ} {C G : ℝ}
    (hC0 : 0 ≤ C) (hC1 : 1 ≤ C) (hG0 : 0 ≤ G)
    (Bf df : ℝ → ℝ → ℝ)
    (hB : ∀ t rho : ℝ, 0 < rho → rho < 1 → Bf t rho ≤ C + |t| * G)
    (hBf0 : ∀ t rho : ℝ, 0 < rho → rho < 1 → 0 ≤ Bf t rho)
    (hd0 : ∀ t rho : ℝ, 0 < rho → rho < 1 → 0 ≤ df t rho)
    (hdrho : ∀ t rho : ℝ, 0 < rho → rho < 1 → df t rho ≤ rho)
    (hcore : ∀ t rho : ℝ, 0 < rho → rho < 1 →
      p t ≤ (1 - rho) ^ (1 - 2 / (q : ℝ)) *
          legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) +
        (1 - rho) ^ (1 - 2 / (q : ℝ)) * (Bf t rho * df t rho)) :
    FiniteValueComparisonWithReserveCost q α β kin g p C G := by
  intro t rho hrho0 hrho1
  have hbl := boundaryLoss_le_reserveCost hq t rho C G (Bf t rho) (df t rho)
    hrho0 hrho1 hC0 hC1 hG0 (hB t rho hrho0 hrho1) (hBf0 t rho hrho0 hrho1)
    (hd0 t rho hrho0 hrho1) (hdrho t rho hrho0 hrho1)
  have hcore' := hcore t rho hrho0 hrho1
  linarith [hcore', hbl]

/-- **The legal pressure limit is at most the weighted stationary value**,
obtained from the retained-core dilation inequality with boundary loss. -/
theorem legalPressureLimit_le_weightedInf_of_boundaryLoss
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {p : ℝ → ℝ} {C G : ℝ} (hq : 4 < q)
    (hC0 : 0 ≤ C) (hC1 : 1 ≤ C) (hG0 : 0 ≤ G)
    (Bf df : ℝ → ℝ → ℝ)
    (hB : ∀ t rho : ℝ, 0 < rho → rho < 1 → Bf t rho ≤ C + |t| * G)
    (hBf0 : ∀ t rho : ℝ, 0 < rho → rho < 1 → 0 ≤ Bf t rho)
    (hd0 : ∀ t rho : ℝ, 0 < rho → rho < 1 → 0 ≤ df t rho)
    (hdrho : ∀ t rho : ℝ, 0 < rho → rho < 1 → df t rho ≤ rho)
    (hcore : ∀ t rho : ℝ, 0 < rho → rho < 1 →
      p t ≤ (1 - rho) ^ (1 - 2 / (q : ℝ)) *
          legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) +
        (1 - rho) ^ (1 - 2 / (q : ℝ)) * (Bf t rho * df t rho))
    (hcont : ∀ t : ℝ, ContinuousAt (fun s : ℝ => legalWeightedInf q α β kin g s) t)
    (t : ℝ) :
    p t ≤ legalWeightedInf q α β kin g t :=
  legalPressureLimit_le_weightedInf_of_reserveComparison hq hcont
    (finiteValueComparisonWithReserveCost_of_boundaryLoss (by omega : 2 < q)
      hC0 hC1 hG0 Bf df hB hBf0 hd0 hdrho hcore) t

/-- **The value identification I_w = I_2 from the retained-core dilation
inequality with boundary loss.**  The only input beyond the imported weighted
stationary comparison machinery is hcore: the retained-core dilation inequality
with boundary loss.  Everything else is assembled: the reserve absorption, the
finite-value comparison, the normalized pressure limit, and the weighted
stationary upper comparison. -/
theorem weightedInf_eq_secondMomentInf_of_boundaryLoss
    {I : Set ℝ} {δ : ℝ} (Dbins : FiniteScalarBins I δ) (hδ : 0 < δ)
    (hIm : MeasurableSet I)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hpi : Vlasov.IsCoupling pi α β)
    (hI : ∀ᵐ z ∂pi, z.1 ∈ I ∧ z.2 ∈ I) (hgap : ∀ᵐ z ∂pi, δ ≤ z.2 - z.1)
    (hsep : ∀ᵐ z ∂α.prod β, δ ≤ |z.2 - z.1|)
    (qq : ℕ) (hqq : 4 < qq)
    {C G : ℝ} (hC : 0 ≤ C) (hC1 : 1 ≤ C) (hG : 0 ≤ G)
    {kin : ℝ → ℝ → (Fin qq → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun z : ℝ × ℝ => kin z.1 z.2)))
    (hkn : ∀ a b (v : Fin qq → ℝ), 0 ≤ kin a b v)
    (hkb : ∀ a b (v : Fin qq → ℝ), |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin qq → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G)
    {A Bs : Set ℝ} (hA : IsCompact A) (hBs : IsCompact Bs)
    (hα : α Aᶜ = 0) (hβ : β Bsᶜ = 0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (matrix : (ℝ × ℝ) → Matrix (Fin qq) (Fin qq) ℝ)
    (hmatrix : ContinuousOn matrix K) (hpos : ∀ w ∈ K, (matrix w).PosDef)
    (hlegal : ∀ a ∈ A, ∀ b ∈ Bs, a < b → (a, b) ∈ K)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    (hgc : ContinuousOn (Function.uncurry g) K)
    {p : ℝ → ℝ}
    (hp : ∀ t : ℝ, Tendsto (fun R : ℝ =>
      legalMarkedScalePressure qq id id α β kin g R t) atTop (𝓝 (p t)))
    (Bf df : ℝ → ℝ → ℝ)
    (hB : ∀ t rho : ℝ, 0 < rho → rho < 1 → Bf t rho ≤ C + |t| * G)
    (hBf0 : ∀ t rho : ℝ, 0 < rho → rho < 1 → 0 ≤ Bf t rho)
    (hd0 : ∀ t rho : ℝ, 0 < rho → rho < 1 → 0 ≤ df t rho)
    (hdrho : ∀ t rho : ℝ, 0 < rho → rho < 1 → df t rho ≤ rho)
    (hcore : ∀ t rho : ℝ, 0 < rho → rho < 1 →
      p t ≤ (1 - rho) ^ (1 - 2 / (qq : ℝ)) *
          legalWeightedInf qq α β kin g (t * (1 - rho) ^ (2 / (qq : ℝ))) +
        (1 - rho) ^ (1 - 2 / (qq : ℝ)) * (Bf t rho * df t rho))
    (t : ℝ)
    (hcont : ContinuousAt (fun s : ℝ => legalWeightedInf qq α β kin g s) t) :
    legalWeightedInf qq α β kin g t = legalSecondMomentInf qq α β kin g t :=
  weightedInf_eq_secondMomentInf_of_finiteValueComparisonCost Dbins hδ hIm pi α β
    hpi hI hgap hsep qq hqq hC hG hk hkn hkb hhom hg hgb hA hBs hα hβ hK matrix
    hmatrix hpos hlegal hactual hgc hp t hcont
    (finiteValueComparisonWithReserveCost_of_boundaryLoss (q := qq)
      (by omega : 2 < qq) hC hC1 hG Bf df hB hBf0 hd0 hdrho hcore)

end OTSelector.Reconstruction
