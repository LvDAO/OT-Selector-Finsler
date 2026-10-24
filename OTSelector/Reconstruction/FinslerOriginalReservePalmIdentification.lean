import OTSelector.Reconstruction.FinslerOriginalRetainedCoreDilation
import OTSelector.Reconstruction.FinslerOriginalReserveValueAssembly

/-!
# Palm identification and the reserve value assembly

This module replaces the abstract hypothesis hcore of
FinslerOriginalReserveValueAssembly by the proved retained-core dilation lemmas,
and it isolates the Palm identification in a single explicit inequality.

The retained-core dilation (FinslerOriginalRetainedCoreDilation) says that the
pressure of the retained core with constant retained density lam against the
population measure mu is

  int lam^(-2/q) I(t lam^(2/q)) d(mu.withDensity (lam on S)) = lam^(1-2/q) int_S I(t lam^(2/q)) dmu,

and that it differs from the dilated full population pressure by a boundary
loss of at most lam^(1-2/q) B mu.real S^c.  The reserve assembly
(FinslerOriginalReserveValueAssembly) turns the boundary loss into the explicit
reserve cost C rho^(1-2/q) + C |t| G rho.

Here the remaining modeling hypothesis is the Palm identification:

  (Palm) p t is at most the retained-core Palm pressure
         int (1-rho)^(-2/q) I(t (1-rho)^(2/q)) d(mu.withDensity ((1-rho) on S_rho)),

and the stationarity comparison

  (Stationarity) the population pressure int I(t (1-rho)^(2/q)) dmu at the
         dilated tilt is at most the weighted stationary value I_w at that tilt.

1. **Dilation plus boundary loss from the Palm identification**
   (retainedPressure_le_dilated_add_boundary): (Palm) and the boundary-loss bound
   give p t <= lam^(1-2/q) int I + lam^(1-2/q) (B delta).

2. **Finite-value comparison from the Palm identification**
   (finiteValueComparisonWithReserveCost_of_palmIdentification): adding the
   stationarity comparison and absorbing the boundary loss gives
   FiniteValueComparisonWithReserveCost.

3. **Value identification I_w = I_2 from the Palm identification**
   (weightedInf_eq_secondMomentInf_of_palmIdentification): the full assembly,
   now unconditional except for (Palm) and (Stationarity).

## Remaining sub-gap

Only (Palm) and (Stationarity) are assumed.  (Palm) is the identification of the
marked Poisson pressure limit with the Palm integral of the local legal pressure
function of the candidate weighted stationary matching (the reserve construction
and the Palm lifting chain provide the candidate; the equality of the pressure
limit with its Palm integral is the remaining modeling statement).
(Stationarity) is the statement that the dilated retained core is a near-minimizer
of the weighted stationary value.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

variable {X : Type*} [MeasurableSpace X]

/-- **Dilation plus boundary loss from the Palm identification.**  If the
pressure p is at most the retained-core Palm pressure with constant retained
density lam on the measurable region S, and the boundary mass mu.real S^c is at
most delta, then p is at most the dilated population pressure plus the boundary
loss lam^(1-2/q) (B delta). -/
theorem retainedPressure_le_dilated_add_boundary
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S)
    {q : ℕ} (I : X → ℝ → ℝ) (t : ℝ) {lam B : ℝ} (hlam : 0 < lam)
    (hBnn : 0 ≤ B)
    (hIbound : ∀ x, |I x (t * lam ^ (2 / (q : ℝ)))| ≤ B)
    (hint : Integrable (fun x => I x (t * lam ^ (2 / (q : ℝ)))) μ)
    {p : ℝ}
    (hpalm : p ≤ ∫ x, lam ^ (-(2 / (q : ℝ))) * I x (t * lam ^ (2 / (q : ℝ)))
        ∂(μ.withDensity (S.indicator (fun _ => ENNReal.ofReal lam))))
    {delta : ℝ} (hdelta : μ.real Sᶜ ≤ delta) :
    p ≤ lam ^ (1 - 2 / (q : ℝ)) * (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) +
      lam ^ (1 - 2 / (q : ℝ)) * (B * delta) := by
  have hbd := retainedCore_boundaryLoss (μ := μ) (S := S) hS
    (f := fun x => I x (t * lam ^ (2 / (q : ℝ)))) hIbound hint
  have hSle : (∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) ≤
      (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) + B * μ.real Sᶜ := by
    have h := (abs_le.mp hbd).2
    linarith
  have hbd2 : B * μ.real Sᶜ ≤ B * delta := mul_le_mul_of_nonneg_left hdelta hBnn
  have hfac : 0 ≤ lam ^ (1 - 2 / (q : ℝ)) := Real.rpow_nonneg hlam.le _
  have hdil := retainedPressure_indicator_scale (μ := μ) (S := S) (q := q) hS I t hlam
  rw [hdil] at hpalm
  calc p ≤ lam ^ (1 - 2 / (q : ℝ)) *
        (∫ x in S, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) := hpalm
    _ ≤ lam ^ (1 - 2 / (q : ℝ)) *
        ((∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) + B * μ.real Sᶜ) :=
        mul_le_mul_of_nonneg_left hSle hfac
    _ ≤ lam ^ (1 - 2 / (q : ℝ)) *
        ((∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) + B * delta) := by
        apply mul_le_mul_of_nonneg_left _ hfac
        linarith
    _ = lam ^ (1 - 2 / (q : ℝ)) *
          (∫ x, I x (t * lam ^ (2 / (q : ℝ))) ∂μ) +
        lam ^ (1 - 2 / (q : ℝ)) * (B * delta) := by ring

/-- **Finite-value comparison from the Palm identification.**  The Palm
identification (p is at most the retained-core Palm pressure) together with the
stationarity comparison (the dilated population pressure is at most the weighted
stationary value) gives the finite-value comparison with explicit reserve cost. -/
theorem finiteValueComparisonWithReserveCost_of_palmIdentification
    {q : ℕ} (hq : 2 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} {p : ℝ → ℝ} {C G : ℝ}
    (hC0 : 0 ≤ C) (hC1 : 1 ≤ C) (hG0 : 0 ≤ G)
    (μ : Measure X) [IsFiniteMeasure μ]
    (S : ℝ → Set X) (hS : ∀ rho, MeasurableSet (S rho))
    (I : X → ℝ → ℝ)
    (hIm : ∀ x u, |I x u| ≤ C + |u| * G)
    (hdelta : ∀ rho, 0 < rho → rho < 1 → μ.real ((S rho)ᶜ) ≤ rho)
    (hint : ∀ t rho, 0 < rho → rho < 1 →
      Integrable (fun x => I x (t * (1 - rho) ^ (2 / (q : ℝ)))) μ)
    (hpalm : ∀ t rho, 0 < rho → rho < 1 →
      p t ≤ ∫ x, (1 - rho) ^ (-(2 / (q : ℝ))) *
          I x (t * (1 - rho) ^ (2 / (q : ℝ)))
        ∂(μ.withDensity ((S rho).indicator (fun _ => ENNReal.ofReal (1 - rho)))))
    (hstat : ∀ t rho, 0 < rho → rho < 1 →
      (∫ x, I x (t * (1 - rho) ^ (2 / (q : ℝ))) ∂μ) ≤
        legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ)))) :
    FiniteValueComparisonWithReserveCost q α β kin g p C G := by
  intro t rho hrho0 hrho1
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hexp : 0 ≤ 2 / (q : ℝ) := by positivity
  have hlam0 : 0 < 1 - rho := by linarith
  have hlam1 : 1 - rho ≤ 1 := by linarith
  have hpow_le : (1 - rho) ^ (2 / (q : ℝ)) ≤ 1 :=
    Real.rpow_le_one hlam0.le hlam1 hexp
  have hBbound : ∀ x, |I x (t * (1 - rho) ^ (2 / (q : ℝ)))| ≤ C + |t| * G := by
    intro x
    have h1 := hIm x (t * (1 - rho) ^ (2 / (q : ℝ)))
    have h2 : |t * (1 - rho) ^ (2 / (q : ℝ))| ≤ |t| := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hlam0.le _)]
      nlinarith [abs_nonneg t]
    have h3 : |t * (1 - rho) ^ (2 / (q : ℝ))| * G ≤ |t| * G :=
      mul_le_mul_of_nonneg_right h2 hG0
    linarith
  have hBnn0 : 0 ≤ C + |t| * G := by
    have h1 : 0 ≤ |t| * G := mul_nonneg (abs_nonneg t) hG0
    linarith
  have hmain := retainedPressure_le_dilated_add_boundary (μ := μ) (S := S rho)
    (hS := hS rho) I t hlam0 hBnn0 hBbound (hint t rho hrho0 hrho1)
    (hpalm t rho hrho0 hrho1) (hdelta rho hrho0 hrho1)
  have hstat' := hstat t rho hrho0 hrho1
  have habs := boundaryLoss_le_reserveCost hq t rho C G (C + |t| * G) rho
    hrho0 hrho1 hC0 hC1 hG0 (le_refl _) hBnn0 (le_of_lt hrho0) (le_refl rho)
  have hfac : 0 ≤ (1 - rho) ^ (1 - 2 / (q : ℝ)) := Real.rpow_nonneg hlam0.le _
  have hstatmul := mul_le_mul_of_nonneg_left hstat' hfac
  linarith [hmain, hstatmul, habs]

/-- **Value identification I_w = I_2 from the Palm identification.**  The only
inputs beyond the imported weighted stationary comparison machinery are the Palm
identification (hpalm) and the stationarity comparison (hstat); the retained-core
dilation, the boundary-loss/reserve absorption and the finite-value comparison
are all proved. -/
theorem weightedInf_eq_secondMomentInf_of_palmIdentification
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
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (S : ℝ → Set X) (hS : ∀ rho, MeasurableSet (S rho))
    (Iloc : X → ℝ → ℝ)
    (hIloc : ∀ x u, |Iloc x u| ≤ C + |u| * G)
    (hdelta : ∀ rho, 0 < rho → rho < 1 → μ.real ((S rho)ᶜ) ≤ rho)
    (hint : ∀ t rho, 0 < rho → rho < 1 →
      Integrable (fun x => Iloc x (t * (1 - rho) ^ (2 / (qq : ℝ)))) μ)
    (hpalm : ∀ t rho, 0 < rho → rho < 1 →
      p t ≤ ∫ x, (1 - rho) ^ (-(2 / (qq : ℝ))) *
          Iloc x (t * (1 - rho) ^ (2 / (qq : ℝ)))
        ∂(μ.withDensity ((S rho).indicator (fun _ => ENNReal.ofReal (1 - rho)))))
    (hstat : ∀ t rho, 0 < rho → rho < 1 →
      (∫ x, Iloc x (t * (1 - rho) ^ (2 / (qq : ℝ))) ∂μ) ≤
        legalWeightedInf qq α β kin g (t * (1 - rho) ^ (2 / (qq : ℝ))))
    (t : ℝ)
    (hcont : ContinuousAt (fun s : ℝ => legalWeightedInf qq α β kin g s) t) :
    legalWeightedInf qq α β kin g t = legalSecondMomentInf qq α β kin g t :=
  weightedInf_eq_secondMomentInf_of_finiteValueComparisonCost Dbins hδ hIm pi α β
    hpi hI hgap hsep qq hqq hC hG hk hkn hkb hhom hg hgb hA hBs hα hβ hK matrix
    hmatrix hpos hlegal hactual hgc hp t hcont
    (finiteValueComparisonWithReserveCost_of_palmIdentification (q := qq)
      (by omega : 2 < qq) hC hC1 hG μ S hS Iloc hIloc hdelta hint hpalm hstat)

end OTSelector.Reconstruction
