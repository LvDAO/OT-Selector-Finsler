import OTSelector.Reconstruction.FinslerOriginalReserveCompletionStationary
import OTSelector.Reconstruction.FinslerOriginalCollarValueDensity
import OTSelector.Reconstruction.MarkedStationaryValueLegalCanonicalFirstInputScene
import OTSelector.Reconstruction.FinslerStationaryPalmReadouts

/-!
# Measurable stationary lifting of scene repairs and the finite-value comparison

This module closes the two named inputs of
FinslerOriginalReserveCompletionStationary as far as the structural and analytic
links allow.

1. **Measurable stationary lifting of scene repairs.**  A measurable scene map T
   which preserves the original colored input and commutes with every original
   reroot pushes any stationary law to a stationary law with exactly the same
   original input law (map_law_stationary, map_law_input_eq), and preserves the
   input Laplace readouts (map_law_input_laplace).  Consequently, once the Palm
   data of the pushed law are supplied (probability, original scalar marginals,
   finite kinetic and probe integrals), the pushed law is again a genuine
   weighted stationary matching of the same original independent input
   (exists_stationary_lifting_of_sceneMap), and its signed value is the integral
   of the repaired cost against that Palm (stationary_lifting_value).  This is
   the measurable stationary lifting used by the reserve construction; the Palm
   computation is the only remaining input, isolated as explicit hypotheses.

2. **The finite-value comparison with explicit reserve cost.**  The paper's
   comparison is packaged as FiniteValueComparisonWithReserveCost: at every tilt
   and every reserve density rho, the actual legal pressure limit is at most
   (1-rho)^(1-2/q) I_w(t(1-rho)^(2/q)) plus the explicit reserve cost
   C rho^(1-2/q) + C|t|G rho.  The normalized limit is proved from it
   (legalPressureLimit_le_weightedInf_of_reserveComparison), and combined with
   the value identification of FinslerOriginalReserveCompletionStationary it
   yields I_w = I_2 (weightedInf_eq_secondMomentInf_of_finiteValueComparisonCost).

## Remaining gap

The Palm data of the pushed law (probability, original scalar marginals, finite
kinetic and probe integrals) and the finite-value comparison itself remain named
inputs.  The finite scene completion, its reserve cost, the allocation of
retained edges, the measurable/stationary structure of the lifting and the
normalized limit are all proved.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
  CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction

open Module Manifold OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

local instance reserveLiftingPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace

local instance reserveLiftingInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace

/-! ## 1. Measurable stationary lifting of scene repairs -/

section StationaryLifting

variable {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
  {g : ℝ → ℝ → ℝ}

/-- The input Laplace readout depends only on the original colored input
component of the scene. -/
theorem legalMarkedInputSceneLaplace_apply (q : ℕ) (F : C_c(LegalColoredInputPoint q, ℝ))
    (hF : ∀ x, 0 ≤ F x) (s : LegalMarkedOptimalInputScene q) :
    legalMarkedInputSceneLaplace q F hF s =
      Real.exp (-LocalFiniteMeasure.testIntegral s.2 F) := rfl

/-- Pushing a stationary law along a measurable scene map which commutes with
every original reroot preserves stationarity. -/
theorem map_law_stationary
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (T : LegalMarkedOptimalInputScene q → LegalMarkedOptimalInputScene q)
    (hT : Measurable T)
    (hcomm : ∀ v : Fin q → ℝ,
      T ∘ legalMarkedInputSceneReroot q v = legalMarkedInputSceneReroot q v ∘ T) :
    ∀ v : Fin q → ℝ,
      MeasurePreserving (legalMarkedInputSceneReroot q v)
        ((M.law : Measure (LegalMarkedOptimalInputScene q)).map T)
        ((M.law : Measure (LegalMarkedOptimalInputScene q)).map T) := by
  intro v
  have hc : Measurable (legalMarkedInputSceneReroot q v) :=
    (continuous_legalMarkedInputSceneReroot q v).measurable
  refine ⟨hc, ?_⟩
  rw [Measure.map_map hc hT, ← hcomm v,
    ← Measure.map_map hT hc, (M.stationary v).map_eq]

/-- A scene map preserving the original colored input pushes the law to a law
with exactly the same original input law. -/
theorem map_law_input_eq
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (T : LegalMarkedOptimalInputScene q → LegalMarkedOptimalInputScene q)
    (hT : Measurable T) (hinput : ∀ s, (T s).2 = s.2) :
    ((M.law : Measure (LegalMarkedOptimalInputScene q)).map T).map Prod.snd =
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd := by
  rw [Measure.map_map measurable_snd hT]
  congr 1
  funext s
  exact hinput s

/-- The input Laplace readouts are preserved by any input-preserving scene map. -/
theorem map_law_input_laplace
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (T : LegalMarkedOptimalInputScene q → LegalMarkedOptimalInputScene q)
    (hT : Measurable T) (hinput : ∀ s, (T s).2 = s.2)
    (S : ℝ) (hS : 0 < S) (F : C_c(LegalColoredInputPoint q, ℝ))
    (hF : ∀ x, 0 ≤ F x)
    (hzero : ∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂((M.law : Measure (LegalMarkedOptimalInputScene q)).map T)) =
      ∫ b, legalInputBlockLaplace (fun x => F (x, 0)) (fun x => F (x, 1)) b
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  rw [integral_map hT.aemeasurable
    (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable]
  have hEq : (fun s => legalMarkedInputSceneLaplace q F hF (T s)) =
      fun s => legalMarkedInputSceneLaplace q F hF s := by
    funext s
    rw [legalMarkedInputSceneLaplace_apply, legalMarkedInputSceneLaplace_apply, hinput s]
  rw [hEq]
  exact M.input_laplace S hS F hF hzero

/-- **Measurable stationary lifting of a scene repair.**  If a measurable scene
map preserves the original colored input, commutes with every original reroot,
and produces a full legal forward matching almost surely, and if the Palm of the
pushed law is a probability with the original scalar marginals and finite
kinetic and probe integrals, then the pushed law is a genuine weighted
stationary matching of the same original input laws.  The Palm data are the only
inputs not mechanically produced by the scene map properties. -/
theorem exists_stationary_lifting_of_sceneMap
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (T : LegalMarkedOptimalInputScene q → LegalMarkedOptimalInputScene q)
    (hT : Measurable T) (hinput : ∀ s, (T s).2 = s.2)
    (hcomm : ∀ v : Fin q → ℝ,
      T ∘ legalMarkedInputSceneReroot q v = legalMarkedInputSceneReroot q v ∘ T)
    (hfull : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q (T s))
    (hforward : ∀ᵐ s ∂((M.law.map hT.aemeasurable :
        ProbabilityMeasure (LegalMarkedOptimalInputScene q)).toMeasure),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (hpalm : IsProbabilityMeasure
      (legalMarkedJointPalm q (M.law.map hT.aemeasurable)))
    (hsource : (legalMarkedJointPalm q (M.law.map hT.aemeasurable)).map
      (fun m => m.1.1) = α)
    (htarget : (legalMarkedJointPalm q (M.law.map hT.aemeasurable)).map
      (fun m => m.1.2) = β)
    (hkin : Integrable (fun m => kin m.1.1 m.1.2 m.2)
      (legalMarkedJointPalm q (M.law.map hT.aemeasurable)))
    (hprobe : Integrable (fun m => g m.1.1 m.1.2)
      (legalMarkedJointPalm q (M.law.map hT.aemeasurable))) :
    ∃ M' : LegalWeightedStationaryPoissonMatching q α β kin g,
      M'.law = M.law.map hT.aemeasurable ∧
      M'.value t = (∫ m, kin m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm q (M.law.map hT.aemeasurable)) +
        t * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q (M.law.map hT.aemeasurable) := by
  have hfull' : ∀ᵐ s ∂((M.law.map hT.aemeasurable :
      ProbabilityMeasure (LegalMarkedOptimalInputScene q)).toMeasure),
      IsFullOriginalInputMatching q s := by
    change ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)).map T,
      IsFullOriginalInputMatching q s
    exact (ae_map_iff hT.aemeasurable (measurableSet_isFullOriginalInputMatching q)).mpr hfull
  have hforward' : ∀ᵐ s ∂((M.law.map hT.aemeasurable :
      ProbabilityMeasure (LegalMarkedOptimalInputScene q)).toMeasure),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 :=
    hforward
  let M' : LegalWeightedStationaryPoissonMatching q α β kin g :=
    { law := M.law.map hT.aemeasurable
      stationary := map_law_stationary M T hT hcomm
      full_matching := hfull'
      forward := hforward'
      input_laplace := map_law_input_laplace M T hT hinput
      palm_probability := hpalm
      source_clock := hsource
      target_clock := htarget
      kinetic_integrable := hkin
      probe_integrable := hprobe }
  exact ⟨M', rfl, rfl⟩

/-- The signed value of a lifted matching is exactly the Palm integral of the
repaired cost.  This is the bridge from a.e.-scene cost bounds to stationary
value bounds. -/
theorem stationary_lifting_value
    (M' : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ) :
    M'.value t =
      (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q M'.law) +
        t * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q M'.law :=
  legal_value_eq_kinetic_add_tilt_mul_probe M' t

end StationaryLifting

/-! ## 2. The finite-value comparison with explicit reserve cost -/

section FiniteValueComparisonCost

/-- **The paper's finite-value comparison with explicit reserve cost.**  For every
tilt and every reserve density rho, the actual legal pressure limit is at most
the dilated weighted stationary value plus the explicit reserve cost
C rho^(1-2/q) + C|t|G rho. -/
def FiniteValueComparisonWithReserveCost (q : ℕ) (α β : Measure ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    (p : ℝ → ℝ) (C G : ℝ) : Prop :=
  ∀ (t rho : ℝ), 0 < rho → rho < 1 →
    p t ≤ (1 - rho) ^ (1 - 2 / (q : ℝ)) *
        legalWeightedInf q α β kin g (t * (1 - rho) ^ (2 / (q : ℝ))) +
      (C * rho ^ (1 - 2 / (q : ℝ)) + C * |t| * G * rho)

/-- The finite-value comparison with explicit reserve cost gives the legal
pressure along the weighted stationary value: p(t) <= I_w(t). -/
theorem legalPressureLimit_le_weightedInf_of_reserveComparison
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {p : ℝ → ℝ} {C G : ℝ} (hq : 4 < q)
    (hcont : ∀ t : ℝ, ContinuousAt (fun s : ℝ => legalWeightedInf q α β kin g s) t)
    (hcompare : FiniteValueComparisonWithReserveCost q α β kin g p C G)
    (t : ℝ) :
    p t ≤ legalWeightedInf q α β kin g t := by
  have hq2 : (2 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 2 < q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hexp : (0 : ℝ) < 1 - 2 / (q : ℝ) := by
    rw [sub_pos, div_lt_one hq0]
    linarith
  have ha : Tendsto (fun rho : ℝ => (1 - rho) ^ (1 - 2 / (q : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_one_sub_rpow _
  have hc : Tendsto (fun rho : ℝ => (1 - rho) ^ (2 / (q : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_one_sub_rpow _
  have hv : Tendsto (fun rho : ℝ => C * rho ^ (1 - 2 / (q : ℝ)) + C * |t| * G * rho)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hrho : Tendsto (fun rho : ℝ => rho) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun rho : ℝ => rho ^ (1 - 2 / (q : ℝ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (tendsto_rpow_neg_nhdsGT_zero (y := -(1 - 2 / (q : ℝ)))
        (by linarith)).inv_tendsto_atTop
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with rho hrho'
      change (rho ^ (-(1 - 2 / (q : ℝ))))⁻¹ = rho ^ (1 - 2 / (q : ℝ))
      rw [Real.rpow_neg hrho'.le]
      simp
    have h2 : Tendsto (fun rho : ℝ => C * rho ^ (1 - 2 / (q : ℝ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (h1.const_mul C)
    have h3 : Tendsto (fun rho : ℝ => C * |t| * G * rho) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (hrho.const_mul (C * |t| * G))
    simpa using h2.add h3
  exact le_of_tendsto_reserveNormalization (hcont t) ha hc hv
    (fun rho h1 h2 => hcompare t rho h1 h2)

/-- **The finite-value comparison with explicit reserve cost gives the value
identification I_w = I_2.**  The normalized limit p <= I_w is proved above, and
the legal pressure upper comparison of FinslerOriginalReserveCompletionStationary
then closes the value identification. -/
theorem weightedInf_eq_secondMomentInf_of_finiteValueComparisonCost
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
    (hcompare : FiniteValueComparisonWithReserveCost qq α β kin g p C G) :
    legalWeightedInf qq α β kin g t = legalSecondMomentInf qq α β kin g t :=
  weightedInf_eq_secondMomentInf_of_finiteValueComparison Dbins hδ hIm pi α β hpi
    hI hgap hsep qq hqq hC hG hk hkn hkb hhom hg hgb hA hB hα hβ hK matrix
    hmatrix hpos hlegal hactual hgc hp t hcont
    (fun rho h1 h2 => hcompare t rho h1 h2)

end FiniteValueComparisonCost

end OTSelector.Reconstruction
