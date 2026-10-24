import OTSelector.Reconstruction.FinslerRelativeLawClassCubePhysicalBinomial

/-! Exact density cancellation between true affine binomial means and finite class count models. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The original true affine full-cube mean is exactly the density-scaled legal
count model. Its count probability is unchanged and need not equal a proposed
geometric volume at the finitely many initial sample sizes. -/
theorem affineBinomialCubeExpectation_eq_density_count_model (q : ℕ) (hq : 0 < q)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {density side : ℝ} (hdensity : 0 < density) (hside : 0 ≤ side)
    (origin : Fin q → ℝ) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    affineBinomialCubeExpectation source target α β N p side origin kin probe t =
      ∫ cloud, legalMarkedTilted q source target ((N : ℝ) * density * side ^ q)
        (fun a b v ↦ density ^ (-(2 / (q : ℝ))) * kin a b v) probe t cloud
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p) := by
  have hfinite := affineBinomialBlock_integrable_integral q hq hs ht α β N p hside origin
    hC hG hk hkb hhom hp hpb t
  have hcancel : ((N : ℝ) * density * side ^ q) ^ (2 / (q : ℝ)) *
      density ^ (-(2 / (q : ℝ))) = (N : ℝ) ^ (2 / (q : ℝ)) * side ^ 2 := by
    rw [show (N : ℝ) * density * side ^ q = ((N : ℝ) * side ^ q) * density by ring,
      rpow_positive_density_cancel (mul_nonneg (Nat.cast_nonneg N) (pow_nonneg hside q)) hdensity,
      rpow_affine_intensity q hq (Nat.cast_nonneg N) hside]
  have hpoint (cloud : TwoMarkedCloudSpace q A B) :
      legalMarkedTilted q source target 1
        (fun a b v ↦ ((N : ℝ) ^ (2 / (q : ℝ)) * side ^ 2) * kin a b v) probe t cloud =
      legalMarkedTilted q source target ((N : ℝ) * density * side ^ q)
        (fun a b v ↦ density ^ (-(2 / (q : ℝ))) * kin a b v) probe t cloud := by
    apply PartialMatching.legalMaximumValue_congr_on_allowed
    intro i j _
    simp only [mKineticCost, Real.one_rpow, one_mul]
    rw [← mul_assoc, hcancel]
  exact hfinite.2.trans (integral_congr_ae (.of_forall hpoint))

end OTSelector.Reconstruction
