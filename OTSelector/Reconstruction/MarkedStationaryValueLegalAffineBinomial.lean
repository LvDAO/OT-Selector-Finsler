import OTSelector.Reconstruction.MarkedStationaryValueLegalShapeBinomial
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineDensity

/-! Actual affine physical cost under the unchanged original binomial law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Original allowed endpoints supply the affine physical identity on the
actual count-law shape subcloud. Its unused iid tail changes no observation. -/
theorem ae_countLaw_unclampedBlockLegalTilted_affine_density
    (q : ℕ) (hq : 0 < q) (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (κ : Measure ℕ) [IsProbabilityMeasure κ] (S : Set (Fin q → ℝ))
    {r density side : ℝ} (hr : 0 ≤ r) (hd : 0 < density) (hside : 0 ≤ side)
    (origin : Fin q → ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (t : ℝ) :
    ∀ᵐ ω ∂twoMarkedCountLaw q α β κ,
      unclampedBlockLegalTilted q source target r kin probe t
        (mapBlockData (affineMarkedPoint origin side) (shapeCloud S ω.1))
        (mapBlockData (affineMarkedPoint origin side) (shapeCloud S ω.2)) =
      shapeLegalMarkedTilted q source target S (r * density * side ^ q)
        (fun a b v ↦ density ^ (-(2 / (q : ℝ))) * kin a b v) probe t ω := by
  have hac := twoMarkedCountLaw_absolutelyContinuous_poisson_one q α β κ
  filter_upwards [hac.ae_le (ae_points_mem_unitCube_twoMarkedCloudLaw q α β 1)] with ω hω
  apply unclampedBlockLegalTilted_affine_density q hq source target hr hd hside origin
    kin hhom probe t
  · intro i
    rw [shapeCloud_point]
    exact hω.1 (shapeCloudEmbedding S ω.1 i)
  · intro j
    rw [shapeCloud_point]
    exact hω.2 (shapeCloudEmbedding S ω.2 j)

/-- Actual affine physical shape means are compared with the full-cube
binomial means at the exact density-scaled cost, uniformly in the shape. -/
theorem FiniteScalarBins.integrable_density_affine_shapeBinomial_compare
    {clockSet : Set ℝ} {gap : ℝ} (D : FiniteScalarBins clockSet gap) (hgap : 0 < gap)
    (q : ℕ) (hq : 0 < q) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) (r density side : ℝ≥0) (hd : 0 < density) (origin : Fin q → ℝ)
    {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ clockSet)
    (hsep : ∀ᵐ ab ∂α.prod β, gap ≤ |target ab.2 - source ab.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun ab : A × B ↦ kin ab.1 ab.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    let intensity := (r : ℝ) * density * side ^ q
    let scaledKin := fun a b v ↦ (density : ℝ) ^ (-(2 / (q : ℝ))) * kin a b v
    let law := twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)
    let value := fun ω ↦ unclampedBlockLegalTilted q source target r kin g t
      (mapBlockData (affineMarkedPoint origin side) (shapeCloud S ω.1))
      (mapBlockData (affineMarkedPoint origin side) (shapeCloud S ω.2))
    Integrable value law ∧
    |(∫ ω, value ω ∂law) - (∫ ω, legalMarkedTilted q source target intensity scaledKin g t ω ∂law)| ≤
      (2 * ((N : ℝ) * (p : ℝ)) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          (intensity ^ (2 / (q : ℝ)) *
            (((density : ℝ) ^ (-(2 / (q : ℝ))) * C) * q) + |t| * G)) := by
  dsimp only
  let c := (density : ℝ) ^ (-(2 / (q : ℝ)))
  let scaledKin := fun a b v ↦ c * kin a b v
  have hc : 0 ≤ c := Real.rpow_nonneg density.coe_nonneg _
  have hm : Measurable (Function.uncurry (fun ab : A × B ↦ scaledKin ab.1 ab.2)) :=
    measurable_const.mul hk
  have hb : ∀ a b v, |scaledKin a b v| ≤ (c * C) * ∑ l, v l ^ 2 := by
    intro a b v
    change |c * kin a b v| ≤ _
    rw [abs_mul, abs_of_nonneg hc]
    calc
      _ ≤ c * (C * ∑ l, v l ^ 2) := mul_le_mul_of_nonneg_left (hkb a b v) hc
      _ = _ := by ring
  have hintensity : 0 ≤ (r : ℝ) * density * side ^ q := by positivity
  obtain ⟨hI, hbound⟩ := D.integral_shapeLegalMarkedTilted_binomial_sub_le hgap q hs ht α β N p
    hintensity hS hsource hsep (mul_nonneg hc hC) hG hm hb hg hgb t
  have heq := ae_countLaw_unclampedBlockLegalTilted_affine_density q hq source target α β
    (ProbabilityTheory.binomial N p) S r.coe_nonneg (by exact_mod_cast hd) side.coe_nonneg
    origin kin hhom g t
  refine ⟨hI.congr (Filter.EventuallyEq.symm heq), ?_⟩
  rw [integral_congr_ae heq]
  exact hbound

end OTSelector.Reconstruction
