import OTSelector.Reconstruction.FinslerOriginalPressureDensityScale
import OTSelector.Finite.MaxCardValueScaling

/-! Exact kinetic scaling preserves the actual legal maximum-cardinality
class, original Poisson input law, original marks and physical density. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
namespace PartialMatching

/-- Multiplication by a nonnegative scalar preserves the literal legal
maximum-cardinality minimization, including signed costs and empty graphs. -/
theorem legalMaximumValue_const_mul {m n : ℕ}
    (allowed : Finset (Fin m × Fin n)) (cost : Fin m → Fin n → ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    legalMaximumValue allowed (fun i j ↦ c * cost i j) =
      c * legalMaximumValue allowed cost := by
  obtain ⟨σ,hσ,hcardσ,hcostσ⟩ := exists_cost_eq_legalMaximumValue allowed cost
  obtain ⟨τ,hτ,hcardτ,hcostτ⟩ :=
    exists_cost_eq_legalMaximumValue allowed (fun i j ↦ c * cost i j)
  apply le_antisymm
  · calc
      _ ≤ σ.cost (fun i j ↦ c * cost i j) := legalMaximumValue_le _ hσ hcardσ
      _ = _ := by rw [OTSelector.PartialMatching.cost_const_mul,hcostσ]
  · have h := mul_le_mul_of_nonneg_left (legalMaximumValue_le cost hτ hcardτ) hc
    simpa only [← OTSelector.PartialMatching.cost_const_mul,hcostτ] using h

end PartialMatching
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Scaling the kinetic coefficient by a positive factor scales the actual
signed legal matching value and inversely rescales its original probe tilt. -/
theorem finiteClassLegalTilted_kinetic_scale
    (q : ℕ) (allowed : A → B → Prop) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    {c : ℝ} (hc : 0 < c) (t : ℝ) (ω : TwoMarkedCloudSpace q A B) :
    finiteClassLegalTilted q allowed r (fun a b v ↦ c * kin a b v) probe t ω =
      c * finiteClassLegalTilted q allowed r kin probe (t / c) ω := by
  have hedge (i : Fin (mSourceCount ω)) (j : Fin (mTargetCount ω)) :
      mKineticCost q r (fun a b v ↦ c * kin a b v) ω i j + t * mProbe probe ω i j =
        c * (mKineticCost q r kin ω i j + (t / c) * mProbe probe ω i j) := by
    dsimp only [mKineticCost]
    field_simp
  simp only [finiteClassLegalTilted,hedge]
  exact PartialMatching.legalMaximumValue_const_mul _ _ hc.le

/-- The same exact scaling identity after expectation against the unchanged
original independent Poisson cloud law. -/
theorem finiteClassLegalPressure_kinetic_scale
    (q : ℕ) (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    finiteClassLegalPressure q allowed α β r (fun a b v ↦ c * kin a b v) probe t =
      c * finiteClassLegalPressure q allowed α β r kin probe (t / c) := by
  simp only [finiteClassLegalPressure,finiteClassLegalTilted_kinetic_scale q allowed r kin probe hc]
  exact integral_const_mul _ _

/-- Real spatial-scale normalization preserves exactly the same kinetic and
probe scaling, including nonpositive side lengths by the original definition. -/
theorem finiteClassLegalScalePressure_kinetic_scale
    (q : ℕ) (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    {c : ℝ} (hc : 0 < c) (R t : ℝ) :
    finiteClassLegalScalePressure q allowed α β (fun a b v ↦ c * kin a b v) probe R t =
      c * finiteClassLegalScalePressure q allowed α β kin probe R (t / c) := by
  by_cases hR : 0 < R
  · simp only [finiteClassLegalScalePressure,hR,↓reduceIte,
      finiteClassLegalPressure_kinetic_scale q allowed α β _ kin probe hc]
    ring
  · simp only [finiteClassLegalScalePressure,hR,↓reduceIte,mul_zero]

/-- Positive physical density contributes one mass factor and the inverse
quadratic kinetic factor. The combined factor is the Haar power `1-2/q`. -/
theorem physical_density_pressure_weight {density q : ℝ} (hdensity : 0 < density)
    (p : ℝ → ℝ) (t : ℝ) :
    density * (density ^ (-2 / q) * p (t / density ^ (-2 / q))) =
      density ^ (1 - 2 / q) * p (t * density ^ (2 / q)) := by
  have hinv : (density ^ (-2 / q))⁻¹ = density ^ (2 / q) := by
    rw [← Real.rpow_neg hdensity.le]
    congr 1
    ring
  have hmass : density * density ^ (-2 / q) = density ^ (1 - 2 / q) := by
    calc
      _ = density ^ (1 : ℝ) * density ^ (-2 / q) := by rw [Real.rpow_one]
      _ = density ^ ((1 : ℝ) + -2 / q) := (Real.rpow_add hdensity _ _).symm
      _ = _ := by congr 1; ring
  have htilt : t / density ^ (-2 / q) = t * density ^ (2 / q) := by
    change t * (density ^ (-2 / q))⁻¹ = _
    rw [hinv]
  rw [htilt,← mul_assoc,hmass]

/-- A unit-density pressure limit determines the physical-density limit
canonically. The original intensity is `density * L^q`, and the original
kinetic coefficient is scaled by `density^(-2/q)`; the output is precisely the
Haar-weighted expression `density^(1-2/q) p(t density^(2/q))`. -/
theorem tendsto_finiteClassLegalPressure_physical_density
    (q : ℕ) (hq : 0 < q) (allowed : A → B → Prop)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ)
    (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun r : ℝ ↦
      finiteClassLegalPressure q allowed α β (Real.toNNReal r) kin probe t / r)
      atTop (𝓝 (p t)))
    (density : ℝ≥0) (hdensity : 0 < density) (t : ℝ) :
    Tendsto (fun L : ℝ ↦ finiteClassLegalPressure q allowed α β
        (density * Real.toNNReal (L ^ q))
        (fun a b v ↦ (density : ℝ) ^ (-2 / (q : ℝ)) * kin a b v) probe t / L ^ q)
      atTop (𝓝 ((density : ℝ) ^ (1 - 2 / (q : ℝ)) *
        p (t * (density : ℝ) ^ (2 / (q : ℝ))))) := by
  have hd : (0 : ℝ) < density := by exact_mod_cast hdensity
  have hc : 0 < (density : ℝ) ^ (-2 / (q : ℝ)) := Real.rpow_pos_of_pos hd _
  have hbase := (hp (t / (density : ℝ) ^ (-2 / (q : ℝ)))).const_mul
    ((density : ℝ) ^ (-2 / (q : ℝ)))
  have hscaled : Tendsto (fun r : ℝ ↦
      finiteClassLegalPressure q allowed α β (Real.toNNReal r)
        (fun a b v ↦ (density : ℝ) ^ (-2 / (q : ℝ)) * kin a b v) probe t / r)
      atTop (𝓝 ((density : ℝ) ^ (-2 / (q : ℝ)) *
        p (t / (density : ℝ) ^ (-2 / (q : ℝ))))) := by
    convert hbase using 1
    funext r
    rw [finiteClassLegalPressure_kinetic_scale q allowed α β _ kin probe hc]
    ring
  have h := tendsto_pressure_density_scaled_side hq hdensity
    (pressure := fun r : ℝ≥0 ↦ finiteClassLegalPressure q allowed α β r
      (fun a b v ↦ (density : ℝ) ^ (-2 / (q : ℝ)) * kin a b v) probe t) hscaled
  rwa [physical_density_pressure_weight hd p t] at h

end OTSelector.Reconstruction
