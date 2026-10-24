import OTSelector.Finite.CommonSampleMatchingCore
import OTSelector.Probability.MarkedRelativeLawCoupling
import OTSelector.Finite.MaxCardValueMeasurable

/-!
# Matching-law comparison from actual repair witnesses

The law-transfer bound is instantiated for the maximum-cardinality tilted
value. Its remaining input is a finite repaired matching extending the edges
of the model optimum whose endpoints agree under common sampling. This input
is a concrete matching construction and an exact kinetic repair-cost bound.
-/

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} {m n : ℕ}

/-- The tilted maximum-cardinality value on a fixed pair of sample arrays. -/
def sampledTiltedValue (c g : X → Y → ℝ) (t : ℝ)
    (z : (Fin m → X) × (Fin n → Y)) : ℝ :=
  PartialMatching.maxCardValue fun i j ↦ c (z.1 i) (z.2 j) + t * g (z.1 i) (z.2 j)

/-- A model optimum and an actual maximum-cardinality repair preserve every
edge whose two sampled endpoints agree. The kinetic cost of the added edges
is bounded by `R`; no pointwise bound on the full kinetic kernel is required. -/
def HasCommonSampleRepair (c c' g : X → Y → ℝ) (t : ℝ)
    (x x' : Fin m → X) (y y' : Fin n → Y) (R : ℝ) : Prop :=
  ∃ σ τ : PartialMatching m n,
    σ.card = min m n ∧
    σ.cost (fun i j ↦ c (x' i) (y' j) + t * g (x' i) (y' j)) =
      sampledTiltedValue c g t (x', y') ∧
    τ.card = min m n ∧
    PartialMatching.commonSampleCore σ x x' y y' ⊆ τ.edges ∧
    (∑ e ∈ τ.edges \ PartialMatching.commonSampleCore σ x x' y y',
      c' (x e.1) (y e.2)) ≤ R

/-- The finite value comparison from a concrete shared-core repair. -/
theorem sampledTiltedValue_le_relative_of_common_repair
    (c c' g : X → Y → ℝ) (t : ℝ) {ρ G : ℝ}
    (hρ : 0 ≤ ρ) (hG : 0 ≤ G)
    (hc : ∀ x y, 0 ≤ c x y) (hg : ∀ x y, |g x y| ≤ G)
    (hrel : ∀ x y, c' x y ≤ (1 + ρ) * c x y)
    (x x' : Fin m → X) (y y' : Fin n → Y) {R : ℝ}
    (hrepair : HasCommonSampleRepair c c' g t x x' y y' R) :
    sampledTiltedValue c' g t (x, y) ≤
      (1 + ρ) * sampledTiltedValue c g t (x', y') +
        ρ * |t| * G * (min m n : ℝ) + R +
        2 * |t| * G * (pairDiffCount m x x' + pairDiffCount n y y') := by
  classical
  obtain ⟨σ, τ, hσ, hσopt, hτ, hcore, hR⟩ := hrepair
  have hmain := PartialMatching.maxCardValue_le_relative_common_core_add_repair
    (c := fun i j ↦ c (x' i) (y' j)) (c' := fun i j ↦ c' (x i) (y j))
    (g := fun i j ↦ g (x' i) (y' j)) (g' := fun i j ↦ g (x i) (y j))
    (t := t) hρ hG (fun i j ↦ hc _ _) (fun i j ↦ hg _ _) (fun i j ↦ hg _ _)
    σ τ hσ hσopt hτ (PartialMatching.commonSampleCore σ x x' y y')
    (PartialMatching.commonSampleCore_subset σ x x' y y') hcore ?_ ?_
  · have hmissing : ((min m n -
        (PartialMatching.commonSampleCore σ x x' y y').card : ℕ) : ℝ) ≤
        pairDiffCount m x x' + pairDiffCount n y y' := by
      simpa only [pairDiffCount, Nat.cast_add] using
        (Nat.cast_le (α := ℝ)).mpr
          (PartialMatching.missing_commonSampleCore_le σ hσ x x' y y')
    exact hmain.trans (by
      dsimp only [sampledTiltedValue]
      gcongr)
  · intro e he
    obtain ⟨hx, hy⟩ := (Finset.mem_filter.mp he).2
    simpa only [hx, hy] using hrel (x e.1) (y e.2)
  · intro e he
    obtain ⟨hx, hy⟩ := (Finset.mem_filter.mp he).2
    rw [hx, hy]

variable [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableEq X] [MeasurableEq Y]

omit [MeasurableEq X] [MeasurableEq Y] in
/-- Measurability uses only measurable kinetic and probe kernels. -/
theorem measurable_sampledTiltedValue (c g : X → Y → ℝ) (t : ℝ)
    (hc : Measurable fun p : X × Y ↦ c p.1 p.2)
    (hg : Measurable fun p : X × Y ↦ g p.1 p.2) :
    Measurable (sampledTiltedValue (m := m) (n := n) c g t) := by
  apply PartialMatching.measurable_maxCardValue
  intro i j
  have hxy : Measurable fun z : (Fin m → X) × (Fin n → Y) ↦ (z.1 i, z.2 j) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)
  exact (hc.comp hxy).add ((hg.comp hxy).const_mul t)

/-- Actual iid cloud costs are bounded by the frozen iid model costs plus the
exact mean kinetic repair and a probe error linear in the disagreement laws. -/
theorem integral_sampledTiltedValue_le_relative_of_repair
    (γs : Measure (X × X)) (γt : Measure (Y × Y))
    [IsProbabilityMeasure γs] [IsProbabilityMeasure γt]
    (μs νs : Measure X) (μt νt : Measure Y)
    (hs₀ : γs.map Prod.fst = μs) (hs₁ : γs.map Prod.snd = νs)
    (ht₀ : γt.map Prod.fst = μt) (ht₁ : γt.map Prod.snd = νt)
    (c c' g : X → Y → ℝ) (t : ℝ)
    (R : ((Fin m → X × X) × (Fin n → Y × Y)) → ℝ)
    {ρ G δs δt : ℝ} (hρ : 0 ≤ ρ) (hG : 0 ≤ G) (hδs : 0 ≤ δs) (hδt : 0 ≤ δt)
    (hc : ∀ x y, 0 ≤ c x y) (hg : ∀ x y, |g x y| ≤ G)
    (hrel : ∀ x y, c' x y ≤ (1 + ρ) * c x y)
    (hcmeas : Measurable fun p : X × Y ↦ c p.1 p.2)
    (hc'meas : Measurable fun p : X × Y ↦ c' p.1 p.2)
    (hgmeas : Measurable fun p : X × Y ↦ g p.1 p.2)
    (hF : Integrable (sampledTiltedValue c' g t)
      ((Measure.pi fun _ : Fin m ↦ μs).prod (Measure.pi fun _ : Fin n ↦ μt)))
    (hF' : Integrable (sampledTiltedValue c g t)
      ((Measure.pi fun _ : Fin m ↦ νs).prod (Measure.pi fun _ : Fin n ↦ νt)))
    (hR : Integrable R (pairedCloudLaw m n γs γt))
    (hbs : γs {p | p.1 ≠ p.2} ≤ ENNReal.ofReal δs)
    (hbt : γt {p | p.1 ≠ p.2} ≤ ENNReal.ofReal δt)
    (hrepair : ∀ᵐ z ∂(pairedCloudLaw m n γs γt),
      HasCommonSampleRepair c c' g t (coordProj m true z.1) (coordProj m false z.1)
        (coordProj n true z.2) (coordProj n false z.2) (R z)) :
    ∫ z, sampledTiltedValue c' g t z ∂((Measure.pi fun _ : Fin m ↦ μs).prod
        (Measure.pi fun _ : Fin n ↦ μt)) ≤
      (1 + ρ) * (∫ z, sampledTiltedValue c g t z ∂((Measure.pi fun _ : Fin m ↦ νs).prod
        (Measure.pi fun _ : Fin n ↦ νt))) + ρ * |t| * G * (min m n : ℝ) +
        (∫ z, R z ∂(pairedCloudLaw m n γs γt)) +
        2 * |t| * G * ((m : ℝ) * δs + (n : ℝ) * δt) := by
  have hpoint : ∀ᵐ z ∂(pairedCloudLaw m n γs γt),
      sampledTiltedValue c' g t (pairedCloudProj m n true z) ≤
        (1 + ρ) * sampledTiltedValue c g t (pairedCloudProj m n false z) +
          ρ * (|t| * G) * (min m n : ℝ) + R z +
            2 * (|t| * G) * (diffCount m z.1 + diffCount n z.2) := by
    filter_upwards [hrepair] with z hz
    have h := sampledTiltedValue_le_relative_of_common_repair c c' g t hρ hG hc hg hrel
      (coordProj m true z.1) (coordProj m false z.1)
      (coordProj n true z.2) (coordProj n false z.2) hz
    have hcs : pairDiffCount m (coordProj m true z.1) (coordProj m false z.1) =
        diffCount m z.1 := by
      unfold pairDiffCount diffCount
      congr 1
    have hct : pairDiffCount n (coordProj n true z.2) (coordProj n false z.2) =
        diffCount n z.2 := by
      unfold pairDiffCount diffCount
      congr 1
    rw [hcs, hct] at h
    simpa only [pairedCloudProj, mul_assoc] using h
  have h := integral_le_relative_of_pairedCloud_repair m n γs γt μs νs μt νt
    hs₀ hs₁ ht₀ ht₁ (sampledTiltedValue c' g t) (sampledTiltedValue c g t) R
    (mul_nonneg (abs_nonneg t) hG) hδs hδt
    (measurable_sampledTiltedValue c' g t hc'meas hgmeas)
    (measurable_sampledTiltedValue c g t hcmeas hgmeas) hF hF' hR hbs hbt hpoint
  simpa only [mul_assoc] using h

end OTSelector.Probability
