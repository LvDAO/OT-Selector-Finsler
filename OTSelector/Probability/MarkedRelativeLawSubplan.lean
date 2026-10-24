import OTSelector.Probability.MarkedRelativeLawMatching

/-!
# Law comparison charged to one original residual subplan

The common sampling on both colors comes from the marginals of the same
subplan of the original coupling. Its fixed original complement controls the
expected moved endpoint count. The matching comparison retains the exact
kinetic repair cost, without multiplying total variation by a kinetic bound.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableEq X] [MeasurableEq Y]

/-- The same original residual controls common sampling at every pair of
sample sizes, while all four one-point marginals are preserved exactly. -/
theorem exists_pairedCloud_sampling_of_original_subplan
    (π χ : Measure (X × Y)) [IsFiniteMeasure π]
    (μs νs : Measure X) [IsProbabilityMeasure μs] [IsProbabilityMeasure νs]
    (μt νt : Measure Y) [IsProbabilityMeasure μt] [IsProbabilityMeasure νt]
    (hπ : Vlasov.IsCoupling π μs μt) (hχ : χ ≤ π)
    (hχs : χ.map Prod.fst ≤ νs) (hχt : χ.map Prod.snd ≤ νt) :
    ∃ γs : Measure (X × X), ∃ γt : Measure (Y × Y),
      IsProbabilityMeasure γs ∧ IsProbabilityMeasure γt ∧
      γs.map Prod.fst = μs ∧ γs.map Prod.snd = νs ∧
      γt.map Prod.fst = μt ∧ γt.map Prod.snd = νt ∧
      γs {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
      γt {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
      ∀ m n : ℕ,
        ∫ z, (diffCount m z.1 + diffCount n z.2) ∂(pairedCloudLaw m n γs γt) ≤
          ((m : ℝ) + n) * (π - χ).real univ := by
  obtain ⟨γs, γt, hps, hpt, hs₀, hs₁, ht₀, ht₁, hbs, hbt⟩ :=
    Reconstruction.exists_common_sampling_of_original_subplan π χ μs νs μt νt
      hπ hχ hχs hχt
  have : IsProbabilityMeasure γs := hps
  have : IsProbabilityMeasure γt := hpt
  refine ⟨γs, γt, hps, hpt, hs₀, hs₁, ht₀, ht₁, hbs, hbt, ?_⟩
  intro m n
  rw [integral_pairedCloud_moved]
  have hrs : (γs {p | p.1 ≠ p.2}).toReal ≤ (π - χ).real univ :=
    ENNReal.toReal_mono (measure_ne_top _ _) hbs
  have hrt : (γt {p | p.1 ≠ p.2}).toReal ≤ (π - χ).real univ :=
    ENNReal.toReal_mono (measure_ne_top _ _) hbt
  calc (m : ℝ) * (γs {p | p.1 ≠ p.2}).toReal +
        (n : ℝ) * (γt {p | p.1 ≠ p.2}).toReal
      ≤ (m : ℝ) * (π - χ).real univ + (n : ℝ) * (π - χ).real univ := by gcongr
    _ = _ := by ring

/-- The mean matching comparison charged to the complement of the same
original subplan on both colors. The kinetic repair remains an exact integral. -/
theorem integral_sampledTiltedValue_le_relative_of_original_residual
    {m n : ℕ} (π χ : Measure (X × Y)) [IsFiniteMeasure π]
    (γs : Measure (X × X)) (γt : Measure (Y × Y))
    [IsProbabilityMeasure γs] [IsProbabilityMeasure γt]
    (μs νs : Measure X) (μt νt : Measure Y)
    (hs₀ : γs.map Prod.fst = μs) (hs₁ : γs.map Prod.snd = νs)
    (ht₀ : γt.map Prod.fst = μt) (ht₁ : γt.map Prod.snd = νt)
    (hbs : γs {p | p.1 ≠ p.2} ≤ (π - χ) univ)
    (hbt : γt {p | p.1 ≠ p.2} ≤ (π - χ) univ)
    (c c' g : X → Y → ℝ) (t : ℝ)
    (R : ((Fin m → X × X) × (Fin n → Y × Y)) → ℝ)
    {ρ G : ℝ} (hρ : 0 ≤ ρ) (hG : 0 ≤ G)
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
    (hrepair : ∀ᵐ z ∂(pairedCloudLaw m n γs γt),
      HasCommonSampleRepair c c' g t (coordProj m true z.1) (coordProj m false z.1)
        (coordProj n true z.2) (coordProj n false z.2) (R z)) :
    ∫ z, sampledTiltedValue c' g t z ∂((Measure.pi fun _ : Fin m ↦ μs).prod
        (Measure.pi fun _ : Fin n ↦ μt)) ≤
      (1 + ρ) * (∫ z, sampledTiltedValue c g t z ∂((Measure.pi fun _ : Fin m ↦ νs).prod
        (Measure.pi fun _ : Fin n ↦ νt))) + ρ * |t| * G * (min m n : ℝ) +
        (∫ z, R z ∂(pairedCloudLaw m n γs γt)) +
        2 * |t| * G * ((m : ℝ) + n) * (π - χ).real univ := by
  have hδ : 0 ≤ (π - χ).real univ := measureReal_nonneg
  have hs : γs {p | p.1 ≠ p.2} ≤ ENNReal.ofReal ((π - χ).real univ) := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hbs
  have ht : γt {p | p.1 ≠ p.2} ≤ ENNReal.ofReal ((π - χ).real univ) := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hbt
  have h := integral_sampledTiltedValue_le_relative_of_repair γs γt μs νs μt νt
    hs₀ hs₁ ht₀ ht₁ c c' g t R hρ hG hδ hδ hc hg hrel hcmeas hc'meas hgmeas
    hF hF' hR hs ht hrepair
  convert h using 1
  ring

omit [MeasurableEq X] [MeasurableEq Y] in
/-- Normalizing by the common sample size leaves an `O(ε)` probe error from
the freezing residual. There is no sample-size dependent kinetic constant. -/
theorem normalized_original_residual_probe_error_le
    (π χ : Measure (X × Y)) [IsFiniteMeasure π]
    {ε K : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (hK : 0 ≤ K)
    (hres : (π - χ) univ ≤ ENNReal.ofReal (6 * ε / (1 - ε)))
    (n : ℕ) (hn : 0 < n) :
    (2 * K * ((n : ℝ) + n) * (π - χ).real univ) / n ≤
      24 * K * ε / (1 - ε) := by
  have hδ : 0 ≤ 6 * ε / (1 - ε) := by positivity
  have hr : (π - χ).real univ ≤ 6 * ε / (1 - ε) := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hres
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc (2 * K * ((n : ℝ) + n) * (π - χ).real univ) / n
      = 4 * K * (π - χ).real univ := by field_simp; ring
    _ ≤ 4 * K * (6 * ε / (1 - ε)) := by gcongr
    _ = _ := by ring

/-- Freezing both finite color laws produces one retained original subplan
and exact iid common samplings whose expected moved count is `O(ε(m+n))`.
No uniform density or exact product law for the actual population is assumed. -/
theorem exists_normalized_freezing_pairedCloud_sampling
    (μ₀ μ₁ : Measure X) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ₁]
    (ν₀ ν₁ : Measure Y) [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁]
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (D₀ : Reconstruction.FiniteLawFreezingBound μ₀ μ₁ ε)
    (D₁ : Reconstruction.FiniteLawFreezingBound ν₀ ν₁ ε)
    (hμ₁ : 0 < μ₁.real univ) (hν₁ : 0 < ν₁.real univ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π (Reconstruction.normalizedFiniteLaw μ₀)
      (Reconstruction.normalizedFiniteLaw ν₀)) :
    ∃ χ : Measure (X × Y), χ ≤ π ∧
      χ.map Prod.fst ≤ Reconstruction.normalizedFiniteLaw μ₁ ∧
      χ.map Prod.snd ≤ Reconstruction.normalizedFiniteLaw ν₁ ∧
      (π - χ) univ ≤ ENNReal.ofReal (6 * ε / (1 - ε)) ∧
      ∃ γs : Measure (X × X), ∃ γt : Measure (Y × Y),
        IsProbabilityMeasure γs ∧ IsProbabilityMeasure γt ∧
        γs.map Prod.fst = Reconstruction.normalizedFiniteLaw μ₀ ∧
        γs.map Prod.snd = Reconstruction.normalizedFiniteLaw μ₁ ∧
        γt.map Prod.fst = Reconstruction.normalizedFiniteLaw ν₀ ∧
        γt.map Prod.snd = Reconstruction.normalizedFiniteLaw ν₁ ∧
        γs {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
        γt {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
        ∀ m n : ℕ,
          ∫ z, (diffCount m z.1 + diffCount n z.2) ∂(pairedCloudLaw m n γs γt) ≤
            ((m : ℝ) + n) * (6 * ε / (1 - ε)) := by
  obtain ⟨χ, hχ, hχs, hχt, hres, γs, γt, hps, hpt, hs₀, hs₁, ht₀, ht₁, hbs, hbt⟩ :=
    Reconstruction.exists_normalized_freezing_subplan_sampling μ₀ μ₁ ν₀ ν₁
      hε hε1 D₀ D₁ hμ₁ hν₁ π hπ
  have : IsProbabilityMeasure γs := hps
  have : IsProbabilityMeasure γt := hpt
  refine ⟨χ, hχ, hχs, hχt, hres, γs, γt, hps, hpt, hs₀, hs₁, ht₀, ht₁, hbs, hbt, ?_⟩
  intro m n
  rw [integral_pairedCloud_moved]
  have hδ : 0 ≤ 6 * ε / (1 - ε) := by positivity
  have hrs : (γs {p | p.1 ≠ p.2}).toReal ≤ 6 * ε / (1 - ε) := by
    simpa only [ENNReal.toReal_ofReal hδ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbs.trans hres)
  have hrt : (γt {p | p.1 ≠ p.2}).toReal ≤ 6 * ε / (1 - ε) := by
    simpa only [ENNReal.toReal_ofReal hδ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbt.trans hres)
  calc (m : ℝ) * (γs {p | p.1 ≠ p.2}).toReal +
        (n : ℝ) * (γt {p | p.1 ≠ p.2}).toReal
      ≤ (m : ℝ) * (6 * ε / (1 - ε)) + (n : ℝ) * (6 * ε / (1 - ε)) := by gcongr
    _ = _ := by ring

end OTSelector.Probability
