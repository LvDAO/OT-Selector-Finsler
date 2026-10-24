import OTSelector.Reconstruction.FinslerOriginalWeightPopulationPressureUpper
import OTSelector.Reconstruction.FinslerOriginalClassPressureUnitDensity
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedPopulation

/-! The original full physical upper uses its canonical unit-density legal
pressures with the precise Haar mass factor and original rescaled probe tilt. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The pressure conclusion of one actual original weighted population:
one unit-density pressure for each literal finite class model and the original full iid assignment
upper, with its explicit physical geometry and once-counted residual errors. -/
def PopulationLocalPressureCore.originalWeightUnitDensityPressureData
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ) : Prop :=
    ∃ (N : Fin D.haar.continuous.count → ℕ)
      (refs : ∀ i, Fin (N i) → (D.haar.continuous.coefficient i).roots)
      (cells : ∀ i, Fin (N i) → Set (ℚ → M))
      (_hcells : ∀ i c, MeasurableSet (cells i c)),
      (∀ i c, cells i c ⊆ (D.haar.continuous.coefficient i).roots ∩ U i (refs i c)) ∧
      let Cell := Sigma (fun i ↦ Fin (N i))
      let coreIndex := fun c : Cell ↦ c.1
      let reference := fun c : Cell ↦ refs c.1 c.2
      let cell := fun c : Cell ↦ cells c.1 c.2
      let Qlocal := fun c : Cell ↦ Q c.1 (reference c)
      let P₀ := fun c : Cell ↦ D.originalWindowReferenceWeights γ originalGap I c.1 (reference c) (Qlocal c) retentionError
      let Seed := fun c : Cell ↦ (P (D.haar.continuous.coefficient c.1).seedIndex).seed
      let q := fun c ↦ Module.finrank ℝ (Seed c).covector.ker
      let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
      ∃ (hP₀ : ∀ c j k, 0 ≤ P₀ c j k) (hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k),
      ∃ (A : ℝ), 0 ≤ A ∧ ∃ cHaar : Cell → ℝ≥0, (∀ c, 0 < cHaar c) ∧
      (∀ c, (κ (D.haar.continuous.coefficient c.1).seedIndex).map
        (Module.finBasis ℝ (Seed c).covector.ker).equivFunL =
        (cHaar c : ℝ≥0∞) • (volume : Measure (Fin (q c) → ℝ))) ∧
      ∃ unitPressure : Cell → ℝ → ℝ,
        (∀ c,
          let C := D.haar.continuous.coefficient (coreIndex c)
          let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
          let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
          let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
          let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
          let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
          ∀ tilt, Tendsto (fun L : ℝ ↦ finiteClassLegalScalePressure (q c)
            (C.clockClassAllowed (Qlocal c)) α β
            (C.clockClassKinetic (Qlocal c) (reference c).val)
            (C.clockClassProbe (Qlocal c) (reference c).val (reference c).property f) L tilt)
            atTop (𝓝 (unitPressure c tilt))) ∧
        ∀ tilt : ℝ,
          let iid := fun n ↦ (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
          let assignment := fun n (sample : (Fin n → M) × (Fin n → M)) ↦ perturbedAssignmentValue
            (fun i j ↦ (n : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
              tilt * f (sample.1 i,sample.2 j)) 0 0
          let geometry := (3 * ε + 2 * ε ^ 2) *
              (A / (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + 1) +
            (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))
          let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
            (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
          (∀ n, 0 < n → Integrable (assignment n) (iid n)) ∧
          ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop,
            (∫ sample, assignment n sample ∂iid n) / n ≤
              (∑ c,
                let density : ℝ≥0 := cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
                volume.real ((coord c) '' cell c) * (density : ℝ) ^ (1 - 2 / (q c : ℝ)) *
                  unitPressure c (tilt * (density : ℝ) ^ (2 / (q c : ℝ)))) + geometry +
                (A * residual ^ (1 - 2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) +
                  2 * |tilt| * ‖f‖ * residual) + ζ

/-- The actual physical upper is canonically expressed by one original
unit-density pressure per frozen cell. Its effective retained density remains
inside the exact Haar weight and probe tilt; no replacement of the original
population experiment or conditional class law is made. -/
theorem PopulationLocalPressureCore.originalWeightLimitingPressureData_unit_density
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (hdata : D.originalWeightLimitingPressureData γ originalGap Q U retentionError splitError
      f ε probeError) :
    D.originalWeightUnitDensityPressureData γ originalGap Q U retentionError splitError
      f ε probeError := by
  classical
  rcases hdata with ⟨N,refs,cells,hcells,hsub,hP₀,hmass,A,hA,cHaar,hcHaar,hmap,limit,hlimit,hupper⟩
  let Cell := Sigma (fun i ↦ Fin (N i))
  let reference := fun c : Cell ↦ refs c.1 c.2
  let cell := fun c : Cell ↦ cells c.1 c.2
  let Qlocal := fun c : Cell ↦ Q c.1 (reference c)
  let P₀ := fun c : Cell ↦ D.originalWindowReferenceWeights γ originalGap I c.1
    (reference c) (Qlocal c) retentionError
  let Seed := fun c : Cell ↦ (P (D.haar.continuous.coefficient c.1).seedIndex).seed
  let q := fun c : Cell ↦ Module.finrank ℝ (Seed c).covector.ker
  let density := fun c : Cell ↦ cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
  have hq (c : Cell) : 4 < q c := by
    have h := D.original_seed_label_finrank c.1
    change q c = Module.finrank ℝ E - 1 at h
    omega
  have hzero (c : Cell) : ∀ j k,
      ¬(D.haar.continuous.coefficient c.1).clockClassAllowed (Qlocal c) j k →
        P₀ c j k = 0 := by
    intro j k hnot
    simp only [P₀, PopulationLocalPressureCore.originalWindowReferenceWeights, maskedClockFlow,
      hnot, ↓reduceIte]
  have hpressure (c : Cell) :=
    (D.haar.continuous.coefficient c.1).exists_clockClassPressure_unit_density
      (Qlocal c) (reference c).val (reference c).property f (P₀ c) (hP₀ c)
      (hzero c) (hmass c) (hq c)
  choose unitPressure hunit hphysical hconc hlip using hpressure
  have hdensity (c : Cell) : 0 < density c := by
    apply mul_pos (hcHaar c)
    apply ENNReal.toNNReal_pos
    · have hr : 0 < (clockClassPairMeasure (P₀ c)).real univ := by
        rw [clockClassPairMeasure_real_univ (P₀ c) (hP₀ c)]
        exact hmass c
      exact ne_of_gt ((ENNReal.toReal_pos_iff.mp hr).1)
    · exact measure_ne_top _ _
  have hident (c : Cell) (tilt : ℝ) :
      limit c tilt = (density c : ℝ) ^ (1 - 2 / (q c : ℝ)) *
        unitPressure c (tilt * (density c : ℝ) ^ (2 / (q c : ℝ))) := by
    apply tendsto_nhds_unique (hlimit c tilt)
    simpa only [ProbabilityMeasure.toMeasure_map, clockClassJointProbability,
      ProbabilityMeasure.coe_mk, density, P₀, Seed, q, Qlocal, reference] using
      hphysical c (density c) (hdensity c) tilt
  refine ⟨N,refs,cells,hcells,hsub,hP₀,hmass,A,hA,cHaar,hcHaar,hmap,unitPressure,?_,?_⟩
  · intro c
    simpa only [ProbabilityMeasure.toMeasure_map, clockClassJointProbability,
      ProbabilityMeasure.coe_mk, P₀, Seed, q, Qlocal, reference] using hunit c
  · intro tilt
    refine ⟨(hupper tilt).1,?_⟩
    intro ζ hζ
    filter_upwards [(hupper tilt).2 ζ hζ] with n hn
    simpa only [hident, density, P₀, Seed, q, Qlocal, reference, mul_assoc] using hn

end OTSelector.Reconstruction
