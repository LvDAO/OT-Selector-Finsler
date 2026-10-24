import OTSelector.Reconstruction.FinslerOriginalDensityResidueRate
import OTSelector.Reconstruction.FinslerOriginalShellBandMass
import OTSelector.Reconstruction.OriginalFinslerKernelLeftDoublePole
import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole

/-! Both immutable original colors share the same actual focal residue and a
common collar and band-mass constant. No colorwise mass balancing is assumed. -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν σ : Measure ℝ}

/-- Both original colors obey the left shell-width rate for one internally
produced original residue, on a common collar with one finite constant. -/
theorem OriginalSeedConditionalMoments.exists_original_left_twoColor_shell_band_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (σ : Fin 2 → Measure ℝ) (ρ : Fin 2 → M → ℝ) {v : M → E → ℝ}
    (c : Fin 2 → ℝ≥0∞)
    (hρ : ∀ i, Continuous (ρ i)) (hρ0 : ∀ i x, 0 ≤ ρ i x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : ∀ i, PopulationSeedClockDensity S w
      ((σ i).map (fun x : ℝ ↦ x - S.level)) (ρ i) v (c i).toReal) :
    ∃ η : ℝ, 0 < η ∧ η < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
        ∀ (i : Fin 2) {t a b s : ℝ}, 0 < t → 0 ≤ s → 2 * t < ε →
          D.lo + t ≤ a → b ≤ D.lo + 2 * t → b - a ≤ s →
          ((σ i).map (fun x : ℝ ↦ x - S.level)) (Ioc a b) ≤
            ENNReal.ofReal (C * t ^ G.rank * s) := by
  obtain ⟨η, hη, hηh, G, Rem, hRem, hpole⟩ := D.exists_original_kernel_left_double_pole hF hw
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hη, hη⟩)
  have heach (i : Fin 2) := D.exists_original_left_shell_band_mass_bound
    hF hw (c i) (hρ i) (hρ0 i) hv hv0 (hdensity i) hη hRem0 hpole
  choose ε C hε hεh hC hband using heach
  have hεmin (i : Fin 2) : min (ε 0) (ε 1) ≤ ε i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hCmax (i : Fin 2) : C i ≤ max (C 0) (C 1) := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨η, hη, hηh, G, Rem, hRem, hpole, min (ε 0) (ε 1), max (C 0) (C 1),
    lt_min (hε 0) (hε 1), (min_le_left _ _).trans_lt (hεh 0),
    (hC 0).trans_le (le_max_left _ _), ?_⟩
  intro i t a b s ht hs h2t ha hb hwidth
  calc
    _ ≤ ENNReal.ofReal (C i * t ^ G.rank * s) :=
      hband i ht (h2t.trans_le (hεmin i)) ha hb hwidth
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCmax i) (pow_nonneg ht.le _)) hs

/-- Both original colors obey the right shell-width rate for one internally
produced original residue, on a common collar with one finite constant. -/
theorem OriginalSeedConditionalMoments.exists_original_right_twoColor_shell_band_bound
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (σ : Fin 2 → Measure ℝ) (ρ : Fin 2 → M → ℝ) {v : M → E → ℝ}
    (c : Fin 2 → ℝ≥0∞)
    (hρ : ∀ i, Continuous (ρ i)) (hρ0 : ∀ i x, 0 ≤ ρ i x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hdensity : ∀ i, PopulationSeedClockDensity S w
      ((σ i).map (fun x : ℝ ↦ x - S.level)) (ρ i) v (c i).toReal) :
    ∃ η : ℝ, 0 < η ∧ η < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      ContDiffOn ℝ ∞ Rem (Ioo (-η) η) ∧
      (∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ ε C : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧ 0 < C ∧
        ∀ (i : Fin 2) {t a b s : ℝ}, 0 < t → 0 ≤ s → 2 * t < ε →
          D.hi - 2 * t ≤ a → b ≤ D.hi - t → b - a ≤ s →
          ((σ i).map (fun x : ℝ ↦ x - S.level)) (Ioc a b) ≤
            ENNReal.ofReal (C * t ^ G.rank * s) := by
  obtain ⟨η, hη, hηh, G, Rem, hRem, hpole⟩ := D.exists_original_kernel_right_double_pole hF hw
  have hRem0 : ContinuousAt Rem 0 := hRem.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hη, hη⟩)
  have heach (i : Fin 2) := D.exists_original_right_shell_band_mass_bound
    hF hw (c i) (hρ i) (hρ0 i) hv hv0 (hdensity i) hη hRem0 hpole
  choose ε C hε hεh hC hband using heach
  have hεmin (i : Fin 2) : min (ε 0) (ε 1) ≤ ε i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hCmax (i : Fin 2) : C i ≤ max (C 0) (C 1) := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨η, hη, hηh, G, Rem, hRem, hpole, min (ε 0) (ε 1), max (C 0) (C 1),
    lt_min (hε 0) (hε 1), (min_le_left _ _).trans_lt (hεh 0),
    (hC 0).trans_le (le_max_left _ _), ?_⟩
  intro i t a b s ht hs h2t ha hb hwidth
  calc
    _ ≤ ENNReal.ofReal (C i * t ^ G.rank * s) :=
      hband i ht (h2t.trans_le (hεmin i)) ha hb hwidth
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hCmax i) (pow_nonneg ht.le _)) hs

end OTSelector.Reconstruction
