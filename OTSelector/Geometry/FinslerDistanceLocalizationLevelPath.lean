import OTSelector.Geometry.Finsler.DistanceLocalizationNormalVariation
import OTSelector.Geometry.Finsler.DistanceLocalizationCompletePath

/-!
# Whole-time upper bounds from actual C1,1 level paths

The complete flow, covector normalization, and the actual C1,1 potential
produce the normal cancellation and common compact constants. No derivative
of the initial covector field is prescribed along the chosen path.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Compact legal covector data give one whole-time quadratic distance estimate
for every actual Lipschitz path in a level set of the same C1,1 potential. The
normal cancellation, complete-flow smoothness, and speed bounds are derived. -/
theorem exists_uniform_normalized_level_path_upper
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {P : Set (E × (E →L[ℝ] ℝ))} (hP : IsCompact P) (hPU : P ⊆ eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hDG : LipschitzWith L (fderiv ℝ G)) (lo hi : ℝ) :
    ∃ A : ℝ≥0, 0 < A ∧ ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ≥0,
      ∀ {a b : ℝ}, a ≤ b → lo ≤ a → b ≤ hi →
      ∀ {σ : ℝ → E} {B : ℝ≥0}, LipschitzOnWith B σ (Icc a b) →
      (∀ s ∈ Icc a b, (σ s, fderiv ℝ G (σ s)) ∈ P) →
      ∀ {c : ℝ}, (∀ s ∈ Icc a b, G (σ s) = c) → ((A * B : ℝ≥0) : ℝ) ≤ r →
      let z := fun s ↦ F.covectorNormalization old eL (1 / 2) (σ s, fderiv ℝ G (σ s))
      (F.lengthEDist (Phi (z a) a) (Phi (z b) b)).toReal - (b - a) ≤
        (b - a) * (C : ℝ) * ((A * B : ℝ≥0) : ℝ) ^ 2 := by
  let N := F.covectorNormalization old eL (1 / 2)
  obtain ⟨_, hN, hspec⟩ := hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨_, _, _, _, Cn, hNl⟩ := exists_lipschitzOnWith_cthickening_of_contDiffOn
    hP eL.open_target hPU (hN.of_le (by simp))
  have hNK : IsCompact (N '' P) := hP.image_of_continuousOn (hN.continuousOn.mono hPU)
  have hNU : N '' P ⊆ chartEnergyDomain old := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hspec q (hPU hq)).2.1
  have hunit (z : E × E) (hz : z ∈ N '' P) : (F.chartLength old z : ℝ) = 1 := by
    obtain ⟨q, hq, rfl⟩ := hz
    have he := (hspec q (hPU hq)).2.2.1
    rw [F.chartEnergy_eq_chartLength_sq] at he
    change (F.chartLength old (F.covectorNormalization old eL (1 / 2) q) : ℝ) = 1
    nlinarith [NNReal.coe_nonneg (F.chartLength old
      (F.covectorNormalization old eL (1 / 2) q))]
  obtain ⟨r, hr, C, hb⟩ := hF.exists_uniform_complete_normal_path_upper old
    hEL hinit hNK hNU hunit lo hi
  let A : ℝ≥0 := Cn * max 1 L + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, r, hr, C, ?_⟩
  intro a b hab hlo hhi σ B hσ hσP c hlevel hsmall
  let z := fun s ↦ N (σ s, fderiv ℝ G (σ s))
  have hq : LipschitzOnWith (max B (L * B))
      (fun s ↦ (σ s, fderiv ℝ G (σ s))) (Icc a b) :=
    hσ.prodMk (hDG.comp_lipschitzOnWith hσ)
  have hz₀ : LipschitzOnWith (Cn * max B (L * B)) z (Icc a b) :=
    hNl.comp hq (fun s hs ↦ self_subset_cthickening P (hσP s hs))
  have hz : LipschitzOnWith (A * B) z (Icc a b) := hz₀.weaken (by
    calc
      Cn * max B (L * B) = (Cn * max 1 L) * B := by rw [mul_assoc, max_mul, one_mul]
      _ ≤ A * B := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (show (0 : ℝ≥0) ≤ B from bot_le))
  have hC2 := ((hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old
    (isOpen_chartEnergyDomain old) hEL (ι := fun z : E × E ↦ z)
    contDiffOn_id (mapsTo_id _) hinit).1).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hn := hF.ae_lengthMomentum_normalized_level_path_zero old hEL hinit hC2
    heL hsource hInv hG hDG hσ (fun s hs ↦ hPU (hσP s hs)) hlevel
  apply hb hab hlo hhi hz (fun s hs ↦ mem_image_of_mem N (hσP s hs)) hsmall
  filter_upwards [hn] with s hs
  exact hs.2 s

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
