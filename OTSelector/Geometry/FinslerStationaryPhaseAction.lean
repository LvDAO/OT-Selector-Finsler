import OTSelector.Geometry.Finsler.SignedSpeed
import OTSelector.Geometry.Finsler.InitialPhaseMomentum
import OTSelector.Geometry.FinslerDistanceParameterJet

/-!
# Stationary action for the original initial-phase family

The original distance is corrected by the smooth initial potential and signed
elapsed lengths. The true endpoint first variation cancels these corrections.
The resulting C2 scalar is stationary without assuming stationarity as an input.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original endpoint distance corrected by initial potential values and the
signed lengths of the same prescribed initial-tangent family. -/
def phaseLengthAction (F : ContinuousFinslerNorm E M) (old : M)
    (Phi : (E × E) → ℝ → M) (P : E → ℝ) (a b : ℝ)
    (z : (E × E) × (E × E)) : ℝ :=
  (F.lengthEDist (Phi z.1 a) (Phi z.2 b)).toReal - P z.2.1 + P z.1.1 -
    b * (F.chartLength old z.2 : ℝ) + a * (F.chartLength old z.1 : ℝ)

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- The actual distance jet and matching initial length covector give a C2 stationary
phase action. No unit-speed premise or stationarity hypothesis is needed. -/
theorem stationary_phaseLengthAction (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old) {P : E → ℝ}
    (hP : ContDiffAt ℝ 2 P z₀.1)
    (hmatch : fderiv ℝ P z₀.1 =
      fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) z₀)
    (a b : ℝ)
    (hdC : ContDiffAt ℝ 2
      (fun z : (E × E) × (E × E) ↦ (F.lengthEDist (Phi z.1 a) (Phi z.2 b)).toReal)
      (z₀, z₀))
    (hd : let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Phi z₀ t) →L[ℝ] ℝ := fun t ↦
        fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Phi z₀ t) ↦
          (F.toFun ⟨Phi z₀ t, v⟩ : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z₀) t 1)
      HasFDerivAt
        (fun z : (E × E) × (E × E) ↦ (F.lengthEDist (Phi z.1 a) (Phi z.2 b)).toReal)
        ((p b).comp (mfderiv 𝓘(ℝ, (E × E) × (E × E)) 𝓘(ℝ, E)
          (fun z ↦ Phi z.2 b) (z₀, z₀)) -
          (p a).comp (mfderiv 𝓘(ℝ, (E × E) × (E × E)) 𝓘(ℝ, E)
            (fun z ↦ Phi z.1 a) (z₀, z₀))) (z₀, z₀)) :
    ContDiffAt ℝ 2 (F.phaseLengthAction old Phi P a b) (z₀, z₀) ∧
      HasFDerivAt (F.phaseLengthAction old Phi P a b)
        (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) (z₀, z₀) := by
  let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Phi z₀ t) →L[ℝ] ℝ := fun t ↦
    fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Phi z₀ t) ↦
      (F.toFun ⟨Phi z₀ t, v⟩ : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z₀) t 1)
  let J : ℝ → (E × E) →L[ℝ] ℝ := fun t ↦
    (p t).comp (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun z ↦ Phi z t) z₀)
  let A := ContinuousLinearMap.fst ℝ (E × E) (E × E)
  let B := ContinuousLinearMap.snd ℝ (E × E) (E × E)
  have hpos (t : ℝ) : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      (fun z ↦ Phi z t) z₀ :=
    (contMDiffAt_positionParameter_of_tangentFamily
      (isOpen_chartEnergyDomain old) hC2 hz₀ t).mdifferentiableAt (by simp)
  have hDa := mfderiv_comp (z₀, z₀) (hpos a)
    ((contDiffAt_fst (𝕜 := ℝ) (n := 1)).contMDiffAt.mdifferentiableAt (by simp))
  have hDb := mfderiv_comp (z₀, z₀) (hpos b)
    ((contDiffAt_snd (𝕜 := ℝ) (n := 1)).contMDiffAt.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, fderiv_fst] at hDa
  rw [mfderiv_eq_fderiv, fderiv_snd] at hDb
  change HasFDerivAt _ ((p b).comp _ - (p a).comp _) (z₀, z₀) at hd
  erw [hDa, hDb, ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc] at hd
  change HasFDerivAt _ ((J b).comp B - (J a).comp A) (z₀, z₀) at hd
  have hJ0 := hF.initial_lengthMomentum_comp_parameterDeriv old hinit hz₀
    (hEL z₀ hz₀ 0 (mem_univ 0))
  change J 0 = _ at hJ0
  rw [← hmatch] at hJ0
  have hPc : HasFDerivAt (fun z : E × E ↦ P z.1) (J 0) z₀ := by
    rw [hJ0]
    exact (hP.differentiableAt (by norm_num)).hasFDerivAt.comp z₀
      (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hs (t : ℝ) : HasFDerivAt (fun z ↦ t * (F.chartLength old z : ℝ))
      (J t - J 0) z₀ := by
    simpa only [sub_zero] using
      hF.hasFDerivAt_signed_speed_of_complete_tangentFamily old 0 hEL hinit hC2 hz₀ t
  have hPa := hPc.comp (z₀, z₀) A.hasFDerivAt
  have hPb := hPc.comp (z₀, z₀) B.hasFDerivAt
  have hsa := (hs a).comp (z₀, z₀) A.hasFDerivAt
  have hsb := (hs b).comp (z₀, z₀) B.hasFDerivAt
  have hder := (((hd.sub hPb).add hPa).sub hsb).add hsa
  have hzero : (J b).comp B - (J a).comp A - (J 0).comp B + (J 0).comp A -
      (J b - J 0).comp B + (J a - J 0).comp A = 0 := by
    simp only [ContinuousLinearMap.sub_comp]
    abel
  rw [hzero] at hder
  have hspeed : ContDiffAt ℝ 2 (fun z ↦ (F.chartLength old z : ℝ)) z₀ :=
    ((hF.contDiffOn_chartLength old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hz₀)).of_le (by simp)
  have hPc2 : ContDiffAt ℝ 2 (fun z : E × E ↦ P z.1) z₀ :=
    hP.comp z₀ contDiffAt_fst
  exact ⟨(((hdC.sub (hPc2.comp (z₀, z₀) contDiffAt_snd)).add
    (hPc2.comp (z₀, z₀) contDiffAt_fst)).sub
      (contDiffAt_const.mul (hspeed.comp (z₀, z₀) contDiffAt_snd))).add
        (contDiffAt_const.mul (hspeed.comp (z₀, z₀) contDiffAt_fst)), hder⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
