import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicHaarMarginal
import OTSelector.Geometry.Finsler.CalibratedSeedWindow

/-!
# Canonical original sample scale and the fixed compact macro cube

Existing exact Haar radii supply every scale/domain/carrier input of the
original scene theorems. The original seed normalization derives a positive
transverse dimension from the original ambient dimension bound.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-- The canonical original spatial scale for n+1 targets in q dimensions. -/
def physicalSceneCanonicalHaarScale (q n : ℕ) : ℝ :=
  2 * haarRootRadius q ((n : ℝ) + 1)

/-- The actual original centered root cube with mass n+1. -/
def physicalSceneCanonicalHaarDomain (q n : ℕ) : Set (Fin q → ℝ) :=
  haarRootCube (Fin q) (haarRootRadius q ((n : ℝ) + 1))

/-- All original macro roots lie in this same compact centered unit cube. -/
def physicalSceneCanonicalMacroCarrier (q : ℕ) : Set (Fin q → ℝ) :=
  haarRootCube (Fin q) (1 / 2)

theorem physicalSceneCanonicalHaarScale_pos (q n : ℕ) :
    0 < physicalSceneCanonicalHaarScale q n :=
  mul_pos (by norm_num) (haarRootRadius_pos _ (by positivity))

theorem physicalSceneCanonicalHaarScale_eq_rpow (q n : ℕ) :
    physicalSceneCanonicalHaarScale q n = ((n : ℝ) + 1) ^ (1 / (q : ℝ)) := by
  unfold physicalSceneCanonicalHaarScale haarRootRadius
  ring

theorem tendsto_physicalSceneCanonicalHaarScale (q : ℕ) (hq : 0 < q) :
    Tendsto (physicalSceneCanonicalHaarScale q) atTop atTop := by
  have hN : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (tendsto_haarRootRadius q hq hN).const_mul_atTop (by norm_num)

theorem physicalSceneCanonicalHaarScale_pow (q : ℕ) (hq : 0 < q) (n : ℕ) :
    physicalSceneCanonicalHaarScale q n ^ q = (n : ℝ) + 1 :=
  haarRootRadius_mass q hq (by positivity)

theorem volume_physicalSceneCanonicalHaarDomain (q : ℕ) (hq : 0 < q) (n : ℕ) :
    volume (physicalSceneCanonicalHaarDomain q n) = ENNReal.ofReal ((n : ℝ) + 1) := by
  simpa only [physicalSceneCanonicalHaarDomain, Fintype.card_fin] using
    volume_haarRootCube_radius (Fin q) (by simpa only [Fintype.card_fin] using hq)
      (N := (n : ℝ) + 1) (by positivity)

theorem isCompact_physicalSceneCanonicalMacroCarrier (q : ℕ) :
    IsCompact (physicalSceneCanonicalMacroCarrier q) := isCompact_Icc

theorem physicalSceneCanonicalHaarDomain_macro_mem (q n : ℕ) {z : Fin q → ℝ}
    (hz : z ∈ physicalSceneCanonicalHaarDomain q n) :
    physicalSceneMacroscopicRoot (physicalSceneCanonicalHaarScale q n) z ∈
      physicalSceneCanonicalMacroCarrier q := by
  change z ∈ physicalSceneMacroscopicRoot (physicalSceneCanonicalHaarScale q n) ⁻¹'
    haarRootCube (Fin q) (1 / 2)
  rw [physicalSceneMacroscopicRoot_preimage_centered_unitCube
    (physicalSceneCanonicalHaarScale_pos q n)]
  have hside : physicalSceneCanonicalHaarScale q n / 2 =
      haarRootRadius q ((n : ℝ) + 1) := by
    unfold physicalSceneCanonicalHaarScale
    ring
  rw [hside]
  exact hz

/-- Every finite canonical root experiment already has the same exact original macro law. -/
theorem physicalSceneMacroscopicRootLaw_canonicalHaarScale
    (q : ℕ) (hq : 0 < q) (n : ℕ) :
    physicalSceneMacroscopicRootLaw n (physicalSceneCanonicalHaarScale q n)
      (physicalSceneCanonicalHaarDomain q n)
      (volume_physicalSceneCanonicalHaarDomain q hq n) =
      physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) := by
  simpa only [physicalSceneCanonicalHaarScale_eq_rpow, physicalSceneCanonicalHaarDomain,
    physicalSceneCanonicalMacroCarrier] using
      physicalSceneMacroscopicRootLaw_haarRootRadius q hq n

section OriginalSeed
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual original seed normalization has positive transverse dimension
under the original ambient dimension bound. -/
theorem original_seed_transverse_finrank_pos (S : F.CalibratedLevelSeedPatch u)
    (hdim : 2 ≤ Module.finrank ℝ E) : 0 < Module.finrank ℝ S.covector.ker := by
  have hh : Module.finrank ℝ S.covector.ker + 1 = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using
      S.normalization.toLinearEquiv.finrank_eq
  omega

/-- All original scene scale, volume and compact macro-carrier inputs are
produced canonically from the SAME original seed and target count. -/
theorem original_seed_canonical_scene_scale_data (W : F.CalibratedSeedWindow u)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    let q := Module.finrank ℝ W.seed.covector.ker
    (∀ n, 0 < physicalSceneCanonicalHaarScale q n) ∧
      Tendsto (physicalSceneCanonicalHaarScale q) atTop atTop ∧
      (∀ n, physicalSceneCanonicalHaarScale q n ^ q = (n : ℝ) + 1) ∧
      (∀ n, volume (physicalSceneCanonicalHaarDomain q n) =
        ENNReal.ofReal ((n : ℝ) + 1)) ∧
      IsCompact (physicalSceneCanonicalMacroCarrier q) ∧
      ∀ n z, z ∈ physicalSceneCanonicalHaarDomain q n →
        physicalSceneMacroscopicRoot (physicalSceneCanonicalHaarScale q n) z ∈
          physicalSceneCanonicalMacroCarrier q := by
  let q := Module.finrank ℝ W.seed.covector.ker
  have hq : 0 < q := original_seed_transverse_finrank_pos W.seed hdim
  exact ⟨physicalSceneCanonicalHaarScale_pos q,
    tendsto_physicalSceneCanonicalHaarScale q hq,
    physicalSceneCanonicalHaarScale_pow q hq,
    volume_physicalSceneCanonicalHaarDomain q hq,
    isCompact_physicalSceneCanonicalMacroCarrier q,
    fun n _ hz ↦ physicalSceneCanonicalHaarDomain_macro_mem q n hz⟩
end OriginalSeed
end OTSelector.Reconstruction
