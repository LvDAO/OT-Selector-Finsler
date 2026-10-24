import OTSelector.Reconstruction.OriginalCubeTraceCompactnessCanonicalSmoothCube
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedKernelLp
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Actual reflected responses as a strongly measurable family in original scalar L2. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

section Restriction
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)

private def originalLtwoRestrictLinear : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 (μ.restrict A) where
  toFun f := ((Lp.memLp f).restrict A).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (f + g)).restrict A).coeFn_toLp,
      ((Lp.memLp f).restrict A).coeFn_toLp, ((Lp.memLp g).restrict A).coeFn_toLp,
      Lp.coeFn_add (((Lp.memLp f).restrict A).toLp f) (((Lp.memLp g).restrict A).toLp g),
      ae_restrict_of_ae (Lp.coeFn_add f g)] with z hfg hf hg hsum hfg'
    rw [hfg, hsum, hfg']
    simp only [Pi.add_apply]
    rw [hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (c • f)).restrict A).coeFn_toLp,
      ((Lp.memLp f).restrict A).coeFn_toLp,
      Lp.coeFn_smul c (((Lp.memLp f).restrict A).toLp f),
      ae_restrict_of_ae (Lp.coeFn_smul c f)] with z hcf hf hsm hcf'
    simp only [RingHom.id_apply]
    rw [hcf, hsm, hcf']
    simp only [Pi.smul_apply]
    rw [hf]

/-- Restriction of an original scalar L2 function to an actual measurable-domain measure
is a genuine continuous linear map with no extra regularity or finite-volume assumption. -/
def originalLtwoRestrict : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict A) :=
  (originalLtwoRestrictLinear μ A).mkContinuous 1 (fun f ↦ by
    rw [one_mul]
    change ‖((Lp.memLp f).restrict A).toLp f‖ ≤ ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_mono_measure f Measure.restrict_le_self))

/-- The actual restricted L2 value retains the literal original representative almost everywhere. -/
theorem originalLtwoRestrict_ae (f : Lp ℝ 2 μ) : originalLtwoRestrict μ A f =ᵐ[μ.restrict A] f :=
  ((Lp.memLp f).restrict A).coeFn_toLp

end Restriction

variable {q : ℕ} {η : (Fin q → ℝ) → ℝ}

private theorem hasCompactSupport_originalUnitKernel
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) : HasCompactSupport η := by
  apply HasCompactSupport.intro (K := haarRootCube (Fin q) 1) isCompact_Icc
  intro z hz
  apply hηsupport
  by_contra! hn
  exact hz ((mem_haarRootCube_iff_norm_le (by norm_num) z).mpr hn.le)

/-- The actual original continuous compact unit-range kernel as one global scalar L2 vector. -/
def originalUnitKernelLtwo (hη : Continuous η) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) :
    Lp ℝ 2 (volume : Measure (Fin q → ℝ)) :=
  (hη.memLp_of_hasCompactSupport (hasCompactSupport_originalUnitKernel hηsupport) (p := 2)).toLp η

/-- The global Hilbert representative is exactly the original kernel almost everywhere. -/
theorem originalUnitKernelLtwo_ae (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) :
    originalUnitKernelLtwo hη hηsupport =ᵐ[volume] η :=
  (hη.memLp_of_hasCompactSupport (hasCompactSupport_originalUnitKernel hηsupport)
    (p := 2)).coeFn_toLp

/-- The genuine translated original kernel, restricted to the actual cube observation measure. -/
def originalTranslatedKernelLtwo (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) (x : Fin q → ℝ) :
    Lp ℝ 2 (volume.restrict (haarRootCube (Fin q) R)) :=
  originalLtwoRestrict volume (haarRootCube (Fin q) R)
    (Lp.compMeasurePreserving (fun z ↦ z - x) (measurePreserving_sub_right volume x)
      (originalUnitKernelLtwo hη hηsupport))

/-- Translating and restricting the actual original kernel is continuous as an L2 family.
The genuine finite-p translation theorem supplies continuity without a convergence oracle. -/
theorem continuous_originalTranslatedKernelLtwo (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) :
    Continuous (originalTranslatedKernelLtwo hη hηsupport R) := by
  let v : (Fin q → ℝ) → C(Fin q → ℝ, Fin q → ℝ) :=
    fun x ↦ ⟨fun z ↦ z - x, continuous_id.sub continuous_const⟩
  have hv : Continuous v := ContinuousMap.continuous_of_continuous_uncurry v (by
    change Continuous (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ p.2 - p.1)
    fun_prop)
  have ht := (continuous_const : Continuous (fun _ : Fin q → ℝ ↦
    originalUnitKernelLtwo hη hηsupport)).compMeasurePreservingLp hv
      (fun x ↦ measurePreserving_sub_right volume x) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  exact (originalLtwoRestrict volume (haarRootCube (Fin q) R)).continuous.comp ht

/-- Each translated restricted Hilbert kernel is the literal original translated kernel. -/
theorem originalTranslatedKernelLtwo_ae (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) (x : Fin q → ℝ) :
    originalTranslatedKernelLtwo hη hηsupport R x =ᵐ[
      volume.restrict (haarRootCube (Fin q) R)] (fun z ↦ η (z - x)) := by
  have hc := Lp.coeFn_compMeasurePreserving (originalUnitKernelLtwo hη hηsupport)
    (measurePreserving_sub_right volume x)
  have he := (measurePreserving_sub_right volume x).quasiMeasurePreserving.ae
    (originalUnitKernelLtwo_ae hη hηsupport)
  exact (originalLtwoRestrict_ae volume (haarRootCube (Fin q) R) _).trans
    (ae_restrict_of_ae (hc.trans he))

/-- The literal reflected full-input response as a single original scalar L2 vector.
Only the input's cube indicator enters, preserving the unchanged full input domain. -/
def originalReflectedInputResponseLtwo (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) (x : Fin q → ℝ) :
    Lp ℝ 2 (volume.restrict (haarRootCube (Fin q) R)) :=
  (haarRootCube (Fin q) R).indicator
    (fun x ↦ ∑ a : Fin q → Fin 3,
      originalTranslatedKernelLtwo hη hηsupport R (originalCubeReflectionImage R a x)) x -
    originalTranslatedKernelLtwo hη hηsupport R x

/-- The actual reflected full-input L2 response family is strongly measurable, internally
from real translation continuity, true reflection maps and the actual input cube indicator. -/
theorem stronglyMeasurable_originalReflectedInputResponseLtwo (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) :
    StronglyMeasurable (originalReflectedInputResponseLtwo hη hηsupport R) := by
  have ht := continuous_originalTranslatedKernelLtwo hη hηsupport R
  have hs : Continuous (fun x ↦ ∑ a : Fin q → Fin 3,
      originalTranslatedKernelLtwo hη hηsupport R (originalCubeReflectionImage R a x)) :=
    continuous_finsetSum Finset.univ (fun a _ ↦ ht.comp (continuous_originalCubeReflectionImage R a))
  exact (hs.stronglyMeasurable.indicator measurableSet_Icc).sub ht.stronglyMeasurable

/-- The actual L2 response is precisely the literal reflected-kernel input response on the
original observation cube, so its later Hilbert image has the original test pairing. -/
theorem originalReflectedInputResponseLtwo_ae (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) (R : ℝ) (x : Fin q → ℝ) :
    originalReflectedInputResponseLtwo hη hηsupport R x =ᵐ[
      volume.restrict (haarRootCube (Fin q) R)]
      (fun z ↦ originalCubeReflectedInputResponse η R z x) := by
  let T := originalTranslatedKernelLtwo hη hηsupport R
  have hs := Lp.coeFn_fun_finsetSum Finset.univ
    (fun a : Fin q → Fin 3 ↦ T (originalCubeReflectionImage R a x))
  have ha := ae_all_iff.mpr (fun a : Fin q → Fin 3 ↦
    originalTranslatedKernelLtwo_ae hη hηsupport R (originalCubeReflectionImage R a x))
  have hx := originalTranslatedKernelLtwo_ae hη hηsupport R x
  by_cases hc : x ∈ haarRootCube (Fin q) R
  · have hd := Lp.coeFn_sub (∑ a : Fin q → Fin 3, T (originalCubeReflectionImage R a x)) (T x)
    filter_upwards [hs, ha, hx, hd] with z hsz haz hxz hdz
    simp only [originalReflectedInputResponseLtwo, indicator_of_mem hc,
      originalCubeReflectedInputResponse] at hdz ⊢
    rw [hdz]
    simp only [Pi.sub_apply]
    rw [hsz, hxz]
    congr 1
    exact Finset.sum_congr rfl (fun a _ ↦ haz a)
  · have hd := Lp.coeFn_neg (T x)
    filter_upwards [hx, hd] with z hxz hdz
    dsimp only [originalReflectedInputResponseLtwo]
    rw [indicator_of_notMem hc, zero_sub]
    change (-T x) z = originalCubeReflectedInputResponse η R z x
    rw [hdz]
    change -(T x z) = (haarRootCube (Fin q) R).indicator
      (originalCubeReflectedKernel η R z) x - η (z - x)
    rw [hxz, indicator_of_notMem hc, zero_sub]

/-- The actual Hilbert response vanishes for every original input outside the same genuine
unit boundary shell, by its proved literal representative and original cube geometry. -/
theorem originalReflectedInputResponseLtwo_eq_zero_off_shell (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R)
    (x : Fin q → ℝ) (hx : x ∉ originalInputBoundaryShell (ι := Fin q) R) :
    originalReflectedInputResponseLtwo hη hηsupport R x = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [originalReflectedInputResponseLtwo_ae hη hηsupport R x,
    ae_restrict_mem (show MeasurableSet (haarRootCube (Fin q) R) from measurableSet_Icc)] with z hz hzc
  exact hz.trans (originalCubeReflectedInputResponse_eq_zero_off_shell hηsupport hR hzc hx)

/-- The actual Hilbert response has genuine compact support in the original input location. -/
theorem hasCompactSupport_originalReflectedInputResponseLtwo (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {R : ℝ} (hR : 1 ≤ R) :
    HasCompactSupport (originalReflectedInputResponseLtwo hη hηsupport R) := by
  apply HasCompactSupport.intro (K := haarRootCube (Fin q) (R + 1)) isCompact_Icc
  intro x hx
  exact originalReflectedInputResponseLtwo_eq_zero_off_shell hη hηsupport hR x
    (fun hs ↦ hx hs.1)

/-- Original amplitude and actual unit support give a radius-independent L2 norm bound
for the genuine reflected response vector. -/
theorem norm_originalReflectedInputResponseLtwo_le (hη : Continuous η)
    (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0) {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ v, |η v| ≤ M) (R : ℝ) (x : Fin q → ℝ) :
    ‖originalReflectedInputResponseLtwo hη hηsupport R x‖ ≤
      (((3 : ℝ)^q + 1) * M) * ((2 : ℝ)^q) ^ (1 / (2 : ℝ)) := by
  have hD : 0 ≤ ((3 : ℝ)^q + 1) * M := mul_nonneg (by positivity) hM
  have hb := eLpNorm_originalCubeReflectedInputResponse_le hM hηM hηsupport 2 R x
  have h := ENNReal.toReal_mono (show
      ENNReal.ofReal (((3 : ℝ)^Fintype.card (Fin q) + 1) * M) *
        ENNReal.ofReal ((2 : ℝ)^Fintype.card (Fin q)) ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ∞ by finiteness) hb
  rw [Lp.norm_def, eLpNorm_congr_ae (originalReflectedInputResponseLtwo_ae hη hηsupport R x)]
  simp only [Fintype.card_fin, ENNReal.toReal_ofNat] at h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hD, ENNReal.toReal_ofReal (show 0 ≤ (2 : ℝ)^q by positivity)] at h
  exact h

end OTSelector.Reconstruction
