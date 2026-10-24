import OTSelector.Reconstruction.OriginalPhysicalCompleteWindowTrafficLtwo
import OTSelector.Reconstruction.FinslerOriginalContractiveOldWindows
import OTSelector.Reconstruction.OriginalFocalPositiveResidue
import OTSelector.Reconstruction.OriginalFinslerKernelRightDoublePole

/-! Actual original minimizers have square-integrable traffic in every finite
old-focal physical-clock window. Geometry supplies the pole, normalizer,
eligibility, contractivity, literal one-edge bound and compact-clock moments.
No selected-edge Poisson law or completed L2 estimate is an input. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "q" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin q) × ℝ

/-- The actual supported old-window mask forces its original source clock
strictly inside the physical strip, even when a support closure meets a pole. -/
theorem originalSupportedOldPhysicalClockMask_source_interior
    (ε cap : ℝ) (side : Fin 2) (n ell : ℕ) (m : PhysicalPairPalmMark (Fin q)) (c : ℝ)
    (hc : D.originalSupportedOldPhysicalClockMask ε cap side n ell (m,c) ≠ 0) :
    m.1.1 - S.level ∈ Ioo D.lo D.hi := by
  have hs := D.originalSupportedOldPhysicalClockMask_support ε cap side n ell (m,c) hc
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε _ (m,c)).mp hs.2.2.1
  constructor <;> linarith [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]

/-- The unchanged physical one-edge bound applies to all Palm marks, not only
the occupied selected edges. Marks outside the original interior have zero mask. -/
theorem originalOldWindow_single_bound_of_edge_bound
    {ε cap B : ℝ} (side : Fin 2) (n ell : ℕ) (_hB : 0 ≤ B)
    {η : (Fin q → ℝ) → ℝ}
    (hedge : ∀ e : LegalMarkedPhysicalEdge q,
      e.1.2 - S.level ∈ Ioo D.lo D.hi →
      originalMaskedCompletePathEdgeTraffic S w η
        (D.originalSupportedOldPhysicalClockMask ε cap side n ell) e ≤ ENNReal.ofReal B) :
    ∀ (x : Fin q → ℝ) (m : PhysicalPairPalmMark (Fin q)),
      (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
        D.originalSupportedOldPhysicalClockWeight ε cap side n ell (m,c)) ≤
          ENNReal.ofReal B := by
  intro x m
  by_cases hz : ∀ c, D.originalSupportedOldPhysicalClockMask ε cap side n ell (m,c) = 0
  · simp only [originalSupportedOldPhysicalClockWeight, hz, mul_zero, lintegral_zero]
    exact bot_le
  · push Not at hz
    obtain ⟨c, hc⟩ := hz
    let e := (physicalPairAnchorHomeomorph q).symm (x,m)
    have he : physicalPairAnchor e = (x,m) :=
      (physicalPairAnchorHomeomorph q).apply_symm_apply (x,m)
    have hclock : e.1.2 - S.level ∈ Ioo D.lo D.hi := by
      have hm := D.originalSupportedOldPhysicalClockMask_source_interior ε cap side n ell m c hc
      change (physicalPairAnchor e).2.1.1 - S.level ∈ Ioo D.lo D.hi
      rwa [he]
    have hh := hedge e hclock
    change legalMarkedCompletePathEdgeTraffic q _ _ _ e ≤ _ at hh
    simpa only [legalMarkedCompletePathEdgeTraffic, he, Prod.fst, Prod.snd,
      originalSupportedOldPhysicalClockWeight] using hh

/-- The real old-clock subdivision produces its own literal one-edge constant
on every scale. This uses physical time, without a normalizer in the bound. -/
theorem exists_original_left_oldWindow_single_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ δ : ℝ, 0 < δ ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, 0 < σ ∧
      ∀ {ε cap : ℝ}, 0 < ε → ε < δ → 0 < cap → cap ≤ σ →
      ∀ (n ell : ℕ), ell < birthPhysicalClockWindowCount cap →
      ∀ {R₀ M₀ : ℝ}, 0 ≤ R₀ → 0 ≤ M₀ →
      ∀ {η : (Fin q → ℝ) → ℝ}, (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M₀) →
        (∀ x, R₀ < ‖x‖ → η x = 0) →
      ∀ (x : Fin q → ℝ) (m : PhysicalPairPalmMark (Fin q)),
        (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
          D.originalSupportedOldPhysicalClockWeight ε cap 0 n ell (m,c)) ≤
            ENNReal.ofReal (4 * M₀ * (R₀ + 1)) := by
  obtain ⟨δ,hδ,hδspan,σ,hσ,_hσhalf,hterminal⟩ :=
    D.exists_original_left_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ,hδ,hδspan,σ,hσ,?_⟩
  intro ε cap hε hεδ hcap hcapσ n ell hell R₀ M₀ hR₀ hM₀ η hη0 hηM hηR
  apply D.originalOldWindow_single_bound_of_edge_bound 0 n ell (by positivity)
  intro e he
  let t := birthDyadicShellScale ε n
  let a := oldPhysicalClockWindowReference cap t ell
  let width := oldPhysicalClockWindowWidth cap t
  let ref := D.originalOldPhysicalClockReference ε cap 0 n ell
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs := oldPhysicalClockWindow_spec hcap ht
  have ha := oldPhysicalClockWindow_inward_bounds hcap ht hell
    (show a ∈ Icc a (a+width) from ⟨le_rfl, by dsimp [width]; linarith [hs.2.1]⟩)
  have htwo : 2*t ≤ ε := by
    dsimp [t]
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have haI : a ∈ Ioo (0:ℝ) δ := ⟨ht.trans_le ha.1, ha.2.trans_lt (htwo.trans_lt hεδ)⟩
  have hband : ∀ c ∈ Icc ref (ref+width), |c-S.level-D.lo-a| ≤ σ*a := by
    intro c hc
    have href : ref = S.level + D.lo + a := by rfl
    have hwidth : width ≤ cap*t := hs.2.2.1
    rw [abs_of_nonneg (by linarith [hc.1,href])]
    nlinarith [hwidth, hcapσ, ha.1, hσ, hc.2, href]
  have hz : ∀ c ∉ Icc ref (ref+width),
      D.originalSupportedOldPhysicalClockMask ε cap 0 n ell ((physicalPairAnchor e).2,c) = 0 := by
    intro c hc
    by_contra hn
    have hh := D.originalSupportedOldPhysicalClockMask_left_clock_mem ε cap n ell _ hn
    exact hc ⟨hh.1.le,hh.2⟩
  have hb := (hterminal a haI ref (ref+width) (by linarith [hs.2.1]) hband e he
    R₀ M₀ hR₀ hM₀ η hη0 hηM hηR
    (D.originalSupportedOldPhysicalClockMask ε cap 0 n ell)
    (fun c _ ↦ D.originalSupportedOldPhysicalClockMask_le_one hε cap 0 n ell _) hz).1
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right (by positivity) (min_le_left _ _)))
/-- The real old-clock subdivision produces its own literal one-edge constant
on every scale. This uses physical time, without a normalizer in the bound. -/
theorem exists_original_right_oldWindow_single_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ δ : ℝ, 0 < δ ∧ δ < D.hi - D.lo ∧ ∃ σ : ℝ, 0 < σ ∧
      ∀ {ε cap : ℝ}, 0 < ε → ε < δ → 0 < cap → cap ≤ σ →
      ∀ (n ell : ℕ), ell < birthPhysicalClockWindowCount cap →
      ∀ {R₀ M₀ : ℝ}, 0 ≤ R₀ → 0 ≤ M₀ →
      ∀ {η : (Fin q → ℝ) → ℝ}, (∀ x, 0 ≤ η x) → (∀ x, η x ≤ M₀) →
        (∀ x, R₀ < ‖x‖ → η x = 0) →
      ∀ (x : Fin q → ℝ) (m : PhysicalPairPalmMark (Fin q)),
        (∫⁻ c : ℝ, ENNReal.ofReal (η (x + originalSeedPathOffset S w c m)) *
          D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell (m,c)) ≤
            ENNReal.ofReal (4 * M₀ * (R₀ + 1)) := by
  obtain ⟨δ,hδ,hδspan,σ,hσ,_hσhalf,hterminal⟩ :=
    D.exists_original_right_focal_maskedCompletePathEdgeTraffic hF hw
  refine ⟨δ,hδ,hδspan,σ,hσ,?_⟩
  intro ε cap hε hεδ hcap hcapσ n ell hell R₀ M₀ hR₀ hM₀ η hη0 hηM hηR
  apply D.originalOldWindow_single_bound_of_edge_bound 1 n ell (by positivity)
  intro e he
  let t := birthDyadicShellScale ε n
  let a := oldPhysicalClockWindowReference cap t ell
  let width := oldPhysicalClockWindowWidth cap t
  let ref := D.originalOldPhysicalClockReference ε cap 1 n ell
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs := oldPhysicalClockWindow_spec hcap ht
  have ha := oldPhysicalClockWindow_inward_bounds hcap ht hell
    (show a ∈ Icc a (a+width) from ⟨le_rfl, by dsimp [width]; linarith [hs.2.1]⟩)
  have htwo : 2*t ≤ ε := by
    dsimp [t]
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have haI : a ∈ Ioo (0:ℝ) δ := ⟨ht.trans_le ha.1, ha.2.trans_lt (htwo.trans_lt hεδ)⟩
  have hband : ∀ c ∈ Icc (ref-width) ref, |D.hi-(c-S.level)-a| ≤ σ*a := by
    intro c hc
    have href : ref = S.level + D.hi - a := by
      simp only [ref, originalOldPhysicalClockReference, one_ne_zero, ↓reduceIte, a, t]
    have hwidth : width ≤ cap*t := hs.2.2.1
    rw [abs_of_nonneg (by linarith [hc.2,href])]
    nlinarith [hwidth, hcapσ, ha.1, hσ, hc.1, href]
  have hz : ∀ c ∉ Icc (ref-width) ref,
      D.originalSupportedOldPhysicalClockMask ε cap 1 n ell ((physicalPairAnchor e).2,c) = 0 := by
    intro c hc
    by_contra hn
    have hh := D.originalSupportedOldPhysicalClockMask_right_clock_mem ε cap n ell _ hn
    exact hc ⟨hh.1,hh.2.le⟩
  have hb := (hterminal a haI (ref-width) ref (by linarith [hs.2.1]) hband e he
    R₀ M₀ hR₀ hM₀ η hη0 hηM hηR
    (D.originalSupportedOldPhysicalClockMask ε cap 1 n ell)
    (fun c _ ↦ D.originalSupportedOldPhysicalClockMask_le_one hε cap 1 n ell _) hz).1
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right (by positivity) (min_le_left _ _)))

/-- Geometry and the same attained minimizer produce square-integrable traffic
in every actual left old-focal window, at every dyadic inward scale. -/
theorem exists_original_minimizer_left_oldWindow_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {R₀ M₀ : ℝ} (hR₀ : 0 ≤ R₀) (hM₀ : 0 ≤ M₀)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x) (hηM : ∀ x, η x ≤ M₀)
    (hηR : ∀ x, R₀ < ‖x‖ → η x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi-D.lo ∧ ∃ cap : ℝ, 0 < cap ∧
      ∀ (n ell : ℕ), ell < birthPhysicalClockWindowCount cap →
      MemLp (fun scene ↦ (D.originalOldWindowAbsoluteTraffic η ε cap 0 n ell scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨δ,hδ,hδspan,σ,hσ,hsingle⟩ := D.exists_original_left_oldWindow_single_bound hF hw
  obtain ⟨poleη,hpoleη,hpolespan,P,Rem,hP,hRem,hpole⟩ :=
    D.exists_original_kernel_left_positive_double_pole hF hw
  let poleη' := min poleη δ
  have hpoleη' : 0 < poleη' := lt_min hpoleη hδ
  have hsub : Ioo (-poleη') poleη' ⊆ Ioo (-poleη) poleη := by
    intro x hx
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hx.1,
      lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  obtain ⟨ε,hε,hεpole,h,hh,B,hB,hwindows⟩ :=
    D.exists_original_left_supported_contractive_oldWindows_sameResidue hF hw hbounds hgap
      hpoleη' ((min_le_left _ _).trans_lt hpolespan) hP (hRem.continuousOn.mono hsub)
      (fun r hr ↦ hpole r ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩)
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let basecap := min σ (1/4:ℝ)
  have hbasecap : 0 < basecap := lt_min hσ (by norm_num)
  let cap := commonPhysicalNormalizedWindowFraction (min basecap (1/4)) B (L:ℝ)
  have hcap : 0 < cap := (commonPhysicalNormalizedWindowFraction_spec
    (lt_min hbasecap (by norm_num)) hB L.coe_nonneg).1
  have hcapσ : cap ≤ σ := (commonPhysicalNormalizedWindowFraction_le_cap _ _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : ε < δ := hεpole.trans_le (min_le_right _ _)
  have hεspan : ε < D.hi-D.lo := hεδ.trans hδspan
  refine ⟨ε,hε,hεspan,cap,hcap,?_⟩
  intro n ell hell
  let T := positiveMatrixNormalizer (focalResidueScale P (birthDyadicShellScale ε n))
  let ref := D.originalOldPhysicalClockReference ε cap 0 n ell
  let width := oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)
  let cut := ref-S.level
  have ht := birthDyadicShellScale_pos hε n
  have hwidth : 0 < width := (oldPhysicalClockWindow_spec hcap ht).2.1
  rcases hwindows L basecap hbasecap n ell hell with
    ⟨hT,hcut,hclockRange,hRzero,hR,hRLip,hsmall,helig⟩
  let _ := Matrix.invertibleOfIsUnitDet T hT
  have hcut' : cut ∈ Ioo D.lo D.hi := hcut
  have hclockRange' : ∀ r ∈ Icc (0:ℝ) 1, cut+width*r ∈ Ioo D.lo D.hi := by
    intro r hr
    have hc := hclockRange r hr
    change ref+width*r-S.level ∈ Ioo D.lo D.hi at hc
    convert hc using 1
    dsimp [cut]
    ring
  have hsmall' : ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) width r‖ *
        Real.sqrt ((q:ℝ)/h^2) ≤ (1/2:ℝ) := by
    change ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) width r‖ * (L:ℝ) ≤ (1/2:ℝ)
    simpa only [cut,sub_add_cancel] using hsmall
  have hR' : ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) width r‖ ≤ cap*B := by
    simpa only [cut,sub_add_cancel] using hR
  have hRLip' : ∀ r ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) width r -
        originalNormalizedClockMobility S w T (cut+S.level) width v‖ ≤ cap*B*|r-v| := by
    simpa only [cut,sub_add_cancel] using hRLip
  have hclock : ∀ m c, D.originalSupportedOldPhysicalClockMask ε cap 0 n ell (m,c) ≠ 0 →
      ∃ r ∈ Icc (0:ℝ) 1, c=cut+S.level+width*r := by
    intro m c hc
    have hc' := D.originalSupportedOldPhysicalClockMask_left_clock_mem ε cap n ell _ hc
    change ref<c ∧ c≤ref+width at hc'
    refine ⟨(c-ref)/width,⟨div_nonneg (by linarith [hc'.1]) hwidth.le,
      (div_le_iff₀ hwidth).mpr (by linarith [hc'.2])⟩,?_⟩
    dsimp [cut]
    field_simp
    ring
  have hηwindow : ∀ x, η x ≠ 0 → ‖T*ᵥx‖ ≤ ‖T‖*R₀ := by
    intro x hx
    have hnorm : ‖x‖ ≤ R₀ := le_of_not_gt (fun hn ↦ hx (hηR x hn))
    exact (Matrix.linfty_opNorm_mulVec T x).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  have hclockJ : ∀ c ∈ Icc ref (ref+width), c-S.level ∈ Ioo D.lo D.hi := by
    intro c hc
    have hh := D.originalOldPhysicalClockWindow_left_inward hε hcap n ell hell hc
    have htwo : 2*birthDyadicShellScale ε n ≤ ε := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    constructor <;> linarith [hh.1,hh.2]
  have hzero : ∀ m c, c ∉ Icc ref (ref+width) →
      D.originalSupportedOldPhysicalClockMask ε cap 0 n ell (m,c)=0 := by
    intro m c hc
    by_contra hn
    have hh := D.originalSupportedOldPhysicalClockMask_left_clock_mem ε cap n ell _ hn
    exact hc ⟨hh.1.le,hh.2⟩
  exact D.original_minimizer_physicalWindowTraffic_memLp_two hF hw hgap hbounds T
    hg hgb τ Q hmin hcut' hh (mul_nonneg (norm_nonneg _) hR₀) hclockRange' hsmall'
    (mul_nonneg hcap.le hB) hR' hRLip' hR₀ hM₀ hη hηM hηR
    (D.originalSupportedOldPhysicalClockMask ε cap 0 n ell)
    (D.measurable_originalSupportedOldPhysicalClockMask ε cap 0 n ell)
    (D.originalSupportedOldPhysicalClockMask_le_one hε cap 0 n ell) hclock hηwindow
    (fun e c hc ↦ (helig e c hc).1) isCompact_Icc hclockJ hzero
    (hsingle hε hεδ hcap hcapσ n ell hell hR₀ hM₀ hη0 hηM hηR)
/-- Geometry and the same attained minimizer produce square-integrable traffic
in every actual right old-focal window, at every dyadic inward scale. -/
theorem exists_original_minimizer_right_oldWindow_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {R₀ M₀ : ℝ} (hR₀ : 0 ≤ R₀) (hM₀ : 0 ≤ M₀)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η)
    (hη0 : ∀ x, 0 ≤ η x) (hηM : ∀ x, η x ≤ M₀)
    (hηR : ∀ x, R₀ < ‖x‖ → η x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi-D.lo ∧ ∃ cap : ℝ, 0 < cap ∧
      ∀ (n ell : ℕ), ell < birthPhysicalClockWindowCount cap →
      MemLp (fun scene ↦ (D.originalOldWindowAbsoluteTraffic η ε cap 1 n ell scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨δ,hδ,hδspan,σ,hσ,hsingle⟩ := D.exists_original_right_oldWindow_single_bound hF hw
  obtain ⟨poleη,hpoleη,hpolespan,P,Rem,hP,hRem,hpole⟩ :=
    D.exists_original_kernel_right_positive_double_pole hF hw
  let poleη' := min poleη δ
  have hpoleη' : 0 < poleη' := lt_min hpoleη hδ
  have hsub : Ioo (-poleη') poleη' ⊆ Ioo (-poleη) poleη := by
    intro x hx
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hx.1,
      lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  obtain ⟨ε,hε,hεpole,h,hh,B,hB,hwindows⟩ :=
    D.exists_original_right_supported_contractive_oldWindows_sameResidue hF hw hbounds hgap
      hpoleη' ((min_le_left _ _).trans_lt hpolespan) hP (hRem.continuousOn.mono hsub)
      (fun r hr ↦ hpole r ⟨hr.1,hr.2.trans_le (min_le_left _ _)⟩)
  let L : ℝ≥0 := ⟨Real.sqrt ((q:ℝ)/h^2),Real.sqrt_nonneg _⟩
  let basecap := min σ (1/4:ℝ)
  have hbasecap : 0 < basecap := lt_min hσ (by norm_num)
  let cap := commonPhysicalNormalizedWindowFraction (min basecap (1/4)) B (L:ℝ)
  have hcap : 0 < cap := (commonPhysicalNormalizedWindowFraction_spec
    (lt_min hbasecap (by norm_num)) hB L.coe_nonneg).1
  have hcapσ : cap ≤ σ := (commonPhysicalNormalizedWindowFraction_le_cap _ _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : ε < δ := hεpole.trans_le (min_le_right _ _)
  have hεspan : ε < D.hi-D.lo := hεδ.trans hδspan
  refine ⟨ε,hε,hεspan,cap,hcap,?_⟩
  intro n ell hell
  let T := positiveMatrixNormalizer (focalResidueScale P (birthDyadicShellScale ε n))
  let ref := D.originalOldPhysicalClockReference ε cap 1 n ell
  let width := oldPhysicalClockWindowWidth cap (birthDyadicShellScale ε n)
  let cut := ref-S.level
  have ht := birthDyadicShellScale_pos hε n
  have hwidth : 0 < width := (oldPhysicalClockWindow_spec hcap ht).2.1
  rcases hwindows L basecap hbasecap n ell hell with
    ⟨hT,hcut,hclockRange,hRzero,hR,hRLip,hsmall,helig⟩
  let _ := Matrix.invertibleOfIsUnitDet T hT
  have hcut' : cut ∈ Ioo D.lo D.hi := hcut
  have hclockRange' : ∀ r ∈ Icc (0:ℝ) 1, cut+(-width)*r ∈ Ioo D.lo D.hi := by
    intro r hr
    have hc := hclockRange r hr
    change ref+(-width)*r-S.level ∈ Ioo D.lo D.hi at hc
    convert hc using 1
    dsimp [cut]
    ring
  have hsmall' : ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r‖ *
        Real.sqrt ((q:ℝ)/h^2) ≤ (1/2:ℝ) := by
    change ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r‖ * (L:ℝ) ≤ (1/2:ℝ)
    simpa only [cut,sub_add_cancel] using hsmall
  have hR' : ∀ r ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r‖ ≤ cap*B := by
    simpa only [cut,sub_add_cancel] using hR
  have hRLip' : ∀ r ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) (-width) r -
        originalNormalizedClockMobility S w T (cut+S.level) (-width) v‖ ≤ cap*B*|r-v| := by
    simpa only [cut,sub_add_cancel] using hRLip
  have hclock : ∀ m c, D.originalSupportedOldPhysicalClockMask ε cap 1 n ell (m,c) ≠ 0 →
      ∃ r ∈ Icc (0:ℝ) 1, c=cut+S.level+(-width)*r := by
    intro m c hc
    have hc' := D.originalSupportedOldPhysicalClockMask_right_clock_mem ε cap n ell _ hc
    change ref-width≤c ∧ c<ref at hc'
    refine ⟨(ref-c)/width,⟨div_nonneg (by linarith [hc'.2]) hwidth.le,
      (div_le_iff₀ hwidth).mpr (by linarith [hc'.1])⟩,?_⟩
    dsimp [cut]
    field_simp
    ring
  have hηwindow : ∀ x, η x ≠ 0 → ‖T*ᵥx‖ ≤ ‖T‖*R₀ := by
    intro x hx
    have hnorm : ‖x‖ ≤ R₀ := le_of_not_gt (fun hn ↦ hx (hηR x hn))
    exact (Matrix.linfty_opNorm_mulVec T x).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  have hclockJ : ∀ c ∈ Icc (ref-width) ref, c-S.level ∈ Ioo D.lo D.hi := by
    intro c hc
    have hh := D.originalOldPhysicalClockWindow_right_inward hε hcap n ell hell hc
    have htwo : 2*birthDyadicShellScale ε n ≤ ε := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    constructor <;> linarith [hh.1,hh.2]
  have hzero : ∀ m c, c ∉ Icc (ref-width) ref →
      D.originalSupportedOldPhysicalClockMask ε cap 1 n ell (m,c)=0 := by
    intro m c hc
    by_contra hn
    have hh := D.originalSupportedOldPhysicalClockMask_right_clock_mem ε cap n ell _ hn
    exact hc ⟨hh.1,hh.2.le⟩
  exact D.original_minimizer_physicalWindowTraffic_memLp_two hF hw hgap hbounds T
    hg hgb τ Q hmin hcut' hh (mul_nonneg (norm_nonneg _) hR₀) hclockRange' hsmall'
    (mul_nonneg hcap.le hB) hR' hRLip' hR₀ hM₀ hη hηM hηR
    (D.originalSupportedOldPhysicalClockMask ε cap 1 n ell)
    (D.measurable_originalSupportedOldPhysicalClockMask ε cap 1 n ell)
    (D.originalSupportedOldPhysicalClockMask_le_one hε cap 1 n ell) hclock hηwindow
    (fun e c hc ↦ (helig e c hc).1) isCompact_Icc hclockJ hzero
    (hsingle hε hεδ hcap hcapσ n ell hell hR₀ hM₀ hη0 hηM hηR)

/-- The finite physical-clock cover transfers actual window L2 estimates to
the same old-focal clock piece. Original kinetic first moments internally
rule out infinite ENNReal summands before passing to real values. -/
theorem originalOldPiece_memLp_two_of_physicalWindows
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) (side : Fin 2) (n : ℕ)
    (hlocal : ∀ ell < birthPhysicalClockWindowCount cap,
      MemLp (fun scene ↦ (D.originalOldWindowAbsoluteTraffic η ε cap side n ell scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) :
    MemLp (fun scene ↦
      (D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr (side,n))) scene).toReal)
      2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  have hsumLp : MemLp (fun scene ↦ ∑ ell : Fin (birthPhysicalClockWindowCount cap),
      (D.originalOldWindowAbsoluteTraffic η ε cap side n ell scene).toReal) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
    memLp_finsetSum Finset.univ (fun ell _ ↦ hlocal ell ell.isLt)
  apply hsumLp.ae_eq
  filter_upwards [D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hη hηI]
    with scene hfinite
  have hpiece : D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr (side,n))) scene ≤
      originalSeedCompletePathAbsoluteTraffic S w η scene := by
    apply legalMarkedCompletePathTraffic_mono_weights
    intro z
    calc
      _ ≤ 1 * ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ :=
        mul_le_mul' (originalPairClockSupportMask_le_one q μ ν z)
          (D.originalClockTrafficPieceWeight_le_occupation hε _ z)
      _ = _ := one_mul _
  have heq := D.sum_originalOldWindowAbsoluteTraffic hF hw hη hε hcap side n scene
  have hwfinite (ell : Fin (birthPhysicalClockWindowCount cap)) :
      D.originalOldWindowAbsoluteTraffic η ε cap side n ell scene ≠ (⊤:ℝ≥0∞) := by
    apply ne_top_of_le_ne_top hfinite.ne
    apply le_trans _ hpiece
    rw [← heq]
    exact Finset.single_le_sum
      (f := fun i : Fin (birthPhysicalClockWindowCount cap) ↦
        D.originalOldWindowAbsoluteTraffic η ε cap side n i scene)
      (fun i _ ↦ by positivity) (Finset.mem_univ ell)
  rw [← heq, ENNReal.toReal_sum (fun ell _ ↦ hwfinite ell)]

/-- With no supplied L2 or envelope estimate, the same attained original
minimizer has L2 traffic on every actual left old-focal dyadic piece. -/
theorem exists_original_minimizer_left_oldPiece_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {R₀ M₀ : ℝ} (hR₀ : 0 ≤ R₀) (hM₀ : 0 ≤ M₀)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hη0 : ∀ x, 0 ≤ η x) (hηM : ∀ x, η x ≤ M₀)
    (hηR : ∀ x, R₀ < ‖x‖ → η x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi-D.lo ∧ ∀ n : ℕ,
      MemLp (fun scene ↦
        (D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr (0,n))) scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨ε,hε,hεspan,cap,hcap,hlocal⟩ :=
    D.exists_original_minimizer_left_oldWindow_memLp_two hF hw hgap hbounds
      hg hgb τ Q hmin hR₀ hM₀ hη hη0 hηM hηR
  exact ⟨ε,hε,hεspan,fun n ↦ D.originalOldPiece_memLp_two_of_physicalWindows
    hF hw hbounds Q hη hηI hε hcap 0 n (hlocal n)⟩
/-- With no supplied L2 or envelope estimate, the same attained original
minimizer has L2 traffic on every actual right old-focal dyadic piece. -/
theorem exists_original_minimizer_right_oldPiece_memLp_two
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ x y, |g x y| ≤ G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching q μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ P.value τ)
    {R₀ M₀ : ℝ} (hR₀ : 0 ≤ R₀) (hM₀ : 0 ≤ M₀)
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hη0 : ∀ x, 0 ≤ η x) (hηM : ∀ x, η x ≤ M₀)
    (hηR : ∀ x, R₀ < ‖x‖ → η x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi-D.lo ∧ ∀ n : ℕ,
      MemLp (fun scene ↦
        (D.originalClockPieceAbsoluteTraffic η ε (.inl (.inr (1,n))) scene).toReal)
        2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨ε,hε,hεspan,cap,hcap,hlocal⟩ :=
    D.exists_original_minimizer_right_oldWindow_memLp_two hF hw hgap hbounds
      hg hgb τ Q hmin hR₀ hM₀ hη hη0 hηM hηR
  exact ⟨ε,hε,hεspan,fun n ↦ D.originalOldPiece_memLp_two_of_physicalWindows
    hF hw hbounds Q hη hηI hε hcap 1 n (hlocal n)⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
