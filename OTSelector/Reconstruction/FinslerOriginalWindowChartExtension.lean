import OTSelector.Reconstruction.FinslerOriginalWindowChartData
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.C11FiniteLevelSeeds

/-!
# Open-neighbourhood chart data from compact C1,1 ball cores

`FinslerOriginalWindowChartData.lean` constructed the atlas-level
`WindowChartData` from the pre-atlas rational chart construction, but left four
open-neighbourhood extension inputs of the `CoreSectionChartData`:

* `EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ chart⁻¹)) U`,
* `EqOn G (u ∘ chart⁻¹) U`,
* `HasFDerivAt (u ∘ chart⁻¹) (fderiv ℝ G y) y` for all `y ∈ U`,
* `CalibratedPartners F u old δ U`,

because the countable calibrated C1,1 family cover supplies the potential data and
the calibration partners only on its compact cores.

## What this file proves

The four open-neighbourhood inputs are *not* independent geometry.  They are
obtained from **compact** data by running the C1,1 ball-core refinement:

* `exists_ball_core_C11_data` produces a C1,1 potential `G` matching `u` on a
  **closed** ball `closedBall y' σ` and differentiating `u` there;
* the compact partner data on that closed ball comes from the calibration
  partners at a prescribed distance on a compact core;
* the ambient curve family `exists_C11_core_family_ball` produces complete
  Euler--Lagrange curves with the correct initial momentum on a closed ball
  `closedBall x r`.

Choosing the open chart domain `U := ball x rU` with `rU := min r (ρx / 2)`, every
open-neighbourhood field follows by monotonicity from the closed-ball data:
potential match and derivative restrictions, the differentiability statement, and
the calibration partners (`CalibratedPartners.mono`).  The finite rational level
seeds then produce the level section on the compact core `K := closedBall x (rU/3)`
and the resulting `CoreSectionChartData` yields `WindowChartData` through
`windowChartData_of_coreSectionChartData`.

## Exact remaining input

The construction consumes producer data that is *compact*, never open:

1. `BallCorePotentialData`: a compact chart ball `closedBall y ρ` with two-sided
   calibration partners at a fixed distance `δ`, refined by
   `exists_ball_core_C11_data` to a closed-ball potential core.

This is the only geometric input.  The rational level is *constructed*:
`exists_rationalLevelPoint_of_ballCore` uses the level-coordinate chart
`exists_original_levelCoordinates_of_calibrated_core` (whose first coordinate is
the potential and whose target is open) together with the density of the rationals
to find, in any ball inside the refined potential core, a point at a rational
level.  Consequently `exists_windowChartData_of_ballCoreData` yields
`WindowChartData` from a compact potential ball core alone, and
`exists_windowChartData_of_chartBallReach` from a compact chart ball with uniform
two-sided reach alone: no open-neighbourhood potential/partner extension input and
no level input remain.  The pre-atlas family cover supplies the two-sided reach at
a fixed distance on its *compact* cores; it is this compact reach data that the
remaining producer input asks for on a chart ball.
-/
open Set Function MeasureTheory Manifold OTSelector.Geometry
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe uE uM uZ

variable {E : Type uE} {M : Type uM} {Z : Type uZ}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## Monotonicity of the calibration partner condition -/

/-- The calibration-partner condition is monotone in the chart set. -/
theorem CalibratedPartners.mono {old : M} {delta : ℝ} {S T : Set E}
    (h : CalibratedPartners F u old delta T) (hST : S ⊆ T) :
    CalibratedPartners F u old delta S := by
  intro x hx
  exact h x (hST hx)

/-! ## Compact potential ball cores -/

/-- A compact chart ball carrying a C1,1 potential core: two-sided calibration
partners at a fixed distance on the closed ball, together with a refined closed
potential ball on which the C1,1 potential matches the original potential, matches
its derivative, and differentiates it.  This is the output shape of
`exists_ball_core_C11_data`, separated into fields. -/
structure BallCorePotentialData (F : ContinuousFinslerNorm E M) (u : M → ℝ) (old : M) where
  delta : ℝ
  delta_pos : 0 < delta
  y : E
  rho : ℝ
  rho_pos : 0 < rho
  yball : closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target
  reach : CalibratedPartners F u old delta (closedBall y rho)
  y' : E
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_subset : closedBall y' sigma ⊆ closedBall y rho
  G : E → ℝ
  L : ℝ≥0
  G_contDiff : ContDiff ℝ 1 G
  G_support : HasCompactSupport G
  G_lip : LipschitzWith L (fderiv ℝ G)
  G_val : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (closedBall y' sigma)
  G_match : EqOn (fderiv ℝ G)
    (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) (closedBall y' sigma)
  G_actual : ∀ z ∈ closedBall y' sigma,
    HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G z) z

/-- **The compact potential ball core exists.**  Running the calibrated C1,1 ball
core refinement on a compact chart ball with uniform two-sided reach produces the
`BallCorePotentialData`. -/
theorem exists_ballCorePotentialData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {delta : ℝ} (hdelta : 0 < delta)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {rho : ℝ} (hrho : 0 < rho)
    (hyball : closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hreach : CalibratedPartners F u old delta (closedBall y rho)) :
    Nonempty (BallCorePotentialData (F := F) (u := u) old) := by
  obtain ⟨y', sig, G, L, hsig, hsub, hG, hsupp, hLip, hval, hmatch, hactual⟩ :=
    exists_ball_core_C11_data (u := u) hF hcomplete old hdelta hu hrho hyball hreach
  exact ⟨
    { delta := delta
      delta_pos := hdelta
      y := y
      rho := rho
      rho_pos := hrho
      yball := hyball
      reach := hreach
      y' := y'
      sigma := sig
      sigma_pos := hsig
      sigma_subset := hsub
      G := G
      L := L
      G_contDiff := hG
      G_support := hsupp
      G_lip := hLip
      G_val := hval
      G_match := hmatch
      G_actual := hactual }⟩

/-! ## The chart datum on an open chart ball -/

/-- **The `CoreSectionChartData` on an open chart ball from a compact potential
ball core.**  The open chart domain is `ball x (min r (ρx / 2))`, where `r` is the
radius of the complete Euler--Lagrange curve family of `exists_C11_core_family_ball`
and `ρx` is the radius of a closed ball inside the potential core.  All four
open-neighbourhood potential/partner fields follow from the closed-ball data of the
potential core, and the level section comes from the finite rational level seeds on
the compact core `closedBall x (min r (ρx / 2) / 3)`. -/
theorem exists_chartData_and_core_of_ballCore
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {old : M} (BC : BallCorePotentialData (F := F) (u := u) old)
    (q : ℚ) (x : E) (rhox : ℝ) (hrhox : 0 < rhox)
    (hxsub : closedBall x rhox ⊆ closedBall BC.y' BC.sigma)
    (hxq : BC.G x = (q : ℝ)) :
    ∃ (C : CoreSectionChartData F u) (K : Set E),
      IsCompact K ∧ K ⊆ C.U ∧ C.σ 0 ∈ K := by
  have hxmem : x ∈ closedBall BC.y' BC.sigma :=
    hxsub (mem_closedBall_self hrhox.le)
  have hxsubBig : closedBall x rhox ⊆ closedBall BC.y BC.rho :=
    hxsub.trans BC.sigma_subset
  have hK0target : closedBall x rhox ⊆ (extChartAt 𝓘(ℝ, E) old).target :=
    hxsubBig.trans BC.yball
  have hmatch0 : EqOn (fderiv ℝ BC.G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) (closedBall x rhox) :=
    BC.G_match.mono hxsub
  have hpart0 : CalibratedPartners F u old BC.delta (closedBall x rhox) :=
    BC.reach.mono hxsubBig
  obtain ⟨r, Γ, hrpos, hrtarget, hΓprops⟩ :=
    hF.exists_C11_core_family_ball (K := closedBall x rhox) (f := u)
      (G := BC.G) (L := BC.L) (x₀ := x) hcomplete old hK0target hu BC.G_contDiff
      BC.G_lip hmatch0 BC.delta_pos hpart0 (mem_closedBall_self hrhox.le)
  set rU : ℝ := min r (rhox / 2) with hrUdef
  have hrUpos : 0 < rU := lt_min hrpos (by positivity)
  have hrU_r : rU ≤ r := min_le_left _ _
  have hrU_x : rU ≤ rhox / 2 := min_le_right _ _
  set U : Set E := ball x rU with hUdef
  have hU_ballr : U ⊆ closedBall x r := by
    intro z hz
    rw [mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le (mem_ball.mp hz) hrU_r)
  have hU_ballx : U ⊆ closedBall x rhox := by
    intro z hz
    rw [mem_closedBall]
    have h := mem_ball.mp hz
    linarith
  have hU_ballY' : U ⊆ closedBall BC.y' BC.sigma := hU_ballx.trans hxsub
  have hU_ballY : U ⊆ closedBall BC.y BC.rho := hU_ballY'.trans BC.sigma_subset
  have hU_target : U ⊆ (extChartAt 𝓘(ℝ, E) old).target := hU_ballr.trans hrtarget
  set K : Set E := closedBall x (rU / 3) with hKdef
  have hKU : K ⊆ U := by
    intro z hz
    rw [hUdef, mem_ball]
    have h := mem_closedBall.mp hz
    linarith
  have hKcompact : IsCompact K := isCompact_closedBall x (rU / 3)
  have hK_ballx : K ⊆ closedBall x rhox := by
    intro z hz
    rw [mem_closedBall]
    have h := mem_closedBall.mp hz
    linarith
  have hK_ballY' : K ⊆ closedBall BC.y' BC.sigma := hK_ballx.trans hxsub
  have hK_ballY : K ⊆ closedBall BC.y BC.rho := hK_ballY'.trans BC.sigma_subset
  have hpartK : CalibratedPartners F u old BC.delta K := BC.reach.mono hK_ballY
  obtain ⟨J, aC, Cg, sec, hseed, hcover⟩ :=
    hF.exists_finite_original_levelSeeds (u := u) (K := K) (U := U) hcomplete old
      hKcompact isOpen_ball hKU hU_target hu BC.G_contDiff
      (BC.G_val.mono hK_ballY') (BC.G_match.mono hK_ballY') BC.delta_pos hpartK (q : ℝ)
  have hxK : x ∈ K := mem_closedBall_self (by positivity : (0 : ℝ) ≤ rU / 3)
  have hxval : u ((extChartAt 𝓘(ℝ, E) old).symm x) = (q : ℝ) :=
    (BC.G_val hxmem).symm.trans hxq
  have hxmem2 : x ∈ K ∩ {z | u ((extChartAt 𝓘(ℝ, E) old).symm z) = (q : ℝ)} :=
    ⟨hxK, hxval⟩
  rw [hcover] at hxmem2
  obtain ⟨y₀, hy₀J, hxmem3⟩ := mem_iUnion₂.mp hxmem2
  rw [mem_image] at hxmem3
  obtain ⟨w₀, hw₀prop, -⟩ := hxmem3
  obtain ⟨ha, hzero, hσcont, -, hσU, hlevel, -, hσD, hinj, hdim, himm⟩ := hseed y₀ hy₀J
  have hcenter : (sec y₀) 0 ∈ K := by
    rw [hzero]
    exact y₀.property.1
  refine ⟨
    { old := old
      G := BC.G
      L := BC.L
      U := U
      U_open := isOpen_ball
      U_target := hU_target
      Γ := Γ
      δ := BC.delta
      δ_pos := BC.delta_pos
      p := fderiv ℝ BC.G (y₀ : E)
      V := ball 0 (aC y₀)
      V_open := isOpen_ball
      σ := sec y₀
      G_contDiff := BC.G_contDiff
      G_lip := BC.G_lip
      match_U := BC.G_match.mono hU_ballY'
      val_U := BC.G_val.mono hU_ballY'
      actual_U := fun z hz => BC.G_actual z (hU_ballY' hz)
      EL_U := fun z hz => (hΓprops z (hU_ballr hz)).2.1
      init_U := fun z hz => (hΓprops z (hU_ballr hz)).1
      mom_U := fun z hz => (hΓprops z (hU_ballr hz)).2.2.2
      partners_U := BC.reach.mono hU_ballY
      σ_contDiff := hσcont
      σ_mapsTo := hσU
      σ_inj := hinj
      dim := hdim
      zero_V := mem_ball_self ha
      covector_eq := by rw [hzero]
      σ_deriv := hσD
      σ_imm := himm
      q := q
      G_level := hlevel },
    K, hKcompact, hKU, hcenter⟩

/-! ## The atlas-level field without open-neighbourhood inputs -/

/-- **`WindowChartData` from a compact potential ball core and a rational-level
point.**  No open-neighbourhood potential or partner extension input is required:
the chart datum on the open chart ball is constructed from the closed-ball data. -/
theorem exists_windowChartData_of_ballCore
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {old : M} (BC : BallCorePotentialData (F := F) (u := u) old)
    (q : ℚ) (x : E) (rhox : ℝ) (hrhox : 0 < rhox)
    (hxsub : closedBall x rhox ⊆ closedBall BC.y' BC.sigma)
    (hxq : BC.G x = (q : ℝ)) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨C, K, hK, hKU, hKcenter⟩ :=
    exists_chartData_and_core_of_ballCore hF hcomplete hu BC q x rhox hrhox hxsub hxq
  exact windowChartData_of_coreSectionChartData hF hcomplete hu C hK hKU hKcenter

/-- **The compact producer form.**  From the compact chart-ball producer inputs of
`exists_ball_core_C11_data` one obtains the refined potential core `G`, and every
rational-level point inside a closed sub-ball of it yields a constant window family
carrying `WindowChartData`. -/
theorem exists_ballCore_levelWindow
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {delta : ℝ} (hdelta : 0 < delta)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {rho : ℝ} (hrho : 0 < rho)
    (hyball : closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hreach : CalibratedPartners F u old delta (closedBall y rho)) :
    ∃ (y' : E) (sig : ℝ) (G : E → ℝ) (L : ℝ≥0), 0 < sig ∧
      closedBall y' sig ⊆ closedBall y rho ∧
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧ LipschitzWith L (fderiv ℝ G) ∧
      EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (closedBall y' sig) ∧
      EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm))
        (closedBall y' sig) ∧
      (∀ z ∈ closedBall y' sig,
        HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G z) z) ∧
      ∀ (q : ℚ) (x : E) (rhox : ℝ), 0 < rhox → closedBall x rhox ⊆ closedBall y' sig →
        G x = (q : ℝ) →
          ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨y', sig, G, L, hsig, hsub, hG, hsupp, hLip, hval, hmatch, hactual⟩ :=
    exists_ball_core_C11_data (u := u) hF hcomplete old hdelta hu hrho hyball hreach
  let BC : BallCorePotentialData (F := F) (u := u) old :=
    { delta := delta
      delta_pos := hdelta
      y := y
      rho := rho
      rho_pos := hrho
      yball := hyball
      reach := hreach
      y' := y'
      sigma := sig
      sigma_pos := hsig
      sigma_subset := hsub
      G := G
      L := L
      G_contDiff := hG
      G_support := hsupp
      G_lip := hLip
      G_val := hval
      G_match := hmatch
      G_actual := hactual }
  refine ⟨y', sig, G, L, hsig, hsub, hG, hsupp, hLip, hval, hmatch, hactual, ?_⟩
  intro q x rhox hrhox hxsub hxq
  exact exists_windowChartData_of_ballCore hF hcomplete hu BC q x rhox hrhox hxsub hxq


/-! ## The rational level point from the level-coordinate chart -/

/-- **A rational-level point exists in any ball inside the refined potential core.**
The calibrated core reach makes the potential derivative nonzero at every core
point, so the level-coordinate chart of `exists_original_levelCoordinates_of_calibrated_core`
is an open partial homeomorphism whose first coordinate is the potential.  Its
target is open around `(G x, 0)`, hence contains a point `(q, 0)` with `q` rational
arbitrarily close to `G x`; the inverse image is a point of the potential core with
the rational level `q`. -/
theorem exists_rationalLevelPoint_of_ballCore
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {old : M} (BC : BallCorePotentialData (F := F) (u := u) old)
    (x : E) (rhox : ℝ) (hrhox : 0 < rhox)
    (hxsub : closedBall x (2 * rhox) ⊆ closedBall BC.y' BC.sigma) :
    ∃ (z : E) (rhoz : ℝ) (q : ℚ), 0 < rhoz ∧
      closedBall z rhoz ⊆ closedBall BC.y' BC.sigma ∧ BC.G z = (q : ℝ) := by
  classical
  have hKtarget : closedBall BC.y' BC.sigma ⊆ (extChartAt 𝓘(ℝ, E) old).target :=
    BC.sigma_subset.trans BC.yball
  have hpartK : CalibratedPartners F u old BC.delta (closedBall BC.y' BC.sigma) :=
    BC.reach.mono BC.sigma_subset
  have hxK : x ∈ closedBall BC.y' BC.sigma :=
    hxsub (mem_closedBall_self (by linarith : (0 : ℝ) ≤ 2 * rhox))
  obtain ⟨-, e, hxsrc, -, -, -, hex, hefirst, -⟩ :=
    hF.exists_original_levelCoordinates_of_calibrated_core (u := u)
      (K := closedBall BC.y' BC.sigma) (G := BC.G) (x := x)
      hcomplete old hKtarget hu BC.G_contDiff BC.G_val BC.G_match BC.delta_pos hpartK hxK
  have hxe : e x = (BC.G x, (0 : (fderiv ℝ BC.G x).ker)) := by
    rw [hex]
    exact Prod.ext (BC.G_val hxK).symm rfl
  have hcont : ContinuousAt e.symm (e x) :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (e.map_source hxsrc))
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ :=
    Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxsrc)
  obtain ⟨δε, hδεpos, hδε⟩ := continuousAt_iff.mp hcont (rhox / 2) (by positivity)
  have hδε' : ∀ y : ℝ × (fderiv ℝ BC.G x).ker, dist y (e x) < δε →
      dist (e.symm y) x < rhox / 2 := by
    intro y hy
    have h := hδε (x := y) hy
    rwa [e.left_inv hxsrc] at h
  have hδmpos : 0 < min ε₀ δε := lt_min_iff.mpr ⟨hε₀pos, hδεpos⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show BC.G x - min ε₀ δε < BC.G x by linarith)
  have hqabs : |(q : ℝ) - BC.G x| < min ε₀ δε := by
    rw [abs_of_neg (by linarith : (q : ℝ) - BC.G x < 0)]
    linarith
  have hy'ball : dist ((q : ℝ), (0 : (fderiv ℝ BC.G x).ker)) (e x) < min ε₀ δε := by
    rw [hxe, Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq]
      exact hqabs
    · rw [dist_self]
      exact lt_min_iff.mpr ⟨hε₀pos, hδεpos⟩
  set z : E := e.symm ((q : ℝ), (0 : (fderiv ℝ BC.G x).ker)) with hzdef
  have hytarget : ((q : ℝ), (0 : (fderiv ℝ BC.G x).ker)) ∈ e.target :=
    hε₀sub (mem_ball.mpr (lt_of_lt_of_le hy'ball (min_le_left _ _)))
  have hzball : dist z x < rhox / 2 :=
    hδε' _ (lt_of_lt_of_le hy'ball (min_le_right _ _))
  have hzcore : closedBall z (rhox / 2) ⊆ closedBall BC.y' BC.sigma := by
    intro w hw
    apply hxsub
    rw [mem_closedBall] at hw ⊢
    calc dist w x ≤ dist w z + dist z x := dist_triangle w z x
      _ ≤ rhox / 2 + rhox / 2 := add_le_add hw (le_of_lt hzball)
      _ = rhox := by ring
      _ ≤ 2 * rhox := by linarith
  have hGz : BC.G z = (q : ℝ) := by
    have hez : e z = ((q : ℝ), (0 : (fderiv ℝ BC.G x).ker)) := e.right_inv hytarget
    have h := hefirst z
    rw [hez] at h
    exact h.symm
  exact ⟨z, rhox / 2, q, by linarith, hzcore, hGz⟩

/-! ## The atlas-level field from a compact potential ball core alone -/

/-- **`WindowChartData` from a compact potential ball core alone.**  No open
chart domain, no open-neighbourhood potential or partner extension, and no level
input is required: the open chart ball, the potential and partner restrictions,
the rational level and the level section are all constructed. -/
theorem exists_windowChartData_of_ballCoreData
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {old : M} (BC : BallCorePotentialData (F := F) (u := u) old) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  have hxsub : closedBall BC.y' (2 * (BC.sigma / 4)) ⊆ closedBall BC.y' BC.sigma := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    have h2 : 2 * (BC.sigma / 4) = BC.sigma / 2 := by ring
    rw [h2] at hw
    linarith [BC.sigma_pos]
  obtain ⟨z, rhoz, q, hρ, hzsub, hGz⟩ :=
    exists_rationalLevelPoint_of_ballCore hF hcomplete hu BC BC.y' (BC.sigma / 4)
      (by linarith [BC.sigma_pos]) hxsub
  exact exists_windowChartData_of_ballCore hF hcomplete hu BC q z rhoz hρ hzsub hGz

/-- **The compact producer form without any level input.**  From the compact chart
ball with uniform two-sided reach one obtains the refined C1,1 potential ball core
`G` and a constant window family carrying `WindowChartData`. -/
theorem exists_windowChartData_of_chartBallReach
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {delta : ℝ} (hdelta : 0 < delta)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {rho : ℝ} (hrho : 0 < rho)
    (hyball : closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hreach : CalibratedPartners F u old delta (closedBall y rho)) :
    ∃ (y' : E) (sig : ℝ) (G : E → ℝ) (L : ℝ≥0), 0 < sig ∧
      closedBall y' sig ⊆ closedBall y rho ∧
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧ LipschitzWith L (fderiv ℝ G) ∧
      EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (closedBall y' sig) ∧
      EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm))
        (closedBall y' sig) ∧
      (∀ z ∈ closedBall y' sig,
        HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G z) z) ∧
      ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨y', sig, G, L, hsig, hsub, hG, hsupp, hLip, hval, hmatch, hactual⟩ :=
    exists_ball_core_C11_data (u := u) hF hcomplete old hdelta hu hrho hyball hreach
  let BC : BallCorePotentialData (F := F) (u := u) old :=
    { delta := delta
      delta_pos := hdelta
      y := y
      rho := rho
      rho_pos := hrho
      yball := hyball
      reach := hreach
      y' := y'
      sigma := sig
      sigma_pos := hsig
      sigma_subset := hsub
      G := G
      L := L
      G_contDiff := hG
      G_support := hsupp
      G_lip := hLip
      G_val := hval
      G_match := hmatch
      G_actual := hactual }
  obtain ⟨P, hP⟩ := exists_windowChartData_of_ballCoreData hF hcomplete hu BC
  exact ⟨y', sig, G, L, hsig, hsub, hG, hsupp, hLip, hval, hmatch, hactual, P, hP⟩

end OTSelector.Reconstruction
