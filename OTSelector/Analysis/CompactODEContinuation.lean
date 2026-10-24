import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.ExtendFrom

/-!
## Lemma skeleton

* **Conditions:** A continuous vector field and a solution confined to a compact set; C1 on an open neighborhood for continuation.
* **Objects:** An actual finite-time endpoint and an extension past it.
* **Proof detail:** Bound the velocity on the compact range, construct the endpoint, solve locally there and glue.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, finite-time continuation in a compact set.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63

**Relationship to the sources:** The book gives the finite-dimensional ODE criterion; the normed-space compact-range formulation, endpoint derivative and left-time version are proved here.
-/

/-!
# Continuation of integral curves with compact range

An actual integral curve of a continuous autonomous field whose range stays in a
compact set has a continuous finite-time endpoint in that set. Its derivative extends
from the left by the original vector field. If the field is C1 on an open neighborhood,
local existence through this derived endpoint and one-sided differentiation give a
continuation past the finite right endpoint; time reversal gives the left continuation.
No endpoint state, uniform existence time,
minimizing property, or extension of the vector field outside its domain is assumed.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Compact range and continuity of the actual field supply an endpoint in the same compact
set, together with the original one-sided ODE at the finite right endpoint. -/
theorem exists_integralCurve_compact_right_endpoint
    {X : E → E} {K : Set E} (hK : IsCompact K) (hX : ContinuousOn X K)
    {γ : ℝ → E} {a b : ℝ} (hab : a < b) (hmap : MapsTo γ (Ioo a b) K)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (X (γ t)) t) :
    ∃ β : ℝ → E, ContinuousOn β (Icc a b) ∧ EqOn β γ (Ioo a b) ∧
      MapsTo β (Icc a b) K ∧ HasDerivWithinAt β (X (β b)) (Iic b) b := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hX.norm
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hlip : LipschitzOnWith L γ (Ioo a b) :=
    (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht ↦ (hγ t ht).hasDerivWithinAt) (fun t ht ↦ by
        apply NNReal.coe_le_coe.mp
        exact (hC (mem_image_of_mem _ (hmap ht))).trans (le_max_left _ _))
  let β := extendFrom (Ioo a b) γ
  have heq : EqOn β γ (Ioo a b) := extendFrom_extends hlip.continuousOn
  have hcont : ContinuousOn β (Icc a b) := by
    apply continuousOn_extendFrom
    · rw [closure_Ioo hab.ne]
    · intro t ht
      have hcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
      have : NeBot (𝓝[Ioo a b] t) := mem_closure_iff_nhdsWithin_neBot.mp hcl
      apply cauchy_map_iff_exists_tendsto.mp
      have hn : Cauchy (𝓝[Ioo a b] t) := cauchy_nhds.mono nhdsWithin_le_nhds
      exact hn.map_of_le hlip.uniformContinuousOn inf_le_right
  have hβmap : MapsTo β (Icc a b) K := by
    have hm : MapsTo β (Ioo a b) K := fun t ht ↦ by rw [heq ht]; exact hmap ht
    have hc : ContinuousOn β (closure (Ioo a b)) := by rwa [closure_Ioo hab.ne]
    simpa only [closure_Ioo hab.ne, hK.isClosed.closure_eq] using
      hm.closure_of_continuousOn hc
  have hβd : ∀ t ∈ Ioo a b, HasDerivAt β (X (β t)) t := by
    intro t ht
    have hevent : β =ᶠ[𝓝 t] γ :=
      eventually_of_mem (isOpen_Ioo.mem_nhds ht) fun u hu ↦ heq hu
    rw [heq ht]
    exact (hγ t ht).congr_of_eventuallyEq hevent
  have hlim : Tendsto (fun t ↦ X (β t)) (𝓝[<] b) (𝓝 (X (β b))) := by
    have hc := ((hX.comp hcont hβmap) b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hab, Function.comp_def] using hc
  have hlimd : Tendsto (deriv β) (𝓝[<] b) (𝓝 (X (β b))) :=
    hlim.congr' (by
      filter_upwards [Ioo_mem_nhdsLT hab] with t ht
      exact (hβd t ht).deriv.symm)
  refine ⟨β, hcont, heq, hβmap, ?_⟩
  exact hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun t ht ↦ (hβd t ht).differentiableAt.differentiableWithinAt)
    ((hcont b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab) hlimd

/-- A C1 autonomous field on an open set continues every actual solution with compact range
past its finite right endpoint. The extended curve agrees on the whole original interval. -/
theorem exists_integralCurve_extension_right_of_compact
    {X : E → E} {U K : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {γ : ℝ → E} {a b : ℝ} (hab : a < b) (hmap : MapsTo γ (Ioo a b) K)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (X (γ t)) t) :
    ∃ δ > (0 : ℝ), ∃ γbar : ℝ → E, EqOn γbar γ (Ioo a b) ∧
      MapsTo γbar (Ioo a (b + δ)) U ∧
      ∀ t ∈ Ioo a (b + δ), HasDerivAt γbar (X (γbar t)) t := by
  classical
  obtain ⟨β, _, hβeq, hβmap, hβd⟩ :=
    exists_integralCurve_compact_right_endpoint hK (hX.continuousOn.mono hKU) hab hmap hγ
  have hbU : β b ∈ U := hKU (hβmap ⟨hab.le, le_rfl⟩)
  have hXp : ContDiffAt ℝ 1 X (β b) := hX.contDiffAt (hU.mem_nhds hbU)
  obtain ⟨α, hα₀, ε, hε, hα⟩ :=
    hXp.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ b
  have hbε : b ∈ Ioo (b - ε) (b + ε) := ⟨by linarith, by linarith⟩
  have hstay : ∀ᶠ t in 𝓝 b, α t ∈ U :=
    (hα b hbε).continuousAt.preimage_mem_nhds (by simpa [hα₀] using hU.mem_nhds hbU)
  obtain ⟨η, hη, hηstay⟩ := Metric.eventually_nhds_iff_ball.mp hstay
  let δ := min ε η
  have hδ : 0 < δ := lt_min hε hη
  have hδε : δ ≤ ε := min_le_left _ _
  have hδη : δ ≤ η := min_le_right _ _
  let γbar : ℝ → E := fun t ↦ if t < b then γ t else α t
  have hbarb : γbar b = β b := by simp [γbar, hα₀]
  have hleft : HasDerivWithinAt γbar (X (β b)) (Iic b) b := by
    apply hβd.congr_of_eventuallyEq _ hbarb
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hab), self_mem_nhdsWithin] with t hat htb
    by_cases htb' : t < b
    · simpa [γbar, htb'] using (hβeq ⟨hat, htb'⟩).symm
    · have htb'' : t = b := le_antisymm htb (le_of_not_gt htb')
      simpa [htb''] using hbarb
  have hright : HasDerivWithinAt γbar (X (β b)) (Ici b) b := by
    have hd := (hα b hbε).hasDerivWithinAt (s := Ici b)
    rw [hα₀] at hd
    apply hd.congr_of_mem _ (mem_Ici.mpr le_rfl)
    intro t ht
    simp [γbar, not_lt_of_ge (mem_Ici.mp ht)]
  have hbarbd : HasDerivAt γbar (X (γbar b)) b := by
    rw [hbarb]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright
  refine ⟨δ, hδ, γbar, ?_, ?_, ?_⟩
  · intro t ht
    simp [γbar, ht.2]
  · intro t ht
    by_cases htb : t < b
    · simpa [γbar, htb] using hKU (hmap ⟨ht.1, htb⟩)
    · simp only [γbar, ite_eq_right htb]
      apply hηstay
      rw [Real.ball_eq_Ioo]
      constructor <;> linarith [ht.2]
  · intro t ht
    rcases lt_trichotomy t b with htb | rfl | hbt
    · have heq : γbar =ᶠ[𝓝 t] γ :=
        eventually_of_mem (Iio_mem_nhds htb) fun u hu ↦ by simp [γbar, mem_Iio.mp hu]
      simpa only [γbar, ite_eq_left htb] using (hγ t ⟨ht.1, htb⟩).congr_of_eventuallyEq heq
    · exact hbarbd
    · have heq : γbar =ᶠ[𝓝 t] α :=
        eventually_of_mem (Ioi_mem_nhds hbt) fun u hu ↦ by simp [γbar, not_lt_of_gt (mem_Ioi.mp hu)]
      have htε : t ∈ Ioo (b - ε) (b + ε) := by
        constructor <;> linarith [ht.2]
      simpa only [γbar, ite_eq_right (not_lt_of_gt hbt)] using
        (hα t htε).congr_of_eventuallyEq heq

/-- Time reversal also continues a compact-range integral curve past its finite left endpoint. -/
theorem exists_integralCurve_extension_left_of_compact
    {X : E → E} {U K : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {γ : ℝ → E} {a b : ℝ} (hab : a < b) (hmap : MapsTo γ (Ioo a b) K)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (X (γ t)) t) :
    ∃ δ > (0 : ℝ), ∃ γbar : ℝ → E, EqOn γbar γ (Ioo a b) ∧
      MapsTo γbar (Ioo (a - δ) b) U ∧
      ∀ t ∈ Ioo (a - δ) b, HasDerivAt γbar (X (γbar t)) t := by
  have hnegmap : MapsTo (fun t ↦ γ (-t)) (Ioo (-b) (-a)) K := by
    intro t ht
    exact hmap ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hnegγ : ∀ t ∈ Ioo (-b) (-a),
      HasDerivAt (fun s ↦ γ (-s)) (-X (γ (-t))) t := by
    intro t ht
    have hd := (hγ (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).scomp t
      (hasDerivAt_neg t)
    simpa only [Function.comp_def, neg_smul, one_smul] using hd
  obtain ⟨δ, hδ, β, hβeq, hβmap, hβd⟩ :=
    exists_integralCurve_extension_right_of_compact hU hX.neg hK hKU
      (neg_lt_neg hab) hnegmap hnegγ
  refine ⟨δ, hδ, fun t ↦ β (-t), ?_, ?_, ?_⟩
  · intro t ht
    simpa only [neg_neg] using hβeq
      (show -t ∈ Ioo (-b) (-a) from ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  · intro t ht
    exact hβmap ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro t ht
    have hd := (hβd (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).scomp t
      (hasDerivAt_neg t)
    simpa only [Function.comp_def, neg_smul, one_smul, neg_neg] using hd

end OTSelector.Geometry
