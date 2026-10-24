import OTSelector.Analysis.Calculus.ParameterizedStationaryTaylor
import OTSelector.Analysis.Calculus.UniformSecondJetTransfer
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformParameterizedActionTransfer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformParameterizedActionTransfer`; the selected original proof blocks follow. -/
section

/-!
Conditions: A compact C3 stationary action family, uniformly O(scale) states and an o(scale) mismatch, with any admissibility predicate stated in the signature.

Objects: Uniform o(scale²) action transfer between the two states.

Proof detail: Expand both actions to quadratic order, bound the bilinear diagonal difference by displacement times mismatch and absorb the cubic remainders.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Locally proved quantitative composition result; it preserves the allowed-state predicate and the stated scaling.
-/

/-!
# Uniform transfer for a single parameterized stationary action

Pointwise C3 regularity at a compact family of centers supplies the common action
remainders and bounded actual Hessians. The caller supplies only the sizes and
uniform first-order mismatch of its endpoint maps; no action remainder or
second-order comparison is assumed.
-/

open Set
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {P E I T : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- One common action transfers uniformly across first-order matching state maps.
The compact center set may be disconnected and the index set arbitrary. -/
theorem uniform_parameterized_stationary_action_transfer
    {f : P × E → ℝ} {K : Set (P × E)} (hK : IsCompact K)
    (hf : ∀ z ∈ K, ContDiffAt ℝ 3 f z)
    (hstationary : ∀ z ∈ K, ∀ h : E, fderiv ℝ f z (0, h) = 0)
    (S : Set I) (z : I → P × E) (hz : ∀ i ∈ S, z i ∈ K)
    (X Y : I → T → E) (scale : T → ℝ) (hscale : ∀ t, 0 ≤ scale t)
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hsize : ∀ i ∈ S, ∀ t, scale t < R →
      ‖X i t - (z i).2‖ ≤ L * scale t ∧ ‖Y i t - (z i).2‖ ≤ L * scale t)
    (hmismatch : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r →
      ‖X i t - Y i t‖ ≤ η * scale t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r →
      ‖f ((z i).1, X i t) - f ((z i).1, Y i t)‖ ≤ ε * (scale t) ^ 2 := by
  let U : Set (P × E) := {q | ContDiffAt ℝ 3 f q}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun q hq ↦
    (show ContDiffAt ℝ 3 f q from hq).eventually (by norm_num)
  have hfU : ContDiffOn ℝ 3 f U := fun q hq ↦
    (show ContDiffAt ℝ 3 f q from hq).contDiffWithinAt
  have hD : ContDiffOn ℝ 2 (fderiv ℝ f) U :=
    hfU.fderiv_of_isOpen hU (by norm_num)
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ f)) K :=
    (hD.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hf
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ f)) hH
  let X' : I → T → P × E := fun i t ↦ ((z i).1, X i t)
  let Y' : I → T → P × E := fun i t ↦ ((z i).1, Y i t)
  have hsize' : ∀ i ∈ S, ∀ t, scale t < R →
      ‖X' i t - z i‖ ≤ L * scale t ∧ ‖Y' i t - z i‖ ≤ L * scale t := by
    intro i hi t ht
    simpa [X', Y', Prod.norm_def] using hsize i hi t ht
  apply uniform_stationary_peano_transfer S (fun _ ↦ f) z
    (fun i ↦ fderiv ℝ (fderiv ℝ f) (z i)) X' Y' scale
    (K := max B 0) (le_max_right _ _) hL hR
    (fun i hi ↦ (hB _ (hz i hi)).trans (le_max_left _ _)) hsize' ?_ hε
  intro η hη
  obtain ⟨rA, hrA, hrem⟩ :=
    exists_uniform_parameterized_stationary_remainder_of_contDiffAt hK hf hstationary hη
  obtain ⟨rM, hrM, hmatch⟩ := hmismatch η hη
  have hL1 : 0 < L + 1 := by linarith
  refine ⟨min R (min rM (rA / (L + 1))),
    lt_min hR (lt_min hrM (div_pos hrA hL1)), ?_⟩
  intro i hi t ht
  have htR := ht.trans_le (min_le_left _ _)
  have htM := (ht.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have htA := (lt_div_iff₀ hL1).mp
    ((ht.trans_le (min_le_right _ _)).trans_le (min_le_right _ _))
  obtain ⟨hX, hY⟩ := hsize i hi t htR
  have hXr : ‖X i t - (z i).2‖ < rA := by nlinarith [hscale t]
  have hYr : ‖Y i t - (z i).2‖ < rA := by nlinarith [hscale t]
  refine ⟨?_, ?_, ?_⟩
  · simpa [X', Y', Prod.norm_def] using hmatch i hi t htM
  · have hdiff : X' i t - z i = (0, X i t - (z i).2) := by
      ext <;> simp [X']
    rw [hdiff]
    simpa [X', Prod.norm_def] using hrem (z i) (hz i hi) (X i t - (z i).2) hXr
  · have hdiff : Y' i t - z i = (0, Y i t - (z i).2) := by
      ext <;> simp [Y']
    rw [hdiff]
    simpa [Y', Prod.norm_def] using hrem (z i) (hz i hi) (Y i t - (z i).2) hYr

/-- Uniform transfer restricted to the original allowed parameters. Extending both
maps by their common center outside that set introduces no regularity requirement. -/
theorem uniform_parameterized_stationary_action_transfer_within
    {f : P × E → ℝ} {K : Set (P × E)} (hK : IsCompact K)
    (hf : ∀ z ∈ K, ContDiffAt ℝ 3 f z)
    (hstationary : ∀ z ∈ K, ∀ h : E, fderiv ℝ f z (0, h) = 0)
    (S : Set I) (z : I → P × E) (hz : ∀ i ∈ S, z i ∈ K)
    (X Y : I → T → E) (scale : T → ℝ) (hscale : ∀ t, 0 ≤ scale t)
    (allowed : I → T → Prop)
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hsize : ∀ i ∈ S, ∀ t, scale t < R → allowed i t →
      ‖X i t - (z i).2‖ ≤ L * scale t ∧ ‖Y i t - (z i).2‖ ≤ L * scale t)
    (hmismatch : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r →
      allowed i t → ‖X i t - Y i t‖ ≤ η * scale t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r → allowed i t →
      ‖f ((z i).1, X i t) - f ((z i).1, Y i t)‖ ≤ ε * (scale t) ^ 2 := by
  classical
  let X' : I → T → E := fun i t ↦ if allowed i t then X i t else (z i).2
  let Y' : I → T → E := fun i t ↦ if allowed i t then Y i t else (z i).2
  have hsize' : ∀ i ∈ S, ∀ t, scale t < R →
      ‖X' i t - (z i).2‖ ≤ L * scale t ∧ ‖Y' i t - (z i).2‖ ≤ L * scale t := by
    intro i hi t ht
    by_cases ha : allowed i t
    · simpa only [X', Y', if_pos ha] using hsize i hi t ht ha
    · simpa only [X', Y', if_neg ha, sub_self, norm_zero, and_self] using
        mul_nonneg hL (hscale t)
  have hmatch' : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ t, scale t < r →
      ‖X' i t - Y' i t‖ ≤ η * scale t := by
    intro η hη
    obtain ⟨r, hr, hb⟩ := hmismatch η hη
    refine ⟨r, hr, ?_⟩
    intro i hi t ht
    by_cases ha : allowed i t
    · simpa only [X', Y', if_pos ha] using hb i hi t ht ha
    · simpa only [X', Y', if_neg ha, sub_self, norm_zero] using
        mul_nonneg hη.le (hscale t)
  obtain ⟨r, hr, hb⟩ := uniform_parameterized_stationary_action_transfer
    hK hf hstationary S z hz X' Y' scale hscale hL hR hsize' hmatch' hε
  exact ⟨r, hr, fun i hi t ht ha ↦ by
    simpa only [X', Y', if_pos ha] using hb i hi t ht⟩

end OTSelector.Geometry

end
end
