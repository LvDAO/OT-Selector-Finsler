import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfiguration.Borel
import OTSelector.PointProcess.LocalConfigurationTestIntegral

/-!
Conditions: A proper metric point space and its actual locally finite integer configurations; the nonnegative-summand lemmas omit properness. The final selected statement uses vague convergence along an arbitrary filter and a site absent from the limit.

Objects: The actual vague topology instance, nonnegative finite test sums, the exact tent integral at an isolated site, and an eventually empty neighborhood of a limit site with zero multiplicity.

Proof detail: Local finiteness isolates the site. A nonnegative compact tent controls nearby integer multiplicities, and convergence of its integral forces the neighborhood eventually to contain no point.

References: Günter Last; Mathew Penrose: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; Günter Last; Mathew Penrose: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
Relation: A local integer-valued test-function argument. Only the selected no-atom exclusion is covered here; the original file’s later simple-atom correspondence and position convergence are outside this selected core.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.PointProcess.LocalConfigurationAtomLimit.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.PointProcess.LocalConfigurationAtomLimit`; the selected original proof blocks follow. -/
section

/-!
# Atom correspondence under actual vague convergence

An isolated simple limit atom has exactly one nearby atom eventually, and that atom
converges in the full point space.  Thus positions and marks converge together.  The
proof uses the defining compactly supported test integrals and integer multiplicities.
-/

open Function Set Filter Topology
open scoped BigOperators Classical CompactlySupported

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] {base : X}

noncomputable local instance atomLimitTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base

omit [ProperSpace X] in
theorem testSummand_nonneg (c : LocalConfiguration base) {f : C_c(X, ℝ)}
    (hf : ∀ x, 0 ≤ f x) (x : X) : 0 ≤ testSummand c f x :=
  mul_nonneg (Nat.cast_nonneg _) (hf x)

omit [ProperSpace X] in
theorem testSummand_le_testIntegral (c : LocalConfiguration base) {f : C_c(X, ℝ)}
    (hf : ∀ x, 0 ≤ f x) (x : X) : testSummand c f x ≤ testIntegral c f :=
  single_le_finsum x (finite_support_testSummand c f) (testSummand_nonneg c hf)



/-- An isolated atom computes the tent integral exactly, including its multiplicity. -/
theorem testIntegral_distanceTent_of_isolated (c : LocalConfiguration base)
    {x : X} {r : ℝ} (hr : 0 < r)
    (hisolate : ∀ y, dist y x < r → y ≠ x → multiplicity c y = 0) :
    testIntegral c (distanceTent x r) = (multiplicity c x : ℝ) * r := by
  have hsum : testIntegral c (distanceTent x r) =
      testSummand c (distanceTent x r) x := by
    apply finsum_eq_single
    intro y hy
    by_cases ht : distanceTent x r y = 0
    · simp [testSummand, ht]
    · simp [testSummand, hisolate y (support_distanceTent_subset_ball x r ht) hy]
  rw [hsum]
  simp [testSummand, distanceTent_apply, hr.le]











/-- A vacant limit site has an eventually vacant neighborhood. -/
theorem eventually_no_atom_near_of_tendsto
    {ι : Type*} {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {x : X} (hx : multiplicity limit x = 0) :
    ∃ r > 0, ∀ᶠ k in l, ∀ y, dist y x < r → multiplicity (c k) y = 0 := by
  obtain ⟨R, hR, hIso⟩ := exists_isolating_ball limit limit x
  have hI : testIntegral limit (distanceTent x R) = 0 := by
    rw [testIntegral_distanceTent_of_isolated limit hR (fun y hy hyx ↦ (hIso y hy hyx).1), hx]
    simp
  have htest := ((continuous_testIntegral (distanceTent x R)).tendsto limit).comp hc
  rw [hI] at htest
  refine ⟨R / 2, by positivity, ?_⟩
  filter_upwards [htest.eventually (gt_mem_nhds (show 0 < R / 2 by positivity))]
    with k hk
  dsimp only [Function.comp_def] at hk
  intro y hy
  by_contra hm
  have hm1 : (1 : ℝ) ≤ multiplicity (c k) y := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
  have hf0 (z : X) : 0 ≤ distanceTent x R z := le_max_left _ _
  have hs := testSummand_le_testIntegral (c k) hf0 y
  have hw : R / 2 < distanceTent x R y := lt_max_of_lt_right (by linarith)
  unfold testSummand at hs
  nlinarith [mul_le_mul_of_nonneg_right hm1 (hf0 y)]





end OTSelector.PointProcess.LocalConfiguration

end
