import PoincareConjecture.ProofContract.Refinement20260927.MinimaxComparison
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RefinedMinimaxDiniLimit
open PoincareConjecture.ProofContract.Refinement20260927
theorem minimax_dini_limit : MinimaxDiniLimitStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro w m t a b hm hunif
  intro r hr
  let base : ℝ := -a + b * w t
  let gap : ℝ := r - base
  have hgap : 0 < gap := by
    dsimp [gap, base]
    linarith
  obtain ⟨eta, heta, hetagap⟩ := exists_between (show (0 : ℝ) < gap by exact hgap)
  obtain ⟨J, H, K, hH, hK, hbound⟩ := hunif eta heta
  have hmargin : 0 < gap - eta := by linarith
  let d : ℝ := min H ((gap - eta) / (K + 1))
  have hd : 0 < d := by
    dsimp [d]
    apply lt_min hH
    apply div_pos hmargin
    linarith
  have hdH : d ≤ H := min_le_left _ _
  -- For each fixed positive step, the uniform estimate passes to the limit in m.
  have hfixed : ∀ h : ℝ, 0 < h → h < d →
      w (t + h) ≤ w t + h * (-a + b * w t + eta) + K * h ^ 2 := by
    intro h hh hhD
    let f : ℝ → ℝ := fun x => x + h * (-a + b * x + eta) + K * h ^ 2
    have hf : Continuous f := by
      dsimp [f]
      fun_prop
    have hlim : Filter.Tendsto (fun j => f (m j)) Filter.atTop (nhds (f (w t))) :=
      hf.continuousAt.tendsto.comp hm
    have hhH : h < H := lt_of_lt_of_le hhD hdH
    have hpoint : ∀ᶠ j : ℕ in Filter.atTop, w (t + h) ≤ f (m j) := by
      filter_upwards [Filter.eventually_atTop.2 ⟨J, fun j hj => by
        simpa [f] using hbound j hj h hh hhH⟩] with j hj
      exact hj
    have hneg := hlim.neg
    have hnegpoint : ∀ᶠ j : ℕ in Filter.atTop, -(f (m j)) ≤ -(w (t + h)) := by
      filter_upwards [hpoint] with j hj
      exact neg_le_neg hj
    have hlimle := le_of_tendsto hneg hnegpoint
    have hle : w (t + h) ≤ f (w t) := by linarith
    simpa [f] using hle
  have hpointSlope : ∀ h : ℝ, 0 < h → h < d → slope w t (t + h) < r := by
    intro h hh hhD
    have hlim := hfixed h hh hhD
    have hsmallDiv : h < (gap - eta) / (K + 1) :=
      lt_of_lt_of_le hhD (min_le_right _ _)
    have hKpos : 0 < K + 1 := by linarith
    have hsmall : (K + 1) * h < gap - eta :=
      by simpa [mul_comm] using (lt_div_iff₀ hKpos).mp hsmallDiv
    have hKsmall : K * h < gap - eta := by nlinarith
    have hdiff : w (t + h) - w t ≤ h * (-a + b * w t + eta + K * h) := by
      nlinarith [hlim]
    have hslope : slope w t (t + h) ≤ -a + b * w t + eta + K * h := by
      rw [slope]
      change ((t + h - t)⁻¹) * (w (t + h) - w t) ≤ _
      rw [show t + h - t = h by ring]
      rw [show h⁻¹ * (w (t + h) - w t) = (w (t + h) - w t) / h by
        rw [div_eq_mul_inv]
        ring]
      exact (div_le_iff₀ hh).2 (by nlinarith [hdiff])
    have hstrict : -a + b * w t + eta + K * h < r := by
      dsimp [base, gap] at hgap ⊢
      linarith
    exact hslope.trans_lt hstrict
  have hnhds : Set.Ioo (t - d) (t + d) ∈ nhds t := by
    apply Ioo_mem_nhds <;> linarith
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnhds,
    self_mem_nhdsWithin] with z hz hzgt
  change t < z at hzgt
  have hzpos : 0 < z - t := by linarith
  have hzd : z - t < d := by linarith [hz.2]
  simpa only [show t + (z - t) = z by ring] using hpointSlope (z - t) hzpos hzd
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedMinimaxDiniLimit
