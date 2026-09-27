import PoincareConjecture.ProofContract.Refinement20260927.ExtinctionBarrier
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RefinedWidthDiniComparison
open PoincareConjecture.ProofContract.Refinement20260927
theorem width_dini_comparison : WidthIntervalComparisonStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro a c s t w ha hc hs hst hw hfd
  let ψ : ℝ → ℝ → ℝ := fun r y => -a + 3 / (4 * (r + c)) * y
  let P : ℝ := widthPotential a c s (w s)
  let G : ℝ → ℝ := fun r => P * (r + c) ^ ((3 : ℝ) / 4) - 4 * a * (r + c)
  have hs0 : 0 < s + c := by linarith
  have ht0 : 0 < t + c := by linarith
  have hpow_mul (x : ℝ) (hx : 0 < x) :
      x ^ ((1 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) = x := by
    rw [← Real.rpow_add hx]
    norm_num [Real.rpow_one]
  have hGs : G s = w s := by
    have hq : (s + c) ^ ((3 : ℝ) / 4) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hs0 _)
    dsimp [G, P, widthPotential]
    rw [add_mul, div_mul_cancel₀ _ hq]
    rw [mul_assoc, hpow_mul (s + c) hs0]
    ring
  have hfd' : ∀ r ∈ Set.Ico s t,
      MorganTianLib.ForwardDiffQuotientLE w r (ψ r (w r)) := by
    intro r hr
    simpa [ψ] using hfd r hr
  have hψ : ContDiffOn ℝ 1 (Function.uncurry ψ)
      (Set.Icc s t ×ˢ Set.univ) := by
    let D : Set (ℝ × ℝ) := Set.Icc s t ×ˢ Set.univ
    have hden : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => 4 * (z.1 + c)) D := by
      fun_prop
    have hden_ne : ∀ z ∈ D, 4 * (z.1 + c) ≠ 0 := by
      intro z hz
      have hz₁ : z.1 ∈ Set.Icc s t := hz.1
      have : 0 < z.1 + c := by linarith [hz₁.1]
      positivity
    have hfrac : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => (3 : ℝ) / (4 * (z.1 + c))) D :=
      contDiffOn_const.div hden hden_ne
    change ContDiffOn ℝ 1
      (fun z : ℝ × ℝ => -a + (3 / (4 * (z.1 + c))) * z.2) D
    exact contDiffOn_const.neg.add (hfrac.mul contDiffOn_snd)
  have hGcont : ContinuousOn G (Set.Icc s t) := by
    have hbase : ContinuousOn (fun r : ℝ => r + c) (Set.Icc s t) :=
      continuousOn_id.add continuousOn_const
    have hpow : ContinuousOn (fun r : ℝ => (r + c) ^ ((3 : ℝ) / 4))
        (Set.Icc s t) :=
      hbase.rpow_const (fun _ _ => Or.inr (by norm_num : 0 ≤ (3 : ℝ) / 4))
    dsimp [G]
    exact (continuousOn_const.mul hpow).sub (continuousOn_const.mul hbase)
  have hGderiv : ∀ r ∈ Set.Ico s t,
      HasDerivWithinAt G (ψ r (G r)) (Set.Ici r) r := by
    intro r hr
    have hr0 : 0 < r + c := by
      have hrleft : s ≤ r := hr.1
      linarith
    have hbase : HasDerivAt (fun x : ℝ => x + c) 1 r := by
      simpa using (hasDerivAt_id r).add_const c
    have hpow : HasDerivAt (fun x : ℝ => (x + c) ^ ((3 : ℝ) / 4))
        (((3 : ℝ) / 4) * (r + c) ^ ((3 : ℝ) / 4 - 1)) r := by
      simpa using hbase.rpow_const (Or.inl hr0.ne')
    have hGd : HasDerivAt G
        (P * (((3 : ℝ) / 4) * (r + c) ^ ((3 : ℝ) / 4 - 1)) - (4 * a) * 1) r := by
      dsimp [G]
      convert! (hpow.const_mul P).sub (hbase.const_mul (4 * a)) using 1
    have heq : P * (((3 : ℝ) / 4) * (r + c) ^ ((3 : ℝ) / 4 - 1)) - (4 * a) * 1 =
        ψ r (G r) := by
      dsimp [ψ, G]
      rw [Real.rpow_sub hr0 ((3 : ℝ) / 4) 1, Real.rpow_one]
      field_simp [ne_of_gt hr0]
      ring
    rw [← heq]
    exact hGd.hasDerivWithinAt
  have hGs_le : w s ≤ G s := by rw [hGs]
  have hwt : w t ≤ G t := by
    exact (MorganTianLib.le_of_forwardDiffQuotientLE hw hfd' hψ hGcont
      hGderiv hGs_le) t ⟨le_of_lt hst, le_rfl⟩
  let p : ℝ := (t + c) ^ ((1 : ℝ) / 4)
  let q : ℝ := (t + c) ^ ((3 : ℝ) / 4)
  have hcross : p * q = t + c := by
    dsimp [p, q]
    exact hpow_mul (t + c) ht0
  have hwt' : w t ≤ P * q - 4 * a * (t + c) := by
    simpa [G, q] using hwt
  have hnum : w t + (4 * a * p) * q ≤ P * q := by
    nlinarith [hwt', hcross]
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos ht0 _
  have hdiv : w t / q ≤ P - (4 * a) * p :=
    (div_le_iff₀ hqpos).2 (by nlinarith [hnum])
  change w t / q + (4 * a) * p ≤ P
  linarith
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedWidthDiniComparison
