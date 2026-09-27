import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedAmbientSweepoutConfinement
open PoincareConjecture.ProofContract.Refinement20260927
theorem ambient_sweepout_confinement : AmbientSweepoutConfinementStatement :=
/- SWARM_PROOF_BEGIN -/
open Set in by
  intro n a U hU ha hstrip
  let ca : C(ℝ × PoincareConjecture.ProofContract.V1.Sphere2, ApproxAmbient n) :=
    ⟨a, ha.continuous⟩
  let slices : C(ℝ, C(PoincareConjecture.ProofContract.V1.Sphere2, ApproxAmbient n)) := ca.curry
  let goodSlices : Set C(PoincareConjecture.ProofContract.V1.Sphere2, ApproxAmbient n) :=
    {f | Set.range f ⊆ U}
  have hgoodSlices : IsOpen goodSlices := by
    dsimp [goodSlices]
    exact ContinuousMap.isOpen_setOf_range_subset hU
  let goodTimes : Set ℝ := {s | slices s ∈ goodSlices}
  have hgoodTimes : IsOpen goodTimes := hgoodSlices.preimage slices.continuous
  have hgoodTimes_iff (s : ℝ) : s ∈ goodTimes ↔ ∀ p, a (s, p) ∈ U := by
    constructor
    · intro hs p
      change Set.range (slices s) ⊆ U at hs
      have hp : slices s p ∈ Set.range (slices s) := ⟨p, rfl⟩
      simpa [slices, ca, ContinuousMap.curry_apply] using hs hp
    · intro hs
      change Set.range (slices s) ⊆ U
      rintro y ⟨p, rfl⟩
      simpa [slices, ca, ContinuousMap.curry_apply] using hs p
  have hstripTimes : ∀ s, s ∈ Icc (0 : ℝ) 1 → s ∈ goodTimes := by
    intro s hs
    rw [hgoodTimes_iff]
    intro p
    exact hstrip (s, p) hs
  have hzero : (0 : ℝ) ∈ goodTimes := hstripTimes 0 (by norm_num)
  have hone : (1 : ℝ) ∈ goodTimes := hstripTimes 1 (by norm_num)
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp hgoodTimes 0 hzero
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp hgoodTimes 1 hone
  let J : Set ℝ := Ioo (-ε₀) (1 + ε₁)
  have hJ : ∀ s, s ∈ J → s ∈ goodTimes := by
    intro s hs
    by_cases hsneg : s < 0
    · have habs : |s| < ε₀ := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hsneg, hε₀]⟩
      have hsball : s ∈ Metric.ball (0 : ℝ) ε₀ := by
        simpa [Metric.mem_ball, Real.dist_eq] using habs
      exact hball₀ hsball
    · by_cases hsle : s ≤ 1
      · exact hstripTimes s ⟨le_of_not_gt hsneg, hsle⟩
      · have hsone : 1 < s := lt_of_not_ge hsle
        have habs : |s - 1| < ε₁ := abs_lt.mpr ⟨by linarith [hsone], by linarith [hs.2]⟩
        have hsball : s ∈ Metric.ball (1 : ℝ) ε₁ := by
          simpa [Metric.mem_ball, Real.dist_eq] using habs
        exact hball₁ hsball
  let K : Set ℝ := Ioo (-(ε₀ / 2)) (1 + ε₁ / 2)
  have hKends : -(ε₀ / 2) < 1 + ε₁ / 2 := by linarith [hε₀, hε₁]
  have hstripK : Icc (0 : ℝ) 1 ⊆ K := by
    intro s hs
    change -(ε₀ / 2) < s ∧ s < 1 + ε₁ / 2
    constructor <;> nlinarith [hε₀, hε₁, hs.1, hs.2]
  have hKclosure : closure K ⊆ J := by
    change closure (Ioo (-(ε₀ / 2)) (1 + ε₁ / 2)) ⊆ Ioo (-ε₀) (1 + ε₁)
    rw [closure_Ioo hKends.ne]
    intro s hs
    change -ε₀ < s ∧ s < 1 + ε₁
    constructor <;> nlinarith [hε₀, hε₁, hs.1, hs.2]
  have hKclosedComplement : IsClosed Kᶜ := isOpen_Ioo.isClosed_compl
  have hdisjoint : Disjoint Kᶜ (Icc (0 : ℝ) 1) := by
    apply Set.disjoint_left.mpr
    intro s hs hstrip
    exact hs (hstripK hstrip)
  have hchiExists :
      ∃ f : ContMDiffMap (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) ℝ ℝ
          (↑(⊤ : ℕ∞)),
        EqOn f 0 Kᶜ ∧ EqOn f 1 (Icc (0 : ℝ) 1) ∧ ∀ x, f x ∈ Icc 0 1 := by
    exact exists_contMDiffMap_zero_one_of_isClosed (modelWithCornersSelf ℝ ℝ)
      hKclosedComplement isClosed_Icc hdisjoint (n := (⊤ : ℕ∞))
  obtain ⟨chiMap, hchiZero, hchiOne, hchiRange⟩ := hchiExists
  let chi : ℝ → ℝ := chiMap
  have hchiSmooth : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞)) chi :=
    chiMap.contMDiff
  have hchi_zero (s : ℝ) (hs : s ∉ K) : chi s = 0 := hchiZero hs
  have hchi_one (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : chi s = 1 := hchiOne hs
  have hchi_bounds (s : ℝ) : 0 ≤ chi s ∧ chi s ≤ 1 := hchiRange s
  have hchiPointSupport : Function.support chi ⊆ K := by
    intro s hs
    by_contra hnot
    exact hs (hchi_zero s hnot)
  have hchiSupport : tsupport chi ⊆ J := by
    calc
      tsupport chi = closure (Function.support chi) := rfl
      _ ⊆ closure K := closure_mono hchiPointSupport
      _ ⊆ J := hKclosure
  let sigma : ℝ → ℝ := fun s => chi s * s + (1 - chi s) * (1 / 2)
  have hsigmaSmooth : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞)) sigma := by
    dsimp [sigma]
    exact (hchiSmooth.mul contMDiff_id).add
      ((contMDiff_const.sub hchiSmooth).mul contMDiff_const)
  have hmidJ : (1 / 2 : ℝ) ∈ J := by
    change -ε₀ < 1 / 2 ∧ 1 / 2 < 1 + ε₁
    constructor <;> linarith [hε₀, hε₁]
  have hsigmaJ (s : ℝ) : sigma s ∈ J := by
    by_cases hzeroChi : chi s = 0
    · simpa [sigma, hzeroChi] using hmidJ
    · have hsJ : s ∈ J := hchiSupport (subset_closure hzeroChi)
      change -ε₀ < chi s * s + (1 - chi s) * (1 / 2) ∧
        chi s * s + (1 - chi s) * (1 / 2) < 1 + ε₁
      have hχ0 : 0 ≤ chi s := (hchi_bounds s).1
      have hχ1 : 0 ≤ 1 - chi s := by linarith [(hchi_bounds s).2]
      constructor
      · have hsum : 0 < chi s * (s + ε₀) + (1 - chi s) * (1 / 2 + ε₀) := by
          have hleft : 0 < s + ε₀ := by linarith [hsJ.1]
          have hright : 0 < (1 / 2 : ℝ) + ε₀ := by linarith [hmidJ.1]
          nlinarith [mul_nonneg hχ0 hleft.le, mul_nonneg hχ1 hright.le]
        nlinarith [hsum]
      · have hsum : 0 < chi s * (1 + ε₁ - s) + (1 - chi s) * (1 + ε₁ - 1 / 2) := by
          have hleft : 0 < 1 + ε₁ - s := by linarith [hsJ.2]
          have hright : 0 < (1 : ℝ) + ε₁ - 1 / 2 := by linarith [hε₁]
          nlinarith [mul_nonneg hχ0 hleft.le, mul_nonneg hχ1 hright.le]
        nlinarith [hsum]
  have hsigma_eq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : sigma s = s := by
    simp [sigma, hchi_one s hs]
  let timeMap : ℝ × PoincareConjecture.ProofContract.V1.Sphere2 →
      ℝ × PoincareConjecture.ProofContract.V1.Sphere2 := fun q => (sigma q.1, q.2)
  have htimeMap : ContMDiff SweepModel SweepModel (↑(⊤ : ℕ∞)) timeMap := by
    dsimp [timeMap]
    exact (hsigmaSmooth.comp contMDiff_fst).prodMk contMDiff_snd
  let b : ℝ × PoincareConjecture.ProofContract.V1.Sphere2 → ApproxAmbient n := a ∘ timeMap
  refine ⟨b, ?_, ?_, ?_⟩
  · exact ha.comp htimeMap
  · intro q hq
    change a (sigma q.1, q.2) = a (q.1, q.2)
    exact congrArg (fun t : ℝ => a (t, q.2)) (hsigma_eq q.1 hq.1)
  · intro q
    change a (sigma q.1, q.2) ∈ U
    exact (hgoodTimes_iff (sigma q.1)).mp
      (hJ (sigma q.1) (hsigmaJ q.1)) q.2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedAmbientSweepoutConfinement
