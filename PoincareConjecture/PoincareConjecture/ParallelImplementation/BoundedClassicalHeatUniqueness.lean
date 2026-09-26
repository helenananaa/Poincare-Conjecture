import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BoundedClassicalHeatUniqueness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The bounded classical heat operator has trivial kernel on actual zero-initial-trace jets.
No mild representation, higher time derivatives or uniqueness hypothesis is supplied. -/
theorem zero_initial_heat_jet_eq_zero
    (T alpha : ℝ) (hT : 0 < T) (z : FullJet T)
    (hz : z ∈ fullParabolicJetSet T alpha hT.le)
    (hheat : ∀ p : Slab T,
      z.1.2 p = ∑ i : Fin 3,
        z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) :
    z = 0 :=
/- SWARM_PROOF_BEGIN -/
by
  have localMax_second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
      (hmax : IsLocalMax f x) (hcont : ContinuousAt f x) :
      deriv (deriv f) x ≤ 0 := by
    by_contra hn
    have hpos : deriv (deriv f) x > 0 := lt_of_not_ge hn
    have hmin : IsLocalMin f x :=
      isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hcont
    have hconst : f =ᶠ[𝓝 x] fun _ => f x := by
      filter_upwards [hmax, hmin] with y hymax hymin
      exact le_antisymm hymax hymin
    have hderiv : deriv f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      simpa using hconst.deriv
    have hzero := hderiv.deriv_eq
    have : deriv (deriv f) x = 0 := by simpa using hzero
    linarith
  have line_second_deriv {f : E3 → ℝ} {x e : E3}
      (hf : ContDiff ℝ 2 f) :
      HasDerivAt (deriv (fun s : ℝ => f (x + s • e)))
        (fderiv ℝ (fderiv ℝ f) x e e) 0 := by
    let line : ℝ → E3 := fun s => x + s • e
    let g : ℝ → ℝ := fun s => f (line s)
    have hline (s : ℝ) : HasDerivAt line e s := by
      simpa [line] using ((hasDerivAt_id s).smul_const e).const_add x
    have hfirst (s : ℝ) :
        HasDerivAt g (fderiv ℝ f (line s) e) s := by
      have hf' : HasFDerivAt f (fderiv ℝ f (line s)) (line s) :=
        (hf.differentiable (by norm_num) (line s)).hasFDerivAt
      have h := hf'.comp_hasDerivAt s (hline s)
      simpa [g, line, Function.comp_def] using h
    have hderiv : deriv g = fun s => fderiv ℝ f (line s) e := by
      funext s
      exact (hfirst s).deriv
    have hfderiv : HasFDerivAt (fun y : E3 => fderiv ℝ f y)
        (fderiv ℝ (fun y : E3 => fderiv ℝ f y) x) x := by
      have hfd : ContDiff ℝ 1 (fun y : E3 => fderiv ℝ f y) :=
        hf.fderiv_right (m := 1) (by norm_num)
      exact (hfd.differentiable (by norm_num) x).hasFDerivAt
    have hcurve : HasDerivAt (fun s : ℝ => fderiv ℝ f (line s))
        (fderiv ℝ (fun y : E3 => fderiv ℝ f y) x e) 0 := by
      have h₀ : HasFDerivAt (fun y : E3 => fderiv ℝ f y)
          (fderiv ℝ (fun y : E3 => fderiv ℝ f y) x) (line 0) := by
        simpa [line] using hfderiv
      simpa [line, Function.comp_def] using h₀.comp_hasDerivAt 0 (hline 0)
    have hconst : HasDerivAt (fun _ : ℝ => e) (0 : E3) 0 :=
      hasDerivAt_const (c := e) (x := 0)
    have heval := HasDerivAt.clm_apply (𝕜 := ℝ) hcurve hconst
    rw [hderiv]
    simpa [g, line, Function.comp_def] using heval
  have line_norm_sq_expansion (x e : E3) :
      (fun s : ℝ => ‖x + s • e‖ ^ 2) =
        fun s => ‖x‖ ^ 2 + 2 * s * inner ℝ x e + s ^ 2 * ‖e‖ ^ 2 := by
    funext s
    rw [norm_add_sq_real]
    simp [real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  have line_norm_sq_second_deriv (x e : E3) :
      HasDerivAt (deriv (fun s : ℝ => ‖x + s • e‖ ^ 2))
        (2 * ‖e‖ ^ 2) 0 := by
    let c₀ : ℝ := ‖x‖ ^ 2
    let c₁ : ℝ := 2 * inner ℝ x e
    let c₂ : ℝ := ‖e‖ ^ 2
    have hpoly : (fun s : ℝ => ‖x + s • e‖ ^ 2) =
        fun s => c₀ + c₁ * s + s ^ 2 * c₂ := by
      funext s
      rw [norm_add_sq_real]
      simp [c₀, c₁, c₂, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
      rw [mul_pow, sq_abs]
      ring
    rw [hpoly]
    have hp (s : ℝ) : HasDerivAt
        (fun r : ℝ => c₀ + c₁ * r + r ^ 2 * c₂)
        (c₁ + 2 * s * c₂) s := by
      have h₁ : HasDerivAt (fun r : ℝ => c₁ * r) c₁ s := by
        simpa [mul_comm] using (hasDerivAt_id s).mul_const c₁
      have h₂ : HasDerivAt (fun r : ℝ => r ^ 2 * c₂) (2 * s * c₂) s := by
        have hpow : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
          simpa using hasDerivAt_pow 2 s
        simpa using hpow.mul_const c₂
      have hq : HasDerivAt (fun r : ℝ => c₁ * r + r ^ 2 * c₂)
          (c₁ + 2 * s * c₂) s := by
        change HasDerivAt ((fun r : ℝ => c₁ * r) + fun r : ℝ => r ^ 2 * c₂)
          (c₁ + 2 * s * c₂) s
        exact h₁.add h₂
      simpa [add_assoc] using hq.const_add c₀
    have hderiv : deriv (fun s : ℝ => c₀ + c₁ * s + s ^ 2 * c₂) =
        fun s => c₁ + 2 * s * c₂ := by
      funext s
      exact (hp s).deriv
    rw [hderiv]
    have hsecond : HasDerivAt (fun s : ℝ => c₁ + 2 * s * c₂) (2 * c₂) 0 := by
      simpa [mul_assoc, add_comm] using
        (((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).mul_const c₂).const_add c₁
    simpa [c₂] using hsecond
  have line_barrier_second_deriv {f : E3 → ℝ} {x e : E3}
      (hf : ContDiff ℝ 2 f) (ε τ : ℝ)
      (hmax : IsLocalMax (fun y : E3 => f y - ε * (‖y‖ ^ 2 + 7 * τ)) x) :
      fderiv ℝ (fderiv ℝ f) x e e - ε * (2 * ‖e‖ ^ 2) ≤ 0 := by
    let line : ℝ → E3 := fun s => x + s • e
    let g : ℝ → ℝ := fun s => f (line s)
    let n : ℝ → ℝ := fun s => ‖line s‖ ^ 2
    let q : ℝ → ℝ := fun s => g s - ε * (n s + 7 * τ)
    have hlineCont : ContinuousAt line 0 := by
      change ContinuousAt (fun s : ℝ => x + s • e) 0
      fun_prop
    have hqmax : IsLocalMax q 0 := by
      have hmax' : IsLocalMax (fun y : E3 => f y - ε * (‖y‖ ^ 2 + 7 * τ)) (line 0) := by
        simpa [line] using hmax
      have h := hmax'.comp_continuous hlineCont
      simpa [q, g, n, line, Function.comp_def] using h
    have hgC2 : ContDiff ℝ 2 g := by
      have hlineC2 : ContDiff ℝ 2 line := by
        change ContDiff ℝ 2 (fun s : ℝ => x + s • e)
        fun_prop
      exact hf.comp hlineC2
    have hnPoly : n = fun s : ℝ =>
        ‖x‖ ^ 2 + 2 * s * inner ℝ x e + s ^ 2 * ‖e‖ ^ 2 := by
      exact line_norm_sq_expansion x e
    have hnC2 : ContDiff ℝ 2 n := by
      rw [hnPoly]
      fun_prop
    have hG2 := line_second_deriv (f := f) (x := x) (e := e) hf
    have hN2 := line_norm_sq_second_deriv x e
    have hqfirst (s : ℝ) : HasDerivAt q (deriv g s - ε * deriv n s) s := by
      have hg : HasDerivAt g (deriv g s) s :=
        (hgC2.differentiable (by norm_num) s).hasDerivAt
      have hn : HasDerivAt n (deriv n s) s :=
        (hnC2.differentiable (by norm_num) s).hasDerivAt
      have hsum : HasDerivAt (fun r : ℝ => n r + 7 * τ) (deriv n s) s :=
        hn.add_const (7 * τ)
      have hscaled : HasDerivAt (fun r : ℝ => ε * (n r + 7 * τ))
          (ε * deriv n s) s := by
        simpa using hsum.const_mul ε
      change HasDerivAt ((fun r : ℝ => g r) - fun r => ε * (n r + 7 * τ))
        (deriv g s - ε * deriv n s) s
      exact hg.sub hscaled
    have hqderiv : deriv q = fun s => deriv g s - ε * deriv n s := by
      funext s
      exact (hqfirst s).deriv
    have hqsecond : HasDerivAt (fun s : ℝ => deriv g s - ε * deriv n s)
        (fderiv ℝ (fderiv ℝ f) x e e - ε * (2 * ‖e‖ ^ 2)) 0 := by
      have hscaled := hN2.const_mul ε
      change HasDerivAt
        ((deriv (fun s : ℝ => f (x + s • e))) -
          fun r => ε * deriv (fun s : ℝ => ‖x + s • e‖ ^ 2) r)
        (fderiv ℝ (fderiv ℝ f) x e e - ε * (2 * ‖e‖ ^ 2)) 0
      exact hG2.sub hscaled
    have hqval : deriv (deriv q) 0 =
        fderiv ℝ (fderiv ℝ f) x e e - ε * (2 * ‖e‖ ^ 2) := by
      rw [hqderiv]
      exact hqsecond.deriv
    have hterm : ContinuousAt (fun s : ℝ => ε * (n s + 7 * τ)) 0 :=
      (hnC2.continuous.continuousAt.add continuousAt_const).const_mul ε
    have hcont : ContinuousAt q 0 := hgC2.continuous.continuousAt.sub hterm
    have hle := localMax_second_deriv_nonpos hqmax hcont
    rw [hqval] at hle
    exact hle
  let scalarTimeExtension (g : Slab T → ℝ) (x : E3) (s : ℝ) : ℝ :=
    if hs : s ∈ Set.Icc (0 : ℝ) T then g (⟨s, hs⟩, x) else 0
  have scalar_max_principle (g d : Slab T → ℝ) (M : ℝ) (hM : 0 ≤ M)
      (hgcont : Continuous g) (hbound : ∀ p, |g p| ≤ M)
      (hzero : ∀ x : E3, g (⟨⟨0, le_rfl, hT.le⟩, x⟩) = 0)
      (hC2 : ∀ t : Set.Icc (0 : ℝ) T, ContDiff ℝ 2 (fun x => g (t,x)))
      (hheatScalar : ∀ p : Slab T,
        d p = ∑ i : Fin 3,
          fderiv ℝ (fderiv ℝ (fun y : E3 => g (p.1,y))) p.2
            (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))
      (hderivScalar : ∀ (t : Set.Icc (0 : ℝ) T), 0 < (t : ℝ) → (t : ℝ) < T →
        ∀ x : E3, HasDerivAt (scalarTimeExtension g x) (d (t,x)) (t : ℝ)) :
      ∀ p : Slab T, (p.1 : ℝ) < T → g p ≤ 0 := by
    intro p hpT
    by_contra hn
    have hp : 0 < g p := lt_of_not_ge hn
    let s : ℝ := p.1
    let x : E3 := p.2
    have hs0 : 0 < s := by
      dsimp [s]
      by_contra hs
      have htzero : (p.1 : ℝ) = 0 := le_antisymm (le_of_not_gt hs) p.1.2.1
      have heq : p = (⟨⟨0, le_rfl, hT.le⟩, x⟩ : Slab T) := by
        apply Prod.ext
        · apply Subtype.ext
          exact htzero
        · rfl
      have hz := hzero x
      rw [heq] at hp
      simp [hz] at hp
    have hsT : s < T := by dsimp [s]; exact hpT
    have hsle : s ≤ T := hsT.le
    have hcpos : 0 < ‖x‖ ^ 2 + 7 * s := by
      have hx : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
      nlinarith
    let ε : ℝ := g p / (2 * (‖x‖ ^ 2 + 7 * s))
    have hε : 0 < ε := by
      dsimp [ε]
      exact div_pos hp (mul_pos (by norm_num) hcpos)
    let R : ℝ := ‖x‖ + M / ε + 2
    have hRone : 1 < R := by
      dsimp [R]
      have : 0 ≤ ‖x‖ := norm_nonneg _
      have : 0 ≤ M / ε := div_nonneg hM hε.le
      linarith
    have hxR : ‖x‖ < R := by
      dsimp [R]
      have : 0 ≤ M / ε := div_nonneg hM hε.le
      linarith
    have hMR : M < ε * R := by
      have hMdiv : M / ε < R := by
        dsimp [R]
        have hMnonneg : 0 ≤ M / ε := div_nonneg hM hε.le
        linarith [norm_nonneg x, hMnonneg]
      have h := (div_lt_iff₀ hε).mp hMdiv
      nlinarith [h]
    have hεR2 : M < ε * R ^ 2 := by
      have hεR : 0 ≤ ε * R := mul_nonneg hε.le (le_of_lt (lt_trans zero_lt_one hRone))
      have hmul : ε * R ≤ ε * R ^ 2 := by nlinarith [hRone]
      linarith
    let Iₛ : Set.Icc (0 : ℝ) s := ⟨s, ⟨le_of_lt hs0, le_rfl⟩⟩
    let B := Metric.closedBall (0 : E3) R
    let KD := Set.Icc (0 : ℝ) s × B
    have htimeSub : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T := by
      intro t ht
      exact ⟨ht.1, ht.2.trans hsle⟩
    let incl : Set.Icc (0 : ℝ) s → Set.Icc (0 : ℝ) T := Set.inclusion htimeSub
    have hincl : Continuous incl := continuous_inclusion htimeSub
    let embed : KD → Slab T := fun q => (incl q.1, q.2)
    have hembed : Continuous embed := by
      exact (hincl.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    let U : KD → ℝ := fun q =>
      g (embed q) - ε * (‖(q.2 : E3)‖ ^ 2 + 7 * (q.1 : ℝ))
    have hUcont : Continuous U := by
      have hsp : Continuous (fun q : KD => (q.2 : E3)) :=
        continuous_subtype_val.comp continuous_snd
      have htm : Continuous (fun q : KD => (q.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hnsq : Continuous (fun q : KD => ‖(q.2 : E3)‖ ^ 2) :=
        (continuous_norm.comp hsp).pow 2
      change Continuous (fun q : KD =>
        g (embed q) - ε * (‖(q.2 : E3)‖ ^ 2 + 7 * (q.1 : ℝ)))
      exact (hgcont.comp hembed).sub
        (continuous_const.mul (hnsq.add (continuous_const.mul htm)))
    have hKcompact : IsCompact (Set.univ : Set KD) := isCompact_univ
    have hxtarget : ‖x‖ ≤ R := hxR.le
    have hxball : x ∈ Metric.closedBall (0 : E3) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hxtarget
    let q₀ : KD := (⟨s, ⟨le_of_lt hs0, le_rfl⟩⟩,
      ⟨x, hxball⟩)
    have hUtarget : 0 < U q₀ := by
      have htimeEq : incl q₀.1 = p.1 := by
        apply Subtype.ext
        rfl
      have hxEq : (q₀.2 : E3) = x := rfl
      have hval : g (embed q₀) = g p := by
        have heq : embed q₀ = p := by
          apply Prod.ext
          · exact htimeEq
          · exact hxEq
        rw [heq]
      have hscale : ε * (‖x‖ ^ 2 + 7 * s) = g p / 2 := by
        dsimp [ε]
        field_simp [ne_of_gt hcpos]
      change 0 < g (embed q₀) - ε * (‖(q₀.2 : E3)‖ ^ 2 + 7 * (q₀.1 : ℝ))
      rw [hval, hscale]
      nlinarith [hp]
    have hKne : (Set.univ : Set KD).Nonempty := ⟨q₀, Set.mem_univ _⟩
    obtain ⟨qmax, hqmax, hmax0⟩ := hKcompact.exists_isMaxOn hKne hUcont.continuousOn
    have hmax : ∀ q : KD, U q ≤ U qmax := isMaxOn_univ_iff.mp hmax0
    have hmaxpos : 0 < U qmax := by
      have hle := hmax q₀
      exact lt_of_lt_of_le hUtarget hle
    let t : Set.Icc (0 : ℝ) s := qmax.1
    let y : E3 := qmax.2
    have hty0 : 0 < (t : ℝ) := by
      by_contra hn0
      have htzero : (t : ℝ) = 0 := le_antisymm (le_of_not_gt hn0) t.2.1
      have hvalueZero : g (embed qmax) = 0 := by
        have heq : embed qmax = (⟨⟨0, le_rfl, hT.le⟩, y⟩ : Slab T) := by
          apply Prod.ext
          · apply Subtype.ext
            exact htzero
          · rfl
        rw [heq]
        exact hzero y
      have hu0 : U qmax ≤ 0 := by
        change g (embed qmax) - ε * (‖y‖ ^ 2 + 7 * (t : ℝ)) ≤ 0
        rw [hvalueZero, htzero]
        nlinarith [sq_nonneg ‖y‖, hε]
      linarith [hmaxpos]
    have hyR : ‖y‖ < R := by
      have hyclosed : ‖y‖ ≤ R := by
        have hdist := Metric.mem_closedBall.mp qmax.2.2
        simpa [dist_zero_right] using hdist
      by_contra hnot
      have heq : ‖y‖ = R := le_antisymm hyclosed (le_of_not_gt hnot)
      have hboundary : U qmax < 0 := by
        have hval : g (embed qmax) ≤ M := by
          have := hbound (embed qmax)
          exact (abs_le.mp this).2
        have htpos : 0 ≤ (t : ℝ) := t.2.1
        dsimp [U]
        rw [heq]
        nlinarith [hval, hεR2, hε, norm_nonneg y]
      linarith [hmaxpos]
    have hspaceMax : IsMaxOn
        (fun v : E3 => g (incl t,v) - ε * (‖v‖ ^ 2 + 7 * (t : ℝ))) B y := by
      intro v hv
      have h := hmax (t, ⟨v, hv⟩)
      simpa [U, embed, t, y] using h
    have hyBall : y ∈ Metric.ball (0 : E3) R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hyR
    have hspaceLocal : IsLocalMax
        (fun v : E3 => g (incl t,v) - ε * (‖v‖ ^ 2 + 7 * (t : ℝ))) y :=
      hspaceMax.isLocalMax (Metric.closedBall_mem_nhds_of_mem hyBall)
    have hdiag (i : Fin 3) :
        fderiv ℝ (fderiv ℝ (fun v : E3 => g (incl t,v))) y
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) ≤ 2 * ε := by
      have hbar := line_barrier_second_deriv
        (f := fun v : E3 => g (incl t,v)) (x := y)
        (e := EuclideanSpace.single i 1) (hC2 (incl t)) ε (t : ℝ) hspaceLocal
      have hi : ‖EuclideanSpace.single i (1 : ℝ)‖ ^ 2 = 1 := by simp
      have hle := hbar
      rw [hi] at hle
      nlinarith
    let pmax : Slab T := embed qmax
    have htrace := hheatScalar pmax
    have htraceBound : d pmax ≤ 6 * ε := by
      rw [htrace]
      calc
        (∑ i : Fin 3,
            fderiv ℝ (fderiv ℝ (fun v : E3 => g (incl t,v))) y
              (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) ≤
            ∑ _i : Fin 3, 2 * ε := Finset.sum_le_sum fun i hi => hdiag i
        _ = 6 * ε := by
          simp [Finset.sum_const]
          ring
    let Ftime : ℝ → ℝ := fun r => scalarTimeExtension g y r -
      ε * (‖y‖ ^ 2 + 7 * r)
    have htimeMax : IsMaxOn Ftime (Set.Icc (0 : ℝ) s) (t : ℝ) := by
      intro r hr
      let q' : KD := (⟨r, hr⟩, qmax.2)
      have h := hmax q'
      have hrT : r ∈ Set.Icc (0 : ℝ) T := htimeSub hr
      have hext : scalarTimeExtension g y r = g (⟨r, hrT⟩, y) := by
        simp only [scalarTimeExtension, dif_pos hrT]
      have hval : embed q' = (⟨r, hrT⟩, y) := by
        dsimp [q', embed]
      have htT : (t : ℝ) ∈ Set.Icc (0 : ℝ) T :=
        ⟨t.2.1, le_trans t.2.2 hsle⟩
      have hextMax : scalarTimeExtension g y (t : ℝ) = g (embed qmax) := by
        have heq : (⟨(t : ℝ), htT⟩, y) = embed qmax := by
          apply Prod.ext
          · apply Subtype.ext
            rfl
          · rfl
        simpa only [scalarTimeExtension, dif_pos htT] using congrArg g heq
      change g (embed q') - ε * (‖(q'.2 : E3)‖ ^ 2 + 7 * (q'.1 : ℝ)) ≤
        g (embed qmax) - ε * (‖y‖ ^ 2 + 7 * (t : ℝ)) at h
      rw [hval] at h
      have hqfst : (q'.1 : ℝ) = r := rfl
      have hqsnd : (q'.2 : E3) = y := rfl
      rw [hqfst, hqsnd] at h
      change scalarTimeExtension g y r - ε * (‖y‖ ^ 2 + 7 * r) ≤
        scalarTimeExtension g y (t : ℝ) - ε * (‖y‖ ^ 2 + 7 * (t : ℝ))
      rw [← hext, ← hextMax] at h
      exact h
    have htimeLocal : IsLocalMaxOn Ftime (Set.Icc (0 : ℝ) s) (t : ℝ) :=
      htimeMax.localize
    have hhalf : t.1 / 2 ∈ Set.Icc (0 : ℝ) s := by
      constructor <;> nlinarith [t.2.1, t.2.2]
    have hseg : segment ℝ (t : ℝ) ((t : ℝ) + (-(t : ℝ) / 2)) ⊆
        Set.Icc (0 : ℝ) s := by
      have hconv : Convex ℝ (Set.Icc (0 : ℝ) s) := convex_Icc (0 : ℝ) s
      have hseg' : segment ℝ (t : ℝ) ((t : ℝ) / 2) ⊆ Set.Icc (0 : ℝ) s := by
        exact hconv.segment_subset t.2 hhalf
      convert hseg' using 1 <;> congr 1 <;> ring
    have hdir : -(t : ℝ) / 2 ∈ posTangentConeAt (Set.Icc (0 : ℝ) s) (t : ℝ) :=
      mem_posTangentConeAt_of_segment_subset hseg
    have htInclPos : 0 < (incl t : ℝ) := by simpa [incl, Set.inclusion] using hty0
    have htInclT : (incl t : ℝ) < T := by
      calc
        (incl t : ℝ) = (t : ℝ) := rfl
        _ ≤ s := t.2.2
        _ < T := hsT
    have htime := hderivScalar (incl t) htInclPos htInclT y
    have hlinear : HasDerivAt
        (fun r : ℝ => ε * (‖y‖ ^ 2 + 7 * r)) (7 * ε) (t : ℝ) := by
      have h7 : HasDerivAt (fun r : ℝ => 7 * r) 7 (t : ℝ) := by
        simpa [mul_comm] using (hasDerivAt_id (t : ℝ)).const_mul (7 : ℝ)
      have hsum : HasDerivAt (fun r : ℝ => ‖y‖ ^ 2 + 7 * r) 7 (t : ℝ) := by
        simpa [add_comm] using h7.const_add (‖y‖ ^ 2)
      simpa [mul_comm] using hsum.const_mul ε
    have hFderiv : HasDerivAt Ftime (d (incl t,y) - 7 * ε) (t : ℝ) := by
      have := htime.sub hlinear
      change HasDerivAt
        ((scalarTimeExtension g y) - fun r : ℝ => ε * (‖y‖ ^ 2 + 7 * r))
        (d (incl t,y) - 7 * ε) (incl t : ℝ)
      exact this
    have hdirSign := htimeLocal.hasFDerivWithinAt_nonpos hFderiv.hasDerivWithinAt hdir
    have hFnonneg : 0 ≤ d (incl t,y) - 7 * ε := by
      have hspos : 0 < (t : ℝ) := hty0
      have hsimp : (d (incl t,y) - 7 * ε) * (-(t : ℝ) / 2) ≤ 0 := by
        simpa [mul_comm] using hdirSign
      nlinarith
    have htraceAt : d (incl t,y) ≤ 6 * ε := by
      simpa [pmax, embed, t, y] using htraceBound
    nlinarith [hFnonneg, htraceAt, hε]
  change z.1.1 ∈ parabolicC2HolderSet T alpha ∧
    (z.1.1.1.1, z.1.2) ∈ slabTimeDerivativeGraph T ∧
    (∀ p : Pair T, z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (z.1.2 p.1.1-z.1.2 p.1.2)) ∧
    (∀ x : E3, z.1.1.1.1 (⟨0, le_rfl, hT.le⟩,x) = 0) at hz
  rcases hz with ⟨hholder, hgraph, hincrement, hinitial⟩
  have hspace : z.1.1.1 ∈ spaceTimeC2JetSet T := hholder.1
  let v : Slab T →ᵇ E6 := z.1.1.1.1
  let grad : Slab T →ᵇ (E3 →L[ℝ] E6) := z.1.1.1.2.1
  let hess : Slab T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6) := z.1.1.1.2.2
  let time : Slab T →ᵇ E6 := z.1.2
  have hspaceC2 (t : Set.Icc (0 : ℝ) T) :
      ContDiff ℝ 2 (fun x : E3 => v (t,x)) := by
    have hh := (spaceTime_C2_jet_complete T).2 z.1.1.1 hspace t
    simpa [v] using hh
  let P (k : Fin 6) : E6 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have hproj_apply (k : Fin 6) (a : E6) : P k a = a k := by
    simp [P, PiLp.proj]
  let g (k : Fin 6) : Slab T → ℝ := fun p => v p k
  let d (k : Fin 6) : Slab T → ℝ := fun p => time p k
  have hscalarC2 (k : Fin 6) (t : Set.Icc (0 : ℝ) T) :
      ContDiff ℝ 2 (fun x : E3 => g k (t,x)) := by
    have hp := (P k).contDiff.comp (hspaceC2 t)
    have heq : (fun x : E3 => g k (t,x)) = fun x => P k (v (t,x)) := by
      funext x
      exact (hproj_apply k (v (t,x))).symm
    rw [heq]
    exact hp
  have hscalarHess (k : Fin 6) (t : Set.Icc (0 : ℝ) T)
      (x e f : E3) :
      fderiv ℝ (fderiv ℝ (fun y : E3 => g k (t,y))) x e f =
        (fderiv ℝ (fderiv ℝ (fun y : E3 => v (t,y))) x e f) k := by
    let F : E3 → E6 := fun y => v (t,y)
    let C : (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] ℝ) :=
      ContinuousLinearMap.compL ℝ E3 E6 ℝ (P k)
    have hprojfun : (fun u : E6 => u k) = P k := by
      funext u
      exact hproj_apply k u
    have hfirst (y : E3) :
        fderiv ℝ (fun u : E3 => F u k) y = (P k).comp (fderiv ℝ F y) := by
      have hh := fderiv_comp (g := P k) (f := F) (x := y)
        (P k).differentiableAt ((hspaceC2 t).differentiable (by norm_num) y)
      have hcompfun : (fun u : E3 => F u k) = (P k) ∘ F := by
        funext u
        simpa [Function.comp_def] using congrFun hprojfun (F u)
      rw [hcompfun]
      simpa [Function.comp_def] using hh
    have hfun : (fun y : E3 => fderiv ℝ (fun u : E3 => F u k) y) =
        fun y => C (fderiv ℝ F y) := by
      funext y
      rw [hfirst y]
      simp [C, ContinuousLinearMap.compL_apply]
    have hfd : DifferentiableAt ℝ (fderiv ℝ F) x :=
      ((hspaceC2 t).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) x
    have hsecond := fderiv_comp (g := C) (f := fderiv ℝ F) (x := x)
      C.differentiableAt hfd
    have hsecond' :
        fderiv ℝ (fun y : E3 => fderiv ℝ (fun u : E3 => F u k) y) x =
          C.comp (fderiv ℝ (fun y : E3 => fderiv ℝ F y) x) := by
      rw [hfun]
      simpa [Function.comp_def] using hsecond
    have hcoord := congrArg (fun L : E3 →L[ℝ] E3 →L[ℝ] ℝ => L e f) hsecond'
    simpa [C, ContinuousLinearMap.compL_apply, P] using hcoord
  have hvectorHess (t : Set.Icc (0 : ℝ) T) (x : E3) :
      fderiv ℝ (fderiv ℝ (fun y : E3 => v (t,y))) x = hess (t,x) := by
    have hs := hspace t
    have hgradEq : (fun y : E3 => grad (t,y)) =
        (fun y => fderiv ℝ (fun u : E3 => v (t,u)) y) := by
      funext y
      exact (hs.1 y).fderiv.symm
    have hderivEq := congrArg (fun F : E3 → E3 →L[ℝ] E6 => fderiv ℝ F x) hgradEq
    exact hderivEq.symm.trans (hs.2 x).fderiv
  have hscalarHeat (k : Fin 6) : ∀ p : Slab T,
      d k p = ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ (fun y : E3 => g k (p.1,y))) p.2
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    intro p
    have hh := congrArg (fun a : E6 => a k) (hheat p)
    have hsum : (∑ i : Fin 3,
        hess p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) k =
        ∑ i : Fin 3,
          (hess p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) k := by
      simp
    rw [hsum] at hh
    change d k p = _
    simpa only [hproj_apply] using hh.trans (Finset.sum_congr rfl fun i hi => by
      rw [← hvectorHess p.1 p.2]
      exact (hscalarHess k p.1 p.2 (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)).symm)
  have hgcont (k : Fin 6) : Continuous (g k) := by
    have hp : Continuous (fun p : Slab T => P k (v p)) :=
      (P k).continuous.comp v.continuous
    have heq : (g k) = fun p => P k (v p) := by
      funext p
      exact (hproj_apply k (v p)).symm
    rw [heq]
    exact hp
  have hscalarDeriv (k : Fin 6) (t : Set.Icc (0 : ℝ) T)
      (ht0 : 0 < (t : ℝ)) (htT : (t : ℝ) < T) (x : E3) :
      HasDerivAt (scalarTimeExtension (g k) x) (d k (t,x)) (t : ℝ) := by
    have hv := hgraph t ht0 htT x
    have hv' : HasDerivAt (timeExtension v x) (time (t,x)) (t : ℝ) := by
      simpa [v, time] using hv
    have hcoord : HasDerivAt (fun s : ℝ => (timeExtension v x s) k)
        ((time (t,x)) k) (t : ℝ) := by
      have heval := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (E := fun _ : Fin 6 => ℝ)
        (p := 2) (f := timeExtension v x (t : ℝ)) k
      have hh := heval.comp_hasDerivAt_of_eq (t : ℝ) hv' (by rfl)
      simpa [Function.comp_def, PiLp.proj, timeExtension, ht0.le, htT.le] using hh
    have hext : scalarTimeExtension (g k) x =
        fun s => (timeExtension v x s) k := by
      funext s
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · simp only [scalarTimeExtension, dif_pos hs, timeExtension]
        rfl
      · simp only [scalarTimeExtension, dif_neg hs, timeExtension]
        simp
    rw [hext]
    exact hcoord
  have hscalarBound (k : Fin 6) (p : Slab T) : |g k p| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    calc
      ‖g k p‖ = ‖(v p) k‖ := by rfl
      _ ≤ ‖v p‖ := by simpa using (PiLp.norm_apply_le (p := 2) (x := v p) k)
      _ ≤ ‖v‖ := BoundedContinuousFunction.norm_coe_le_norm v p
  have hscalarZero (k : Fin 6) :
      ∀ p : Slab T, (p.1 : ℝ) < T → g k p = 0 := by
    let gn : Slab T → ℝ := fun p => -g k p
    let dn : Slab T → ℝ := fun p => -d k p
    have hzero : ∀ x : E3, g k (⟨⟨0, le_rfl, hT.le⟩,x⟩) = 0 := by
      intro x
      have hh := congrArg (fun a : E6 => a k) (hinitial x)
      simpa [g, v] using hh
    have hnegzero : ∀ x : E3, gn (⟨⟨0, le_rfl, hT.le⟩,x⟩) = 0 := by
      intro x
      simp [gn, hzero x]
    have hnegcont : Continuous gn := by
      change Continuous ((fun y : ℝ => -y) ∘ g k)
      exact continuous_neg.comp (hgcont k)
    have hnegbound : ∀ p : Slab T, |gn p| ≤ ‖v‖ := by
      intro p
      simpa [gn] using hscalarBound k p
    have hnegC2 (t : Set.Icc (0 : ℝ) T) :
        ContDiff ℝ 2 (fun x : E3 => gn (t,x)) := by
      simpa [gn] using (hscalarC2 k t).neg
    have hnegHeat : ∀ p : Slab T,
        dn p = ∑ i : Fin 3,
          fderiv ℝ (fderiv ℝ (fun y : E3 => gn (p.1,y))) p.2
            (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
      intro p
      rw [show dn p = -(d k p) by rfl, hscalarHeat k p]
      have hnegEntry (i : Fin 3) :
          fderiv ℝ (fderiv ℝ (fun y : E3 => -g k (p.1,y))) p.2
              (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
            -fderiv ℝ (fderiv ℝ (fun y : E3 => g k (p.1,y))) p.2
              (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
        have hfun :
            (fun y : E3 => fderiv ℝ (fun w : E3 => -g k (p.1,w)) y) =
              fun y => -fderiv ℝ (fun w : E3 => g k (p.1,w)) y := by
          funext y
          exact fderiv_fun_neg
        have hsecond := congrArg
          (fun F : E3 → E3 →L[ℝ] ℝ => fderiv ℝ F p.2) hfun
        have heval := congrArg
          (fun L : E3 →L[ℝ] E3 →L[ℝ] ℝ =>
            L (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) hsecond
        calc
          _ = (fderiv ℝ
              (fun y : E3 => -fderiv ℝ (fun w : E3 => g k (p.1,w)) y) p.2)
                (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := heval
          _ = -((fderiv ℝ
              (fun y : E3 => fderiv ℝ (fun w : E3 => g k (p.1,w)) y) p.2)
                (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) := by
            rw [fderiv_fun_neg]
            simp
      calc
        -(∑ i : Fin 3,
            fderiv ℝ (fderiv ℝ (fun y : E3 => g k (p.1,y))) p.2
              (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
            ∑ i : Fin 3,
              -fderiv ℝ (fderiv ℝ (fun y : E3 => g k (p.1,y))) p.2
                (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
          rw [← Finset.sum_neg_distrib]
        _ = ∑ i : Fin 3,
            fderiv ℝ (fderiv ℝ (fun y : E3 => -g k (p.1,y))) p.2
              (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hnegEntry i]
    have hnegDeriv : ∀ (t : Set.Icc (0 : ℝ) T), 0 < (t : ℝ) → (t : ℝ) < T →
        ∀ x : E3, HasDerivAt (scalarTimeExtension gn x) (dn (t,x)) (t : ℝ) := by
      intro t ht0 htT x
      have hh := hscalarDeriv k t ht0 htT x
      have heq : scalarTimeExtension gn x = -scalarTimeExtension (g k) x := by
        funext s
        change (if hs' : s ∈ Set.Icc (0 : ℝ) T then gn (⟨s, hs'⟩,x) else 0) =
          -(if hs' : s ∈ Set.Icc (0 : ℝ) T then g k (⟨s, hs'⟩,x) else 0)
        by_cases hs : s ∈ Set.Icc (0 : ℝ) T
        · simp [hs, gn]
        · simp [hs, gn]
      rw [heq]
      simpa [dn] using hh.neg
    have hpositive := scalar_max_principle (g k) (d k) ‖v‖
      (norm_nonneg v) (hgcont k) (hscalarBound k) hzero (hscalarC2 k)
      (hscalarHeat k) (hscalarDeriv k)
    have hnegative := scalar_max_principle gn dn ‖v‖
      (norm_nonneg v) hnegcont hnegbound hnegzero hnegC2 hnegHeat hnegDeriv
    intro p hpT
    have hp' := hpositive p hpT
    have hn' := hnegative p hpT
    dsimp [gn] at hn'
    linarith
  let clamp : ℝ → Set.Icc (0 : ℝ) T := fun s =>
    ⟨max 0 (min s T), ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩⟩
  have hclamp : Continuous clamp := by
    apply Continuous.subtype_mk
    exact continuous_const.max (continuous_id.min continuous_const)
  have hclampInterior (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
      clamp s = ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ := by
    apply Subtype.ext
    simp [clamp, min_eq_left hs.2.le, max_eq_right hs.1.le]
  have hclampAt (t : Set.Icc (0 : ℝ) T) : clamp (t : ℝ) = t := by
    apply Subtype.ext
    simp [clamp, min_eq_left t.2.2, max_eq_right t.2.1]
  have hscalarAllZero (k : Fin 6) (t : Set.Icc (0 : ℝ) T) (x : E3) :
      g k (t,x) = 0 := by
    by_cases ht : (t : ℝ) < T
    · exact hscalarZero k (t,x) ht
    · have htEq : (t : ℝ) = T := (le_antisymm (le_of_not_gt ht) t.2.2).symm
      let F : ℝ → ℝ := fun s => g k (clamp s,x)
      have hF : Continuous F := by
        exact (hgcont k).comp (hclamp.prodMk continuous_const)
      let eqSet : Set ℝ := {s | F s = 0}
      have heqClosed : IsClosed eqSet := isClosed_eq hF continuous_const
      have hsubset : Set.Ioo (0 : ℝ) T ⊆ eqSet := by
        intro s hs
        change g k (clamp s,x) = 0
        rw [hclampInterior s hs]
        exact hscalarZero k (⟨s, ⟨hs.1.le, hs.2.le⟩⟩,x) hs.2
      have hcl : (T : ℝ) ∈ closure eqSet := by
        apply closure_mono hsubset
        rw [closure_Ioo (a := (0 : ℝ)) (b := T) (ne_of_lt hT)]
        exact ⟨hT.le, le_rfl⟩
      have hzeroT : F T = 0 := heqClosed.closure_subset hcl
      have hct : clamp T = ⟨T, ⟨hT.le, le_rfl⟩⟩ := by
        apply Subtype.ext
        simp [clamp, max_eq_right hT.le]
      have h : g k (⟨T, ⟨hT.le, le_rfl⟩⟩,x) = 0 := by
        simpa [F, hct] using hzeroT
      have htval : t = ⟨T, ⟨hT.le, le_rfl⟩⟩ := by
        apply Subtype.ext
        exact htEq
      rw [htval]
      exact h
  have hvalueZero (p : Slab T) : v p = 0 := by
    ext k
    have hh := hscalarAllZero k p.1 p.2
    simpa [g, v] using hh
  have htimeInterior (t : Set.Icc (0 : ℝ) T) (ht0 : 0 < (t : ℝ))
      (htT : (t : ℝ) < T) (x : E3) : time (t,x) = 0 := by
    have hv := hgraph t ht0 htT x
    have hext : timeExtension v x = fun _ : ℝ => (0 : E6) := by
      funext s
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · simp [timeExtension, hs, hvalueZero]
      · simp [timeExtension, hs]
    rw [hext] at hv
    have hconst : HasDerivAt (fun _ : ℝ => (0 : E6)) (0 : E6) (t : ℝ) :=
      hasDerivAt_const (c := (0 : E6)) (x := (t : ℝ))
    exact hv.unique hconst
  have htimeZero (p : Slab T) : time p = 0 := by
    let F : ℝ → E6 := fun s => time (clamp s,p.2)
    have hF : Continuous F := by
      exact time.continuous.comp (hclamp.prodMk continuous_const)
    let eqSet : Set ℝ := {s | F s = 0}
    have heqClosed : IsClosed eqSet := isClosed_eq hF continuous_const
    have hsubset : Set.Ioo (0 : ℝ) T ⊆ eqSet := by
      intro s hs
      change time (clamp s,p.2) = 0
      rw [hclampInterior s hs]
      exact htimeInterior ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ hs.1 hs.2 p.2
    have hcl : (p.1 : ℝ) ∈ closure eqSet := by
      apply closure_mono hsubset
      rw [closure_Ioo (a := (0 : ℝ)) (b := T) (ne_of_lt hT)]
      exact p.1.2
    have hzero := heqClosed.closure_subset hcl
    change F (p.1 : ℝ) = 0 at hzero
    dsimp [F] at hzero
    rw [hclampAt] at hzero
    exact hzero
  have hgradZero (p : Slab T) : grad p = 0 := by
    have hs := hspace p.1
    have hvalueSlice : (fun y : E3 => v (p.1,y)) = fun _ => (0 : E6) := by
      funext y
      exact hvalueZero (p.1,y)
    have hderiv := hs.1 p.2
    rw [hvalueSlice] at hderiv
    have hconst : HasFDerivAt (fun _ : E3 => (0 : E6))
        (0 : E3 →L[ℝ] E6) p.2 :=
      hasFDerivAt_const (𝕜 := ℝ) (0 : E6) p.2
    have heq := hderiv.unique hconst
    simpa [grad] using heq
  have hhessZero (p : Slab T) : hess p = 0 := by
    have hs := hspace p.1
    have hgradSlice : (fun y : E3 => grad (p.1,y)) =
        fun _ => (0 : E3 →L[ℝ] E6) := by
      funext y
      exact hgradZero (p.1,y)
    have hderiv := hs.2 p.2
    rw [hgradSlice] at hderiv
    have hconst : HasFDerivAt (fun _ : E3 => (0 : E3 →L[ℝ] E6))
        (0 : E3 →L[ℝ] E3 →L[ℝ] E6) p.2 :=
      hasFDerivAt_const (𝕜 := ℝ) (0 : E3 →L[ℝ] E6) p.2
    have heq := hderiv.unique hconst
    simpa [hess] using heq
  have hincrementZero (p : Pair T) : z.2 p = 0 := by
    rw [hincrement p, htimeZero, htimeZero]
    simp
  have hholderIncrementZero (p : Pair T) : z.1.1.2 p = 0 := by
    rw [hholder.2 p]
    simp [hess, hhessZero]
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply BoundedContinuousFunction.ext
          intro p
          exact hvalueZero p
        · apply Prod.ext
          · apply BoundedContinuousFunction.ext
            intro p
            exact hgradZero p
          · apply BoundedContinuousFunction.ext
            intro p
            exact hhessZero p
      · apply BoundedContinuousFunction.ext
        intro p
        exact hholderIncrementZero p
    · apply BoundedContinuousFunction.ext
      intro p
      exact htimeZero p
  · apply BoundedContinuousFunction.ext
    intro p
    exact hincrementZero p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BoundedClassicalHeatUniqueness
