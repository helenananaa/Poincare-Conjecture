import PoincareConjecture.ParallelImplementation.SlabTimeLipschitz
import PoincareConjecture.ParallelImplementation.ZeroTraceLowerJetSmallness
import PoincareConjecture.ParallelImplementation.GradientSupInterpolation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceGradientHolderSmallness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology ContDiff BoundedContinuousFunction
/-- Actual zero-trace gradients become small in the parabolic Holder seminorm. -/
theorem zero_trace_gradient_holder_smallness
    (T alpha : ℝ) (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1)
    (z : FullJet T) (hz : z ∈ fullParabolicJetSet T alpha hT.le) :
    ∀ p q : Slab T, ‖z.1.1.1.2.1 p-z.1.1.1.2.1 q‖ ≤
      16 * ‖z‖ * T^((1-alpha)/2) * parabolicRho p q ^ alpha :=
/- SWARM_PROOF_BEGIN -/
by
  simp only [fullParabolicJetSet] at hz
  rcases hz with ⟨hholder, hgraph, hincrement, hzero⟩
  have hz' : z ∈ fullParabolicJetSet T alpha hT.le := by
    exact ⟨hholder, hgraph, hincrement, hzero⟩
  have hjet : z.1.1.1 ∈ spaceTimeC2JetSet T := hholder.1
  let u : Slab T → EuclideanSpace ℝ (Fin 6) := fun p => z.1.1.1.1 p
  let grad : Slab T → (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 6)) := fun p => z.1.1.1.2.1 p
  let hess : Slab T → (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 6)) :=
    fun p => z.1.1.1.2.2 p
  let N : ℝ := ‖z‖
  let Tf : ℝ := T^((1-alpha)/2)
  have hN : 0 ≤ N := by positivity
  have htimeNorm : ‖z.1.2‖ ≤ N := by
    dsimp [N]
    exact (norm_snd_le z.1).trans (norm_fst_le z)
  have hhessNorm : ‖z.1.1.1.2.2‖ ≤ N := by
    dsimp [N]
    exact (norm_snd_le (z.1.1.1.2)).trans <|
      (norm_snd_le (z.1.1.1)).trans <|
        (norm_fst_le (z.1.1)).trans <|
          (norm_fst_le z.1).trans (norm_fst_le z)
  have hTf : 0 ≤ Tf := by
    dsimp [Tf]
    exact Real.rpow_nonneg hT.le _
  have hscale (d : ℝ) (hd : 0 ≤ d) (hdT : d ≤ Real.sqrt T) :
      d ≤ Tf * d^alpha := by
    by_cases hd0 : d = 0
    · simp [hd0, Tf, ha.ne']
    · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      have hb : 0 ≤ 1-alpha := by linarith [ha1]
      have hp : d^(1-alpha) ≤ (Real.sqrt T)^(1-alpha) :=
        Real.rpow_le_rpow hd hdT hb
      have hsqrt : (Real.sqrt T)^(1-alpha) = Tf := by
        dsimp [Tf]
        calc
          (Real.sqrt T)^(1-alpha) = (T^(1/(2:ℝ)))^(1-alpha) := by
            rw [Real.sqrt_eq_rpow]
          _ = T^((1/(2:ℝ))*(1-alpha)) := by
            rw [← Real.rpow_mul hT.le]
          _ = T^((1-alpha)/2) := by congr 1; ring
      have hsplit : d = d^alpha * d^(1-alpha) := by
        calc
          d = d^(1:ℝ) := by rw [Real.rpow_one]
          _ = d^(alpha + (1-alpha)) := by congr 1; ring
          _ = d^alpha * d^(1-alpha) := Real.rpow_add hdpos _ _
      rw [hsqrt] at hp
      calc
        d = d^alpha * d^(1-alpha) := hsplit
        _ ≤ d^alpha * Tf := mul_le_mul_of_nonneg_left hp
            (Real.rpow_nonneg hd alpha)
        _ = Tf * d^alpha := by ring
  have hsmall :=
    PoincareConjecture.ParallelImplementation.ZeroTraceLowerJetSmallness.zero_trace_lower_jet_smallness
      T alpha hT z hz'
  have hgradSup : ‖z.1.1.1.2.1‖ ≤ 3*N*Real.sqrt T := by
    calc
      ‖z.1.1.1.2.1‖ ≤
          (2*‖z.1.2‖ + ‖z.1.1.1.2.2‖)*Real.sqrt T := hsmall.2
      _ ≤ (2*N + N)*Real.sqrt T := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
        exact add_le_add (mul_le_mul_of_nonneg_left htimeNorm (by norm_num))
          hhessNorm
      _ = 3*N*Real.sqrt T := by ring
  have hslice (t : Set.Icc (0:ℝ) T) :
      (∀ x : EuclideanSpace ℝ (Fin 3),
        HasFDerivAt (fun y => u (t,y)) (grad (t,x)) x) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3),
        HasFDerivAt (fun y => grad (t,y)) (hess (t,x)) x) := by
    simpa [u, grad, hess] using hjet t
  have hC2 (t : Set.Icc (0:ℝ) T) :
      ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => u (t,x)) := by
    simpa [u] using (spaceTime_C2_jet_complete T).2 z.1.1.1 hjet t
  have hgradEq (t : Set.Icc (0:ℝ) T) :
      (fun x => fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => u (t,y)) x) =
        (fun x => grad (t,x)) := by
    funext x
    exact (hslice t).1 x |>.fderiv
  have hHessEq (t : Set.Icc (0:ℝ) T) (x : EuclideanSpace ℝ (Fin 3)) :
      fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => grad (t,w)) x =
        hess (t,x) := by
    exact (hslice t).2 x |>.fderiv
  have hgradPoint (p : Slab T) : ‖grad p‖ ≤ 3*N*Real.sqrt T := by
    calc
      ‖grad p‖ ≤ ‖z.1.1.1.2.1‖ := by
        exact BoundedContinuousFunction.norm_coe_le_norm z.1.1.1.2.1 p
      _ ≤ 3*N*Real.sqrt T := hgradSup
  have hhessPoint (p : Slab T) : ‖hess p‖ ≤ N := by
    calc
      ‖hess p‖ ≤ ‖z.1.1.1.2.2‖ := by
        exact BoundedContinuousFunction.norm_coe_le_norm z.1.1.1.2.2 p
      _ ≤ N := hhessNorm
  have hgradLipschitz (t : Set.Icc (0:ℝ) T)
      (x y : EuclideanSpace ℝ (Fin 3)) :
      ‖grad (t,x)-grad (t,y)‖ ≤ N*‖x-y‖ := by
    have hGdiff : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin 3) => grad (t,x)) := by
      have hGcd : ContDiff ℝ 1
          (fun x : EuclideanSpace ℝ (Fin 3) => grad (t,x)) := by
        rw [← hgradEq t]
        exact (hC2 t).fderiv_right (by norm_num)
      exact hGcd.differentiable_one
    exact (convex_univ : Convex ℝ
      (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hGdiff.differentiableAt)
      (fun w _ => by
        rw [hHessEq t w]
        exact hhessPoint (t,w))
      (Set.mem_univ x) (Set.mem_univ y)
  have hspatial (t : Set.Icc (0:ℝ) T)
      (x y : EuclideanSpace ℝ (Fin 3)) :
      ‖grad (t,x)-grad (t,y)‖ ≤ 6*N*Tf*‖x-y‖^alpha := by
    let d : ℝ := ‖x-y‖
    have hd : 0 ≤ d := by positivity
    have hdPow : 0 ≤ d^alpha := Real.rpow_nonneg hd alpha
    have hsmallD : d ≤ Real.sqrt T ∨ Real.sqrt T ≤ d := le_total d (Real.sqrt T)
    rcases hsmallD with hsmallD | hlargeD
    · calc
        ‖grad (t,x)-grad (t,y)‖ ≤ N*d := by
          simpa [d] using hgradLipschitz t x y
        _ ≤ N*(Tf*d^alpha) := mul_le_mul_of_nonneg_left
          (hscale d hd hsmallD) hN
        _ = N*Tf*d^alpha := by ring
        _ ≤ 6*N*Tf*d^alpha := by nlinarith [mul_nonneg (mul_nonneg hN hTf) hdPow]
    · have hrootScale := hscale (Real.sqrt T) (Real.sqrt_nonneg T) le_rfl
      have hrootPow : (Real.sqrt T)^alpha ≤ d^alpha :=
        Real.rpow_le_rpow (Real.sqrt_nonneg T) hlargeD ha.le
      calc
        ‖grad (t,x)-grad (t,y)‖ ≤ 6*N*Real.sqrt T := by
          calc
            _ ≤ ‖grad (t,x)‖+‖grad (t,y)‖ := norm_sub_le _ _
            _ ≤ 3*N*Real.sqrt T + 3*N*Real.sqrt T :=
              add_le_add (hgradPoint (t,x)) (hgradPoint (t,y))
            _ = 6*N*Real.sqrt T := by ring
        _ ≤ 6*N*(Tf*(Real.sqrt T)^alpha) :=
          mul_le_mul_of_nonneg_left hrootScale (by positivity)
        _ ≤ 6*N*(Tf*d^alpha) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hrootPow hTf
          · positivity
        _ = 6*N*Tf*d^alpha := by ring
  have htemporal (t s : Set.Icc (0:ℝ) T)
      (x : EuclideanSpace ℝ (Fin 3)) :
      ‖grad (t,x)-grad (s,x)‖ ≤
        4*N*Tf*(Real.sqrt |(t:ℝ)-(s:ℝ)|)^alpha := by
    let d : ℝ := |(t:ℝ)-(s:ℝ)|
    have hd : 0 ≤ d := by positivity
    by_cases hd0 : d = 0
    · have htsval : (t:ℝ) = (s:ℝ) := by
        have hzero : |(t:ℝ)-(s:ℝ)| = 0 := hd0
        exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
      have hts : t = s := Subtype.ext htsval
      subst s
      simp [ha.ne']
    · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      have hdT : d ≤ T := by
        dsimp [d]
        apply abs_le.mpr
        constructor <;> nlinarith [t.2.1, t.2.2, s.2.1, s.2.2]
      let r : ℝ := Real.sqrt d
      have hr : 0 < r := by
        dsimp [r]
        exact Real.sqrt_pos.2 hdpos
      have hrT : r ≤ Real.sqrt T := by
        dsimp [r]
        exact Real.sqrt_le_sqrt hdT
      let f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 6) :=
        fun y => u (t,y)-u (s,y)
      have hf : ContDiff ℝ 2 f := by
        dsimp [f]
        exact (hC2 t).sub (hC2 s)
      have hfEq : f =
          (fun y : EuclideanSpace ℝ (Fin 3) => u (t,y)) -
            (fun y => u (s,y)) := by
        funext y
        rfl
      have hgradFun :
          (fun y => fderiv ℝ f y) = (fun y => grad (t,y)-grad (s,y)) := by
        funext y
        have hderiv : HasFDerivAt f (grad (t,y)-grad (s,y)) y := by
          rw [hfEq]
          exact ((hslice t).1 y).sub ((hslice s).1 y)
        exact hderiv.fderiv
      have hgradDiffEq :
          (fun w : EuclideanSpace ℝ (Fin 3) => grad (t,w)-grad (s,w)) =
            (fun w => grad (t,w)) - (fun w => grad (s,w)) := by
        funext w
        rfl
      have hsecondEq (y : EuclideanSpace ℝ (Fin 3)) :
          fderiv ℝ (fderiv ℝ f) y = hess (t,y)-hess (s,y) := by
        calc
          _ = fderiv ℝ (fun w => grad (t,w)-grad (s,w)) y := by
            congr 1
          _ = hess (t,y)-hess (s,y) := by
            rw [hgradDiffEq]
            exact (((hslice t).2 y).sub ((hslice s).2 y)).fderiv
      have hvalue : ∀ y, ‖f y‖ ≤ d*N := by
        intro y
        have htime :=
          PoincareConjecture.ParallelImplementation.SlabTimeLipschitz.slab_time_lipschitz
            T hT.le z.1.1.1.1 z.1.2 hgraph s t y
        have htime' : ‖f y‖ ≤ ‖z.1.2‖*d := by
          simpa [f, d, u] using htime
        calc
          ‖f y‖ ≤ ‖z.1.2‖*d := htime'
          _ ≤ N*d := mul_le_mul_of_nonneg_right htimeNorm hd
          _ = d*N := by ring
      have hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ 2*N := by
        intro y
        calc
          ‖fderiv ℝ (fderiv ℝ f) y‖ = ‖hess (t,y)-hess (s,y)‖ := by
            rw [hsecondEq y]
          _ ≤ ‖hess (t,y)‖+‖hess (s,y)‖ := norm_sub_le _ _
          _ ≤ N+N := add_le_add (hhessPoint (t,y)) (hhessPoint (s,y))
          _ = 2*N := by ring
      have hA : 0 ≤ d*N := mul_nonneg hd hN
      have hM : 0 ≤ 2*N := by positivity
      have hinterp :=
        PoincareConjecture.ParallelImplementation.GradientSupInterpolation.gradient_sup_interpolation
          f hf (d*N) (2*N) r hA hM hr hvalue hsecond
      have hxEq : grad (t,x)-grad (s,x) = fderiv ℝ f x :=
        (congrFun hgradFun x).symm
      have hraw : ‖grad (t,x)-grad (s,x)‖ ≤
          2*(d*N)/r+(2*N)*r := by
        simpa [hxEq] using hinterp x
      have hsquare : r^2 = d := by
        dsimp [r]
        exact Real.sq_sqrt hd
      have hterm : 2*(d*N)/r = 2*N*r := by
        rw [← hsquare]
        field_simp [ne_of_gt hr]
      have hraw' : ‖grad (t,x)-grad (s,x)‖ ≤ 4*N*r := by
        calc
          _ ≤ 2*(d*N)/r+(2*N)*r := hraw
          _ = 4*N*r := by rw [hterm]; ring
      have hscaleR := hscale r (Real.sqrt_nonneg d) hrT
      calc
        ‖grad (t,x)-grad (s,x)‖ ≤ 4*N*r := hraw'
        _ ≤ 4*N*(Tf*r^alpha) :=
          mul_le_mul_of_nonneg_left hscaleR (by positivity)
        _ = 4*N*Tf*r^alpha := by ring
  intro p q
  let rho : ℝ := parabolicRho p q
  let dspace : ℝ := ‖p.2-q.2‖
  let rtime : ℝ := Real.sqrt |(p.1:ℝ)-(q.1:ℝ)|
  have hrho : 0 ≤ rho := by
    dsimp [rho, parabolicRho]
    positivity
  have hdspace : 0 ≤ dspace := by positivity
  have hspaceRho : dspace ≤ rho := by
    dsimp [dspace, rho, parabolicRho]
    have hsqrt : 0 ≤ Real.sqrt |(p.1:ℝ)-(q.1:ℝ)| := Real.sqrt_nonneg _
    linarith [norm_nonneg (p.2-q.2)]
  have htimeRho : rtime ≤ rho := by
    dsimp [rtime, rho, parabolicRho]
    have hnorm : 0 ≤ ‖p.2-q.2‖ := norm_nonneg _
    linarith
  have hspacePow : dspace^alpha ≤ rho^alpha :=
    Real.rpow_le_rpow hdspace hspaceRho ha.le
  have htimePow : rtime^alpha ≤ rho^alpha :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) htimeRho ha.le
  have hcoeff4 : 0 ≤ 4*N*Tf := by positivity
  have hcoeff6 : 0 ≤ 6*N*Tf := by positivity
  have htimeBound :
      ‖grad p-grad (q.1,p.2)‖ ≤ 4*N*Tf*rho^alpha := by
    calc
      ‖grad p-grad (q.1,p.2)‖ ≤
          4*N*Tf*(Real.sqrt |(p.1:ℝ)-(q.1:ℝ)|)^alpha :=
        htemporal p.1 q.1 p.2
      _ = 4*N*Tf*rtime^alpha := by rfl
      _ ≤ 4*N*Tf*rho^alpha := mul_le_mul_of_nonneg_left htimePow hcoeff4
  have hspaceBound : ‖grad (q.1,p.2)-grad q‖ ≤ 6*N*Tf*rho^alpha := by
    calc
      ‖grad (q.1,p.2)-grad q‖ ≤ 6*N*Tf*dspace^alpha :=
        hspatial q.1 p.2 q.2
      _ ≤ 6*N*Tf*rho^alpha := mul_le_mul_of_nonneg_left hspacePow hcoeff6
  have htriangle : ‖grad p-grad q‖ ≤
      ‖grad p-grad (q.1,p.2)‖ + ‖grad (q.1,p.2)-grad q‖ := by
    calc
      ‖grad p-grad q‖ =
          ‖(grad p-grad (q.1,p.2)) + (grad (q.1,p.2)-grad q)‖ := by
            congr 1; abel
      _ ≤ _ := norm_add_le _ _
  calc
    ‖z.1.1.1.2.1 p-z.1.1.1.2.1 q‖ = ‖grad p-grad q‖ := by rfl
    _ ≤ 4*N*Tf*rho^alpha + 6*N*Tf*rho^alpha :=
      htriangle.trans (add_le_add htimeBound hspaceBound)
    _ ≤ 16*N*Tf*rho^alpha := by
      nlinarith [mul_nonneg (mul_nonneg hN hTf) (Real.rpow_nonneg hrho alpha)]
    _ = 16*‖z‖*T^((1-alpha)/2)*parabolicRho p q^alpha := by
      simp [N, Tf, rho]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceGradientHolderSmallness
