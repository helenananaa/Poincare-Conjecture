import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.RicciLowerOrder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual lower-order nonlinearity is smooth and locally Lipschitz in the metric and first jets. -/
theorem ricci_lower_order_local_control (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (i j : Fin 3) :
    let F := fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => ricciLowerOrder q.1 q.2 i j
    ContDiffAt ℝ ∞ F (A,P) ∧ ∃ r K : ℝ, 0<r ∧ 0<K ∧
      ∀ q z, ‖q-(A,P)‖<r → ‖z-(A,P)‖<r → |F q-F z|≤K*‖q-z‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  have hInv : ContDiffAt ℝ ∞
      (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInv' : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => q.1.inverse) (A, P) :=
    hInv.comp (A, P) contDiffAt_fst
  have hP : ∀ r : Fin 3, ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => q.2 r) (A, P) := by
    intro r
    fun_prop
  have hcoord : ∀ (r l s : Fin 3), ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        (q.2 r (EuclideanSpace.single l 1)) s) (A, P) := by
    intro r l s
    fun_prop
  have hChristoffel : ∀ (k a b : Fin 3), ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        coordinateChristoffel q.1 q.2 k a b) (A, P) := by
    intro k a b
    have hterm : ∀ l : Fin 3, ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          q.1.inverse (EuclideanSpace.single l 1) k *
            ((q.2 a (EuclideanSpace.single l 1)) b +
              (q.2 b (EuclideanSpace.single l 1)) a -
                (q.2 l (EuclideanSpace.single b 1)) a)) (A, P) := by
      intro l
      have hinv_l : ContDiffAt ℝ ∞
          (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
            q.1.inverse (EuclideanSpace.single l 1) k) (A, P) := by
        simpa [Function.comp_def, EuclideanSpace.coe_proj] using
          ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp (A, P)
            (hInv'.clm_apply contDiffAt_const))
      exact hinv_l.mul ((hcoord a l b).add (hcoord b l a) |>.sub (hcoord l b a))
    have hsum : ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ∑ l : Fin 3,
            q.1.inverse (EuclideanSpace.single l 1) k *
              ((q.2 a (EuclideanSpace.single l 1)) b +
                (q.2 b (EuclideanSpace.single l 1)) a -
                  (q.2 l (EuclideanSpace.single b 1)) a)) (A, P) := by
      simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun l _ => hterm l))
    simpa [coordinateChristoffel] using hsum.const_smul (1 / 2 : ℝ)
  have hJetComp : ∀ r : Fin 3, ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        q.1.inverse.comp ((q.2 r).comp q.1.inverse)) (A, P) := by
    intro r
    exact hInv'.clm_comp ((hP r).clm_comp hInv')
  have hLower : ∀ (r k a b : Fin 3), ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        lowerConnectionJet q.1 q.2 r k a b) (A, P) := by
    intro r k a b
    have hterm : ∀ l : Fin 3, ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          (-(q.1.inverse.comp ((q.2 r).comp q.1.inverse)))
              (EuclideanSpace.single l 1) k *
            ((q.2 a (EuclideanSpace.single l 1)) b +
              (q.2 b (EuclideanSpace.single l 1)) a -
                (q.2 l (EuclideanSpace.single b 1)) a)) (A, P) := by
      intro l
      have hfirst : ContDiffAt ℝ ∞
          (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
            (-(q.1.inverse.comp ((q.2 r).comp q.1.inverse)))
                (EuclideanSpace.single l 1) k) (A, P) := by
        simpa [Function.comp_def, EuclideanSpace.coe_proj] using
          ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp (A, P)
            (((hJetComp r).neg).clm_apply contDiffAt_const))
      exact hfirst.mul ((hcoord a l b).add (hcoord b l a) |>.sub (hcoord l b a))
    have hsum : ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ∑ l : Fin 3,
            (-(q.1.inverse.comp ((q.2 r).comp q.1.inverse)))
                (EuclideanSpace.single l 1) k *
              ((q.2 a (EuclideanSpace.single l 1)) b +
                (q.2 b (EuclideanSpace.single l 1)) a -
                  (q.2 l (EuclideanSpace.single b 1)) a)) (A, P) := by
      simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun l _ => hterm l))
    simpa [lowerConnectionJet] using hsum.const_smul (1 / 2 : ℝ)
  have hQuadratic : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        quadraticRicciProduct q.1 q.2 i j) (A, P) := by
    have hterm : ∀ k l : Fin 3, ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          coordinateChristoffel q.1 q.2 k k l * coordinateChristoffel q.1 q.2 l i j -
            coordinateChristoffel q.1 q.2 k j l * coordinateChristoffel q.1 q.2 l i k)
        (A, P) := by
      intro k l
      exact (hChristoffel k k l).mul (hChristoffel l i j) |>.sub
        ((hChristoffel k j l).mul (hChristoffel l i k))
    have hinner : ∀ k : Fin 3, ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ∑ l : Fin 3,
            (coordinateChristoffel q.1 q.2 k k l * coordinateChristoffel q.1 q.2 l i j -
              coordinateChristoffel q.1 q.2 k j l * coordinateChristoffel q.1 q.2 l i k))
        (A, P) := by
      intro k
      simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun l _ => hterm k l))
    have hsum : ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ∑ k : Fin 3, ∑ l : Fin 3,
            (coordinateChristoffel q.1 q.2 k k l * coordinateChristoffel q.1 q.2 l i j -
              coordinateChristoffel q.1 q.2 k j l * coordinateChristoffel q.1 q.2 l i k))
        (A, P) := by
      simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun k _ => hinner k))
    simpa [quadraticRicciProduct] using hsum
  have hF : ContDiffAt ℝ ∞
      (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        ricciLowerOrder q.1 q.2 i j) (A, P) := by
    have hterm : ∀ k : Fin 3, ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          lowerConnectionJet q.1 q.2 k k i j -
            lowerConnectionJet q.1 q.2 j k i k) (A, P) := by
      intro k
      exact (hLower k k i j).sub (hLower j k i k)
    have hsum : ContDiffAt ℝ ∞
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ∑ k : Fin 3,
            (lowerConnectionJet q.1 q.2 k k i j -
              lowerConnectionJet q.1 q.2 j k i k)) (A, P) := by
      simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun k _ => hterm k))
    simpa [ricciLowerOrder] using hsum.add hQuadratic
  constructor
  · exact hF
  · obtain ⟨U, hU, hFU⟩ := hF.contDiffOn (m := (1 : ℕ∞ω)) (by simp) (by simp)
    obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU
    have hBall : ContDiffOn ℝ (1 : ℕ∞ω)
        (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ricciLowerOrder q.1 q.2 i j) (Metric.ball (A, P) ρ) :=
      hFU.mono hρU
    have hDeriv : ContinuousOn
        (fderiv ℝ (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ricciLowerOrder q.1 q.2 i j)) (Metric.ball (A, P) ρ) :=
      hBall.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)
    let r : ℝ := ρ / 2
    have hr : 0 < r := by
      dsimp [r]
      linarith
    have hrho : r < ρ := by
      dsimp [r]
      linarith
    have hclosedsub : Metric.closedBall (A, P) r ⊆ Metric.ball (A, P) ρ := by
      intro q hq
      rw [Metric.mem_closedBall] at hq
      change dist q (A, P) < ρ
      exact lt_of_le_of_lt hq hrho
    have hballsub : Metric.ball (A, P) r ⊆ Metric.ball (A, P) ρ :=
      Metric.ball_subset_closedBall.trans hclosedsub
    have hDerivClosed := hDeriv.mono hclosedsub
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (A, P) r).exists_bound_of_continuousOn hDerivClosed
    have hCnonneg : 0 ≤ C := by
      have hx : (A, P) ∈ Metric.closedBall (A, P) r :=
        Metric.mem_closedBall_self hr.le
      exact (norm_nonneg _).trans (hC (A, P) hx)
    let K : ℝ := C + 1
    have hK : 0 < K := by
      dsimp [K]
      linarith
    have hbound : ∀ q ∈ Metric.ball (A, P) r,
        ‖fderiv ℝ (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ricciLowerOrder q.1 q.2 i j) q‖ ≤ K := by
      intro q hq
      have hq' := hC q (Metric.ball_subset_closedBall hq)
      dsimp [K]
      linarith
    have hdiff : ∀ q ∈ Metric.ball (A, P) r,
        DifferentiableAt ℝ
          (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
            ricciLowerOrder q.1 q.2 i j) q := by
      intro q hq
      have hDiffOn := (hBall.mono hballsub).differentiableOn (by simp)
      exact hDiffOn.differentiableAt (Metric.isOpen_ball.mem_nhds hq)
    refine ⟨r, K, hr, hK, ?_⟩
    intro q z hq hz
    have hq' : q ∈ Metric.ball (A, P) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hq
    have hz' : z ∈ Metric.ball (A, P) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hz
    have hm :
        ‖(fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
            ricciLowerOrder q.1 q.2 i j) q -
          (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
            ricciLowerOrder q.1 q.2 i j) z‖ ≤ K * ‖q - z‖ := by
      exact (convex_ball (A, P) r).norm_image_sub_le_of_norm_fderiv_le
        (f := fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ricciLowerOrder q.1 q.2 i j)
        (C := K) (x := z) (y := q) hdiff hbound hz' hq'
    simpa [Real.norm_eq_abs] using hm
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
