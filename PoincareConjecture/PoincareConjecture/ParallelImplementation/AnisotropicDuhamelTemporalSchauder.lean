import PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder
import PoincareConjecture.ParallelImplementation.LinearHessianDifferenceTransport
import PoincareConjecture.ParallelImplementation.AnisotropicDuhamelIdentity
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.AnisotropicHeatKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AnisotropicDuhamelTemporalSchauder
open MorganTianLib.MetricCoefficient Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Actual anisotropic Duhamel Hessians satisfy temporal Schauder control, including time zero. -/
theorem anisotropic_duhamel_temporal_schauder
    (B : E3 ≃L[ℝ] E3) (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L t h : ℝ), 0 ≤ L → 0 ≤ t → 0 < h →
      (∀ s ∈ Icc (0:ℝ) (t+h), ∀ x z : E3, |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) →
      let u : ℝ → E3 → ℝ := fun T x => ∫ s in (0:ℝ)..T, ∫ y : E3,
        anisotropicHeatKernel B (T-s) (x-y) * F (s,y)
      ∀ (x : E3) (i j : Fin 3),
      |fderiv ℝ (fun z => fderiv ℝ (u (t+h)) z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) -
       fderiv ℝ (fun z => fderiv ℝ (u t) z (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)| ≤
        C * L * h^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨Ciso, hCiso, hiso⟩ :=
    PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder.actual_duhamel_temporal_schauder
      alpha ha ha1
  obtain ⟨Csp, hCsp, hsp⟩ :=
    MorganTianLib.ParabolicPDE.full_duhamel_spatial_C2 alpha ha ha1
  let Bc : E3 →L[ℝ] E3 := B
  let S : E3 →L[ℝ] E3 := B.symm
  let C : ℝ := 1 + 9 * Ciso * ‖S‖ ^ 2 * ‖Bc‖ ^ alpha
  have hBpow : 0 ≤ ‖Bc‖ ^ alpha := Real.rpow_nonneg (norm_nonneg Bc) _
  have hcoef : 0 ≤ 9 * Ciso * ‖S‖ ^ 2 * ‖Bc‖ ^ alpha := by
    positivity
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    linarith
  · intro F L t h hL ht hh hholder u x i j
    let G : (ℝ × E3) →ᵇ ℝ :=
      BoundedContinuousFunction.mk
        (ContinuousMap.mk (fun p : ℝ × E3 => F (p.1, B p.2)) (by fun_prop))
        ⟨2 * ‖F‖, by
          intro p q
          calc
            dist (F (p.1, B p.2)) (F (q.1, B q.2)) ≤
                ‖F (p.1, B p.2)‖ + ‖F (q.1, B q.2)‖ := dist_le_norm_add_norm _ _
            _ ≤ ‖F‖ + ‖F‖ := add_le_add
              (BoundedContinuousFunction.norm_coe_le_norm F (p.1, B p.2))
              (BoundedContinuousFunction.norm_coe_le_norm F (q.1, B q.2))
            _ = 2 * ‖F‖ := by ring⟩
    let LL : ℝ := L * ‖Bc‖ ^ alpha
    have hLL : 0 ≤ LL := by dsimp [LL]; exact mul_nonneg hL hBpow
    have hGholder : ∀ s ∈ Icc (0 : ℝ) (t + h), ∀ x z : E3,
        |G (s, x) - G (s, z)| ≤ LL * ‖x - z‖ ^ alpha := by
      intro s hs x z
      have hnorm : ‖Bc x - Bc z‖ ≤ ‖Bc‖ * ‖x - z‖ := by
        calc
          ‖Bc x - Bc z‖ = ‖Bc (x - z)‖ := by rw [← map_sub]
          _ ≤ ‖Bc‖ * ‖x - z‖ := Bc.le_opNorm _
      calc
        |G (s, x) - G (s, z)| = |F (s, B x) - F (s, B z)| := rfl
        _ ≤ L * ‖Bc x - Bc z‖ ^ alpha := hholder s hs (B x) (B z)
        _ ≤ L * (‖Bc‖ * ‖x - z‖) ^ alpha :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hnorm (le_of_lt ha)) hL
        _ = L * (‖Bc‖ ^ alpha * ‖x - z‖ ^ alpha) := by
          rw [Real.mul_rpow (norm_nonneg Bc) (norm_nonneg _)]
        _ = LL * ‖x - z‖ ^ alpha := by dsimp [LL]; ring
    let v : ℝ → E3 → ℝ := fun T z => ∫ s in (0 : ℝ)..T, ∫ w : E3,
      MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (T - s) (z - w) * G (s, w)
    have hpow : 0 ≤ h ^ (alpha / 2) := Real.rpow_nonneg (le_of_lt hh) _
    have hIsoBound : ∀ x i j,
        |fderiv ℝ (fun z => fderiv ℝ (v (t + h)) z (EuclideanSpace.single i 1)) x
             (EuclideanSpace.single j 1) -
         fderiv ℝ (fun z => fderiv ℝ (v t) z (EuclideanSpace.single i 1)) x
             (EuclideanSpace.single j 1)| ≤ Ciso * LL * h ^ (alpha / 2) := by
      intro x i j
      simpa [v, LL] using hiso G LL t h hLL ht hh hGholder x i j
    have hGholderPast : ∀ s ∈ Icc (0 : ℝ) t, ∀ x z : E3,
        |G (s, x) - G (s, z)| ≤ LL * ‖x - z‖ ^ alpha := by
      intro s hs x z
      apply hGholder s ⟨hs.1, hs.2.trans (by linarith)⟩
    have hVplus : ContDiff ℝ 2 (fun z : E3 => v (t + h) z) := by
      simpa [v] using (hsp G LL (t + h) hLL (by linarith) hGholder).1
    have hVpast : ContDiff ℝ 2 (fun z : E3 => v t z) := by
      by_cases ht0 : t = 0
      · subst t
        have hz : (fun z : E3 => v 0 z) = fun _ => (0 : ℝ) := by
          funext z
          simp [v]
        rw [hz]
        fun_prop
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        simpa [v] using (hsp G LL t hLL htpos hGholderPast).1
    let f : E3 → ℝ := fun z => v (t + h) z
    let g : E3 → ℝ := fun z => v t z
    have hf : ContDiff ℝ 2 f := by simpa [f] using hVplus
    have hg : ContDiff ℝ 2 g := by simpa [g] using hVpast
    have hK : 0 ≤ Ciso * LL * h ^ (alpha / 2) := by
      dsimp [LL]
      positivity
    have htrans :=
      PoincareConjecture.ParallelImplementation.LinearHessianDifferenceTransport.linear_pullback_hessian_difference_bound
        f g hf hg S (Ciso * LL * h ^ (alpha / 2)) hK hIsoBound
    have hSapply (y : E3) : S y = B.symm y := rfl
    have hPullPlus : (fun y : E3 => f (S y)) = fun y => u (t + h) y := by
      funext y
      dsimp [f, v, G, u]
      rw [hSapply]
      exact (PoincareConjecture.ParallelImplementation.AnisotropicDuhamelIdentity.anisotropic_duhamel_eq_pullback
        B F (t + h) (by linarith) y).symm
    have hPullPast : (fun y : E3 => g (S y)) = fun y => u t y := by
      funext y
      dsimp [g, v, G, u]
      rw [hSapply]
      exact (PoincareConjecture.ParallelImplementation.AnisotropicDuhamelIdentity.anisotropic_duhamel_eq_pullback
        B F t ht y).symm
    have hAnisoBound :
        |fderiv ℝ (fun z => fderiv ℝ (u (t + h)) z (EuclideanSpace.single i 1)) x
             (EuclideanSpace.single j 1) -
         fderiv ℝ (fun z => fderiv ℝ (u t) z (EuclideanSpace.single i 1)) x
             (EuclideanSpace.single j 1)| ≤
          9 * (Ciso * LL * h ^ (alpha / 2)) * ‖S‖ ^ 2 := by
      simpa only [← hPullPlus, ← hPullPast] using htrans x i j
    calc
      _ ≤ 9 * (Ciso * LL * h ^ (alpha / 2)) * ‖S‖ ^ 2 := hAnisoBound
      _ = (9 * Ciso * ‖S‖ ^ 2 * ‖Bc‖ ^ alpha) * (L * h ^ (alpha / 2)) := by
        dsimp [LL]
        ring
      _ ≤ (1 + 9 * Ciso * ‖S‖ ^ 2 * ‖Bc‖ ^ alpha) * (L * h ^ (alpha / 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hL hpow)
      _ = C * L * h ^ (alpha / 2) := by dsimp [C]; ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AnisotropicDuhamelTemporalSchauder
