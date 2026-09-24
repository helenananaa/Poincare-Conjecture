import PoincareConjecture.ParallelImplementation.TemporalHessianConvolution
import PoincareConjecture.ParallelImplementation.TemporalDuhamelSplit
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.TemporalSchauderIntegral
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.DuhamelHessianTemporalHolder
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Temporal Holder control of the actual untruncated Duhamel Hessian integral. -/
theorem duhamel_hessian_temporal_holder
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L t h : ℝ), 0 ≤ L → 0 ≤ t → 0 < h →
      (∀ s ∈ Icc (0:ℝ) (t+h), ∀ x z : E3, |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) →
      ∀ (x : E3) (i j : Fin 3),
      |(∫ s in (0:ℝ)..(t+h), ∫ y : E3, heatHessian3 (t+h-s) i j y * F (s,x-y)) -
       (∫ s in (0:ℝ)..t, ∫ y : E3, heatHessian3 (t-s) i j y * F (s,x-y))| ≤
        C * L * h^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨Cconv, hCconv, hconv⟩ :=
    PoincareConjecture.ParallelImplementation.TemporalHessianConvolution.heatHessian_convolution_time_modulus
      alpha ha ha1
  obtain ⟨Ctail, hCtail, htail⟩ :=
    MorganTianLib.ParabolicPDE.duhamel_hessian_terminal_tail alpha ha ha1
  let K : ℝ := 2 / alpha + 2 / (2 - alpha)
  let C : ℝ := Cconv * K + Ctail
  have hK : 0 < K := by
    have h2a : 0 < 2 - alpha := by linarith
    dsimp [K]
    exact add_pos (div_pos (by norm_num) ha) (div_pos (by norm_num) h2a)
  have hCpos : 0 < C := by
    dsimp [C]
    exact add_pos (mul_pos hCconv hK) hCtail
  refine ⟨C, ?_, ?_⟩
  · exact hCpos
  · intro F L t h hL ht hh hholder x i j
    let G : ℝ → ℝ := fun s => ∫ y : E3,
      (heatHessian3 (t+h-s) i j y - heatHessian3 (t-s) i j y) * F (s,x-y)
    let q : ℝ → ℝ := fun r => min (r^(alpha/2-1)) (h*r^(alpha/2-2))
    have hsplit :=
      PoincareConjecture.ParallelImplementation.TemporalDuhamelSplit.duhamel_hessian_time_split
        alpha ha ha1 F L t h hL ht hh hholder x i j
    change IntervalIntegrable G volume 0 t ∧
      ((∫ s in (0:ℝ)..(t+h), ∫ y : E3,
          heatHessian3 (t+h-s) i j y * F (s,x-y)) -
       (∫ s in (0:ℝ)..t, ∫ y : E3,
          heatHessian3 (t-s) i j y * F (s,x-y))) =
        (∫ s in (0:ℝ)..t, G s) +
        (∫ s in t..(t+h), ∫ y : E3,
          heatHessian3 (t+h-s) i j y * F (s,x-y)) at hsplit
    obtain ⟨hG, hsplitEq⟩ := hsplit

    obtain ⟨hq, hqBound⟩ :=
      MorganTianLib.MetricCoefficient.temporal_schauder_integral
        alpha h t ha ha1 hh ht
    have hqInt : IntervalIntegrable q volume 0 t := by
      simpa [q] using hq
    have hqBound' : (∫ r in (0:ℝ)..t, q r) ≤ K * h^(alpha/2) := by
      simpa [q, K] using hqBound

    let M : ℝ → ℝ := fun s => (Cconv * L) * q (t-s)
    have hqRev : IntervalIntegrable (fun s => q (t-s)) volume 0 t := by
      have h := hqInt.comp_sub_left t
      simpa using h.symm
    have hMInt : IntervalIntegrable M volume 0 t := by
      dsimp [M]
      exact hqRev.const_mul (Cconv * L)
    have hMIntegral : (∫ s in (0:ℝ)..t, M s) =
        Cconv * L * (∫ r in (0:ℝ)..t, q r) := by
      dsimp [M]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left]
      simp

    have hpoint : ∀ s ∈ Ioo (0:ℝ) t, ‖G s‖ ≤ M s := by
      intro s hs
      have hrs : 0 < t-s := by linarith [hs.2]
      let f : E3 →ᵇ ℝ :=
        F.compContinuous (ContinuousMap.prodMk
          (⟨fun _ : E3 => s, continuous_const⟩ : C(E3, ℝ))
          (⟨fun z : E3 => z, continuous_id⟩ : C(E3, E3)))
      have hslice : ∀ u v : E3, |f u - f v| ≤ L * ‖u-v‖^alpha := by
        intro u v
        have hspt := hholder s
          ⟨le_of_lt hs.1, hs.2.le.trans (by linarith : t ≤ t+h)⟩ u v
        simpa [f] using hspt
      have hmod := hconv f L hL hslice (t-s) h hrs hh x i j
      have htime : t+h-s = (t-s)+h := by ring
      simpa [G, M, q, f, htime, Real.norm_eq_abs] using hmod

    have hMbound : ∀ᵐ s ∂volume, s ∈ Ioc (0:ℝ) t → ‖G s‖ ≤ M s := by
      filter_upwards [Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := t)] with s hs
      intro hsIoc
      exact hpoint s (hs.mpr hsIoc)
    have hpastNorm : ‖∫ s in (0:ℝ)..t, G s‖ ≤ ∫ s in (0:ℝ)..t, M s :=
      intervalIntegral.norm_integral_le_of_norm_le ht hMbound hMInt
    have hpastBound : |∫ s in (0:ℝ)..t, G s| ≤
        (Cconv * L) * (K * h^(alpha/2)) := by
      calc
        |∫ s in (0:ℝ)..t, G s| = ‖∫ s in (0:ℝ)..t, G s‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ ∫ s in (0:ℝ)..t, M s := hpastNorm
        _ = (Cconv * L) * (∫ r in (0:ℝ)..t, q r) := hMIntegral
        _ ≤ (Cconv * L) * (K * h^(alpha/2)) :=
          mul_le_mul_of_nonneg_left hqBound' (mul_nonneg (le_of_lt hCconv) hL)

    have htailRaw := htail F L (t+h) h hL hh.le (by linarith) hholder x i j
    have htailBound :
        |∫ s in t..(t+h), ∫ y : E3,
          heatHessian3 (t+h-s) i j y * F (s,x-y)| ≤ Ctail * L * h^(alpha/2) := by
      simpa [heatHessian3] using htailRaw.2

    have hsum := hsplitEq
    calc
      |(∫ s in (0:ℝ)..(t+h), ∫ y : E3,
          heatHessian3 (t+h-s) i j y * F (s,x-y)) -
       (∫ s in (0:ℝ)..t, ∫ y : E3,
          heatHessian3 (t-s) i j y * F (s,x-y))|
          = |(∫ s in (0:ℝ)..t, G s) +
              (∫ s in t..(t+h), ∫ y : E3,
                heatHessian3 (t+h-s) i j y * F (s,x-y))| := by rw [hsum]
      _ ≤ |∫ s in (0:ℝ)..t, G s| +
          |∫ s in t..(t+h), ∫ y : E3,
            heatHessian3 (t+h-s) i j y * F (s,x-y)| := abs_add_le _ _
      _ ≤ (Cconv * L) * (K * h^(alpha/2)) + Ctail * L * h^(alpha/2) :=
        add_le_add hpastBound htailBound
      _ = C * L * h^(alpha/2) := by
        dsimp [C]
        ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.DuhamelHessianTemporalHolder
