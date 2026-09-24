import PoincareConjecture.ParallelImplementation.HessianSliceIntegrability
import PoincareConjecture.ParallelImplementation.DuhamelPastIntegrability
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.GaussianHessianTimeDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.TemporalDuhamelSplit
open MorganTianLib.MetricCoefficient
open Set MeasureTheory
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The actual time-difference splits into a past integral and a terminal tail. -/
theorem duhamel_hessian_time_split
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (F : (ℝ × E3) →ᵇ ℝ) (L t h : ℝ) (hL : 0 ≤ L) (ht : 0 ≤ t) (hh : 0 < h)
    (hholder : ∀ s ∈ Icc (0:ℝ) (t+h), ∀ x z : E3,
      |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha) (x : E3) (i j : Fin 3) :
    let G : ℝ → ℝ := fun s => ∫ y : E3,
      (heatHessian3 (t+h-s) i j y - heatHessian3 (t-s) i j y) * F (s,x-y)
    IntervalIntegrable G volume 0 t ∧
    ((∫ s in (0:ℝ)..(t+h), ∫ y : E3, heatHessian3 (t+h-s) i j y * F (s,x-y)) -
     (∫ s in (0:ℝ)..t, ∫ y : E3, heatHessian3 (t-s) i j y * F (s,x-y))) =
      (∫ s in (0:ℝ)..t, G s) +
      (∫ s in t..(t+h), ∫ y : E3, heatHessian3 (t+h-s) i j y * F (s,x-y)) :=
/- SWARM_PROOF_BEGIN -/
by
  let A : ℝ → ℝ := fun s => ∫ y : E3,
    heatHessian3 (t+h-s) i j y * F (s,x-y)
  let B : ℝ → ℝ := fun s => ∫ y : E3,
    heatHessian3 (t-s) i j y * F (s,x-y)
  let G : ℝ → ℝ := fun s => ∫ y : E3,
    (heatHessian3 (t+h-s) i j y - heatHessian3 (t-s) i j y) * F (s,x-y)
  change IntervalIntegrable G volume 0 t ∧
    ((∫ s in (0:ℝ)..(t+h), A s) - (∫ s in (0:ℝ)..t, B s)) =
      (∫ s in (0:ℝ)..t, G s) + (∫ s in t..(t+h), A s)

  have hAfull : IntervalIntegrable A volume 0 (t+h) := by
    simpa [A] using
      (PoincareConjecture.ParallelImplementation.DuhamelPastIntegrability.duhamel_hessian_initial_interval_integrable
        alpha ha ha1 F L (t+h) (t+h) hL (by linarith) (by linarith) (by rfl)
        hholder x i j)
  have hA0 : IntervalIntegrable A volume 0 t := by
    simpa [A] using
      (PoincareConjecture.ParallelImplementation.DuhamelPastIntegrability.duhamel_hessian_initial_interval_integrable
        alpha ha ha1 F L (t+h) t hL (by linarith) ht (by linarith)
        hholder x i j)
  have hholder_t : ∀ s ∈ Icc (0:ℝ) t, ∀ x z : E3,
      |F (s,x)-F (s,z)| ≤ L*‖x-z‖^alpha := by
    intro s hs x0 z0
    apply hholder s
    exact ⟨hs.1, le_trans hs.2 (le_add_of_nonneg_right hh.le)⟩
  have hB0 : IntervalIntegrable B volume 0 t := by
    simpa [B] using
      (PoincareConjecture.ParallelImplementation.DuhamelPastIntegrability.duhamel_hessian_initial_interval_integrable
        alpha ha ha1 F L t t hL ht ht (by rfl)
        hholder_t x i j)
  have hAtail : IntervalIntegrable A volume t (t+h) := by
    apply hAfull.mono_set
    rw [Set.uIcc_of_le (le_add_of_nonneg_right hh.le),
      Set.uIcc_of_le (show (0:ℝ) ≤ t+h by linarith)]
    intro s hs
    exact ⟨ht.trans hs.1, hs.2⟩

  have hD : IntervalIntegrable (fun s => A s - B s) volume 0 t := hA0.sub hB0
  have hDOnIoc : IntegrableOn (fun s => A s - B s) (Ioc (0:ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hD

  have hEqIoo : EqOn (fun s => A s - B s) G (Ioo (0:ℝ) t) := by
    intro s hs
    by_cases ht0 : t = 0
    · subst t
      simp at hs
    · have hr1 : 0 < t+h-s := by linarith [hs.1, hs.2, hh]
      have hr2 : 0 < t-s := by linarith [hs.2]
      have hslice1 : Integrable
          (fun y : E3 => heatHessian3 (t+h-s) i j y * F (s,x-y)) volume :=
        PoincareConjecture.ParallelImplementation.HessianSliceIntegrability.heatHessian_time_slice_integrable
          F (t+h-s) s hr1 x i j
      have hslice2 : Integrable
          (fun y : E3 => heatHessian3 (t-s) i j y * F (s,x-y)) volume :=
        PoincareConjecture.ParallelImplementation.HessianSliceIntegrability.heatHessian_time_slice_integrable
          F (t-s) s hr2 x i j
      change
        (∫ y : E3, heatHessian3 (t+h-s) i j y * F (s,x-y)) -
          (∫ y : E3, heatHessian3 (t-s) i j y * F (s,x-y)) =
        ∫ y : E3, (heatHessian3 (t+h-s) i j y - heatHessian3 (t-s) i j y) *
          F (s,x-y)
      calc
        _ = ∫ y : E3,
            (heatHessian3 (t+h-s) i j y * F (s,x-y) -
              heatHessian3 (t-s) i j y * F (s,x-y)) :=
          (integral_sub hslice1 hslice2).symm
        _ = ∫ y : E3,
            (heatHessian3 (t+h-s) i j y - heatHessian3 (t-s) i j y) *
              F (s,x-y) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y => by ring)

  have hGOnIoc : IntegrableOn G (Ioc (0:ℝ) t) volume := by
    have hDOnIoo : IntegrableOn (fun s => A s - B s) (Ioo (0:ℝ) t) volume :=
      hDOnIoc.mono_set (by
        intro s hs
        exact ⟨hs.1, hs.2.le⟩)
    have hGOnIoo : IntegrableOn G (Ioo (0:ℝ) t) volume :=
      hDOnIoo.congr_fun hEqIoo measurableSet_Ioo
    exact hGOnIoo.congr_set_ae Ioo_ae_eq_Ioc.symm
  have hG : IntervalIntegrable G volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hGOnIoc

  have hDiff :
      (∫ s in (0:ℝ)..t, A s) - (∫ s in (0:ℝ)..t, B s) =
        ∫ s in (0:ℝ)..t, G s := by
    rw [← intervalIntegral.integral_sub hA0 hB0]
    exact intervalIntegral.integral_congr_Ioo_of_le ht hEqIoo

  constructor
  · exact hG
  · calc
      (∫ s in (0:ℝ)..(t+h), A s) - (∫ s in (0:ℝ)..t, B s) =
          ((∫ s in (0:ℝ)..t, A s) + (∫ s in t..(t+h), A s)) -
            (∫ s in (0:ℝ)..t, B s) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hA0 hAtail]
      _ = ((∫ s in (0:ℝ)..t, A s) - (∫ s in (0:ℝ)..t, B s)) +
            (∫ s in t..(t+h), A s) := by ring
      _ = (∫ s in (0:ℝ)..t, G s) + (∫ s in t..(t+h), A s) := by
        rw [hDiff]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.TemporalDuhamelSplit
