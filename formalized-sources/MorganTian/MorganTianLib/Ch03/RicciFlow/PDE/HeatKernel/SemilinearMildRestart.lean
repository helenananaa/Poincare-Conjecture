import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelRestart
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelTerminalQuotient
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.CompactSpatialDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedNemytskiiOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.ParabolicPDE
open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual restart identity for the already constructed semilinear integral solution. -/
theorem semilinear_mild_restart (f : E3 →ᵇ ℝ) (N : ℝ → ℝ) (L T : ℝ) (hL : 0≤L)
    (hN : ∀ a b : ℝ, |N a-N b|≤L*|a-b|) (u : (ℝ × E3) →ᵇ ℝ)
    (hu : ∀ t : ℝ, 0<t → t≤T → ∀ x : E3,
      u (t,x)=(∫ y : E3, euclideanHeatKernel 3 t y*f (x-y))+
        ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y*N (u (s,x-y)))
    (S h : ℝ) (hS : 0<S) (hh : 0<h) (hST : S+h≤T) (x : E3) :
    u (S+h,x)=(∫ y : E3, euclideanHeatKernel 3 h y*u (S,x-y))+
      ∫ s in S..(S+h), ∫ y : E3, euclideanHeatKernel 3 (S+h-s) y*N (u (s,x-y)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨B, hB, -, -⟩ := bounded_nemytskii_operator N L hL hN
  let F : (ℝ × E3) →ᵇ ℝ := B u
  have hF (s : ℝ) (y : E3) : F (s, y) = N (u (s, y)) := by
    dsimp [F]
    exact hB u (s, y)
  obtain ⟨A, hA, hsemigroup⟩ := exists_three_dimensional_bounded_heat_semigroup
  have hST0 : S ≤ T := by linarith
  have hShpos : 0 < S + h := by linarith
  have hrestart := duhamel_restart_identity F S h hS.le hh x
  have hrestartN :
      (∫ s in (0 : ℝ)..(S+h), ∫ y : E3,
          euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y))) =
        (∫ z : E3, euclideanHeatKernel 3 h z *
          (∫ s in (0 : ℝ)..S, ∫ y : E3,
            euclideanHeatKernel 3 (S-s) y * N (u (s,x-z-y)))) +
          ∫ s in S..(S+h), ∫ y : E3,
            euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y)) := by
    simpa only [hF] using hrestart
  let uS : E3 →ᵇ ℝ := u.compContinuous
    ⟨fun y : E3 => (S, y), continuous_const.prodMk continuous_id⟩
  let PS : E3 →ᵇ ℝ := A S f
  let DS : E3 →ᵇ ℝ := uS - PS
  have huS_decomp : uS = PS + DS := by
    apply BoundedContinuousFunction.ext
    intro y
    simp [DS]
  have hDpoint (y : E3) :
      DS y = ∫ s in (0 : ℝ)..S, ∫ z : E3,
        euclideanHeatKernel 3 (S-s) z * N (u (s,y-z)) := by
    dsimp [DS, uS, PS]
    rw [hu S hS hST0 y, ((hA S hS).2 f y).2]
    ring
  have hPSint : Integrable
      (fun z : E3 => euclideanHeatKernel 3 h z * PS (x-z)) volume :=
    (hA h hh).2 PS x |>.1
  have hDSint : Integrable
      (fun z : E3 => euclideanHeatKernel 3 h z * DS (x-z)) volume :=
    (hA h hh).2 DS x |>.1
  have hIntegralAdd :
      (∫ z : E3, euclideanHeatKernel 3 h z * (PS + DS) (x-z)) =
        (∫ z : E3, euclideanHeatKernel 3 h z * PS (x-z)) +
          ∫ z : E3, euclideanHeatKernel 3 h z * DS (x-z) := by
    have heq :
        (fun z : E3 => euclideanHeatKernel 3 h z * (PS + DS) (x-z)) =
          (fun z : E3 => euclideanHeatKernel 3 h z * PS (x-z)) +
            (fun z : E3 => euclideanHeatKernel 3 h z * DS (x-z)) := by
      funext z
      rw [BoundedContinuousFunction.add_apply]
      simp only [Pi.add_apply]
      ring
    rw [heq]
    exact integral_add hPSint hDSint
  have hAh_sum : A h uS x = A h PS x + A h DS x := by
    calc
      A h uS x = ∫ z : E3, euclideanHeatKernel 3 h z * uS (x-z) :=
        (hA h hh).2 uS x |>.2
      _ = ∫ z : E3, euclideanHeatKernel 3 h z * (PS + DS) (x-z) := by
        rw [huS_decomp]
      _ = (∫ z : E3, euclideanHeatKernel 3 h z * PS (x-z)) +
          ∫ z : E3, euclideanHeatKernel 3 h z * DS (x-z) := hIntegralAdd
      _ = A h PS x + A h DS x := by
        rw [(hA h hh).2 PS x |>.2, (hA h hh).2 DS x |>.2]
  have hsemf : A h (A S f) x = A (S+h) f x := by
    have hs := hsemigroup h S hh hS
    calc
      A h (A S f) x = ((A h).comp (A S)) f x := rfl
      _ = A (h+S) f x := by rw [← hs]
      _ = A (S+h) f x := by rw [add_comm]
  have hinitial :
      (∫ y : E3, euclideanHeatKernel 3 (S+h) y * f (x-y)) = A h PS x := by
    calc
      (∫ y : E3, euclideanHeatKernel 3 (S+h) y * f (x-y)) =
          A (S+h) f x := ((hA (S+h) hShpos).2 f x).2.symm
      _ = A h (A S f) x := hsemf.symm
      _ = A h PS x := by rfl
  have hDSnonlin :
      A h DS x = ∫ z : E3, euclideanHeatKernel 3 h z *
        (∫ s in (0 : ℝ)..S, ∫ y : E3,
          euclideanHeatKernel 3 (S-s) y * N (u (s,x-z-y))) := by
    calc
      A h DS x = ∫ z : E3, euclideanHeatKernel 3 h z * DS (x-z) :=
        (hA h hh).2 DS x |>.2
      _ = ∫ z : E3, euclideanHeatKernel 3 h z *
          (∫ s in (0 : ℝ)..S, ∫ y : E3,
            euclideanHeatKernel 3 (S-s) y * N (u (s,x-z-y))) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hDpoint]
  calc
    u (S+h,x) =
        (∫ y : E3, euclideanHeatKernel 3 (S+h) y * f (x-y)) +
          ∫ s in (0 : ℝ)..(S+h), ∫ y : E3,
            euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y)) :=
      hu (S+h) hShpos hST x
    _ = (∫ y : E3, euclideanHeatKernel 3 (S+h) y * f (x-y)) +
          ((∫ z : E3, euclideanHeatKernel 3 h z *
            (∫ s in (0 : ℝ)..S, ∫ y : E3,
              euclideanHeatKernel 3 (S-s) y * N (u (s,x-z-y)))) +
            ∫ s in S..(S+h), ∫ y : E3,
              euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y))) := by
      rw [hrestartN]
    _ = A h PS x + (A h DS x +
          ∫ s in S..(S+h), ∫ y : E3,
            euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y))) := by
      rw [hinitial, ← hDSnonlin]
    _ = A h uS x +
          ∫ s in S..(S+h), ∫ y : E3,
            euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y)) := by
      rw [hAh_sum]
      ring
    _ = (∫ y : E3, euclideanHeatKernel 3 h y * uS (x-y)) +
          ∫ s in S..(S+h), ∫ y : E3,
            euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y)) := by
      rw [(hA h hh).2 uS x |>.2]
    _ = (∫ y : E3, euclideanHeatKernel 3 h y * u (S,x-y)) +
          ∫ s in S..(S+h), ∫ y : E3,
            euclideanHeatKernel 3 (S+h-s) y * N (u (s,x-y)) := by
      rfl
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
