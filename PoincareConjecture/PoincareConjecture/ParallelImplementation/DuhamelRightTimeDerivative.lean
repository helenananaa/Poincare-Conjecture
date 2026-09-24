import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelRestart
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelTerminalQuotient
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.HeatGeneratorC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.DuhamelRightTimeDerivative
open MorganTianLib.ParabolicPDE Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- A genuine one-sided time derivative of the actual forced heat solution, without assuming a PDE. -/
theorem duhamel_right_time_derivative
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 < T)
    (hholder : ∀ s ∈ Icc (0:ℝ) T, ∀ x y : E3,
      |F (s,x)-F (s,y)| ≤ L*‖x-y‖^alpha) :
    let u : ℝ → E3 → ℝ := fun t x => ∫ s in (0:ℝ)..t,
      ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)
    ∀ t ∈ Ioo (0:ℝ) T, ∀ x : E3,
      HasDerivWithinAt (fun s => u s x)
        ((∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u t) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) + F (t,x)) (Ici t) t :=
/- SWARM_PROOF_BEGIN -/
by
  intro u t ht x
  rcases ht with ⟨ht0, htT⟩
  obtain ⟨D, hD, hDbound, hDlip⟩ := clipped_duhamel_operator T hT.le
  let V := D F
  have hclip (s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T) : max 0 (min T s) = s := by
    rw [min_eq_right hsT, max_eq_right hs0]
  have hVformula (s : ℝ) (z : E3) (hs0 : 0 ≤ s) (hsT : s ≤ T) :
      V (s,z) = ∫ r in (0:ℝ)..s,
        ∫ y : E3, euclideanHeatKernel 3 (s-r) y * F (r,z-y) := by
    rw [hD F (s,z), hclip s hs0 hsT]
  have hspace (r a : ℝ) (z : E3) :
      (∫ y : E3, euclideanHeatKernel 3 a (z-y) * F (r,y)) =
        ∫ y : E3, euclideanHeatKernel 3 a y * F (r,z-y) := by
    let g : E3 → ℝ := fun y => euclideanHeatKernel 3 a (z-y) * F (r,y)
    have hMP : MeasurePreserving (fun y : E3 => z-y) volume volume :=
      MeasureTheory.Measure.measurePreserving_sub_left volume z
    have hME : MeasurableEmbedding (fun y : E3 => z-y) :=
      (MeasurableEquiv.subLeft z).measurableEmbedding
    calc
      (∫ y : E3, euclideanHeatKernel 3 a (z-y) * F (r,y)) = ∫ y : E3, g y := rfl
      _ = ∫ y : E3, g (z-y) := (hMP.integral_comp hME g).symm
      _ = ∫ y : E3, euclideanHeatKernel 3 a y * F (r,z-y) := by
        congr 1
        funext y
        simp [g]
  have hslice (s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T) (z : E3) :
      V (s,z) = ∫ r in (0:ℝ)..s,
        ∫ y : E3, euclideanHeatKernel 3 (s-r) (z-y) * F (r,y) := by
    rw [hVformula s z hs0 hsT]
    apply intervalIntegral.integral_congr
    intro r hr
    exact (hspace r (s-r) z).symm
  have hident (s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T) (z : E3) :
      u s z = V (s,z) := by
    simpa [u] using (hslice s hs0 hsT z).symm
  let sliceMap : C(E3, ℝ × E3) :=
    (ContinuousMap.const E3 t).prodMk (ContinuousMap.id E3)
  let f : E3 →ᵇ ℝ := V.compContinuous sliceMap
  have hfeval (z : E3) : f z = V (t,z) := rfl
  have hfun : (f : E3 → ℝ) = u t := by
    funext z
    rw [hfeval, hident t ht0.le htT.le z]
  obtain ⟨C, hCpos, hC⟩ := full_duhamel_spatial_C2 alpha ha ha1
  have hholder_t : ∀ s ∈ Icc (0:ℝ) t, ∀ y z : E3,
      |F (s,y)-F (s,z)| ≤ L*‖y-z‖^alpha := by
    intro s hs y z
    exact hholder s ⟨hs.1, le_trans hs.2 htT.le⟩ y z
  obtain ⟨hfC2, _⟩ := hC F L t hL ht0 hholder_t
  have hfC2' : ContDiff ℝ 2 (f : E3 → ℝ) := by
    rw [hfun]
    simpa [u] using hfC2
  let Δ : ℝ := ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)
  have hheat : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ z : E3, euclideanHeatKernel 3 h z * f (x-z)) - f x))
      (nhdsWithin 0 (Ioi 0)) (nhds Δ) := by
    have hh := heat_generator_at_C2_initial_data f hfC2' x
    simpa [Δ, hfun] using hh
  have htail := duhamel_terminal_quotient F t x
  let H : ℝ → ℝ := fun h => h⁻¹ *
    ((∫ z : E3, euclideanHeatKernel 3 h z * f (x-z)) - f x)
  let R : ℝ → ℝ := fun h => h⁻¹ *
    ∫ s in t..t+h, ∫ y : E3,
      euclideanHeatKernel 3 (t+h-s) y * F (s,x-y)
  let Q : ℝ → ℝ := fun h => h⁻¹ * (u (t+h) x-u t x)
  have hsum : Tendsto (fun h => H h + R h) (nhdsWithin 0 (Ioi 0))
      (nhds (Δ + F (t,x))) := by
    have hheat' : Tendsto H (nhdsWithin 0 (Ioi 0)) (nhds Δ) := by
      simpa [H] using hheat
    have htail' : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds (F (t,x))) := by
      simpa [R] using htail
    exact hheat'.add htail'
  have hdecomp (h : ℝ) (hh : 0 < h) (hupper : h ≤ T-t) :
      u (t+h) x =
        (∫ z : E3, euclideanHeatKernel 3 h z * f (x-z)) +
          ∫ s in t..t+h, ∫ y : E3,
            euclideanHeatKernel 3 (t+h-s) y * F (s,x-y) := by
    have htime : t+h ≤ T := by linarith
    have hpos : 0 ≤ t+h := by linarith
    have hrestart := duhamel_restart_identity F t h ht0.le hh x
    have hconv :
        (∫ z : E3, euclideanHeatKernel 3 h z *
          ∫ r in (0:ℝ)..t, ∫ y : E3,
            euclideanHeatKernel 3 (t-r) y * F (r,x-z-y)) =
        ∫ z : E3, euclideanHeatKernel 3 h z * f (x-z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1
      calc
        (∫ r in (0:ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-r) y * F (r,x-z-y)) = V (t,x-z) := by
            symm
            exact hVformula t (x-z) ht0.le htT.le
        _ = f (x-z) := (hfeval (x-z)).symm
    calc
      u (t+h) x = V (t+h,x) := hident (t+h) hpos htime x
      _ = ∫ s in (0:ℝ)..t+h, ∫ y : E3,
          euclideanHeatKernel 3 (t+h-s) y * F (s,x-y) := hVformula (t+h) x hpos htime
      _ = (∫ z : E3, euclideanHeatKernel 3 h z *
            ∫ r in (0:ℝ)..t, ∫ y : E3,
              euclideanHeatKernel 3 (t-r) y * F (r,x-z-y)) +
          ∫ s in t..t+h, ∫ y : E3,
            euclideanHeatKernel 3 (t+h-s) y * F (s,x-y) := hrestart
      _ = _ := by rw [hconv]
  have hQeq (h : ℝ) (hh : 0 < h) (hupper : h ≤ T-t) : Q h = H h + R h := by
    have hbase : f x = u t x := by rw [hfun]
    dsimp [Q, H, R]
    rw [hdecomp h hh hupper, ← hbase]
    ring
  have hlocal : ∀ᶠ h : ℝ in nhdsWithin 0 (Ioi 0), h < T-t := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (sub_pos.mpr htT))
  have hQeq' : Q =ᶠ[nhdsWithin 0 (Ioi 0)] fun h => H h + R h := by
    filter_upwards [hlocal, self_mem_nhdsWithin] with h hsmall hpos
    exact hQeq h hpos (le_of_lt hsmall)
  have hQtend : Tendsto Q (nhdsWithin 0 (Ioi 0)) (nhds (Δ + F (t,x))) :=
    Tendsto.congr' hQeq'.symm hsum
  have hshift : Tendsto (fun s : ℝ => s-t) (nhdsWithin t (Ioi t))
      (nhdsWithin 0 (Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun s : ℝ => s-t) (nhds t) (nhds 0) := by
        have hc' : Continuous (fun s : ℝ => s-t) := continuous_id.sub continuous_const
        simpa using hc'.tendsto t
      exact hc.mono_left nhdsWithin_le_nhds
    · apply eventually_nhdsWithin_of_forall
      intro s hs
      change t < s at hs
      exact sub_pos.mpr hs
  have hslope : Tendsto (slope (fun s : ℝ => u s x) t)
      (nhdsWithin t (Ioi t)) (nhds (Δ + F (t,x))) := by
    have hcomp := hQtend.comp hshift
    have heq : (fun s : ℝ => Q (s-t)) =ᶠ[nhdsWithin t (Ioi t)]
        slope (fun s : ℝ => u s x) t := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hst : t < s := hs
      simp only [Q, slope_def_field]
      rw [show t + (s-t) = s by ring]
      field_simp
    exact Tendsto.congr' heq hcomp
  have hright : HasDerivWithinAt (fun s : ℝ => u s x) (Δ + F (t,x)) (Ioi t) t := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).2
    exact hslope
  have hfinal : HasDerivWithinAt (fun s : ℝ => u s x) (Δ + F (t,x)) (Ici t) t :=
    hright.Ici_of_Ioi
  simpa [Δ] using hfinal
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.DuhamelRightTimeDerivative
