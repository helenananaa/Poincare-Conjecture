import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideDuhamelHessianThree
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TimeDerivativeDominator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.RecursiveHessianFormula
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatGradientFDeriv
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatHessianContinuous
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
theorem duhamel_hessian_terminal_tail (alpha : ℝ) (ha : 0<alpha) (ha1 : alpha<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L T eps : ℝ), 0≤L → 0≤eps → eps≤T →
      (∀ s∈Icc (0:ℝ) T, ∀ x y : E3, |F (s,x)-F (s,y)|≤L*‖x-y‖^alpha) →
      ∀ (x : E3) (i j : Fin 3),
        IntervalIntegrable (fun s => ∫ y : E3,
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)) volume (T-eps) T ∧
        |∫ s in (T-eps)..T, ∫ y : E3,
          fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1)*F (s,x-y)| ≤ C*L*eps^(alpha/2) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hC, hcontrol⟩ :=
    euclideanHeatKernel_three_duhamel_hessian_control alpha ha ha1
  refine ⟨C, hC, ?_⟩
  intro F L T eps hL heps hepsT hHolder x i j
  by_cases heps0 : eps = 0
  · subst eps
    simp [ha.ne']
  · let d : ℝ := T - eps
    let q : ℝ → ℝ := fun s => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (T-s)) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) * F (s,x-y)
    let Fshift : (ℝ × E3) → ℝ := fun p => F (p.1 + d, p.2)
    let qshift : ℝ → ℝ := fun r => ∫ y : E3,
      fderiv ℝ (fun z : E3 => fderiv ℝ (euclideanHeatKernel 3 (eps-r)) z
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single j 1) *
          Fshift (r,x-y)
    have hFshift : Continuous Fshift := by
      dsimp [Fshift]
      exact F.continuous.comp
        ((continuous_fst.add (continuous_const : Continuous (fun _ : ℝ × E3 => d))).prodMk
          continuous_snd)
    have hFshift_bound : ∀ s ∈ Icc (0 : ℝ) eps, ∀ z : E3,
        |Fshift (s,z)| ≤ ‖F‖ := by
      intro s hs z
      dsimp [Fshift]
      simpa [Real.norm_eq_abs] using F.norm_coe_le_norm (s + d, z)
    have hFshift_holder : ∀ s ∈ Icc (0 : ℝ) eps, ∀ u v : E3,
        |Fshift (s,u) - Fshift (s,v)| ≤ L * ‖u-v‖^alpha := by
      intro s hs u v
      have hsd0 : 0 ≤ s + d := by
        dsimp [d]
        linarith [hs.1, hepsT]
      have hsdT : s + d ≤ T := by
        dsimp [d]
        linarith [hs.2]
      simpa [Fshift] using hHolder (s + d) ⟨hsd0, hsdT⟩ u v
    obtain ⟨hIntShift, hTailShift⟩ :=
      hcontrol Fshift hFshift ‖F‖ L eps (norm_nonneg F) hL heps
        hFshift_bound hFshift_holder i j x
    have hIntShift' : IntervalIntegrable qshift volume 0 eps := by
      simpa [qshift] using hIntShift
    have hTailShift' : |∫ r in (0 : ℝ)..eps, qshift r| ≤
        C * L * eps^(alpha/2) := by
      simpa [qshift] using hTailShift
    have hqcomp : (fun s => qshift (s + -d)) = q := by
      funext s
      dsimp [qshift, q, Fshift, d]
      apply integral_congr_ae
      filter_upwards [] with y
      have htime : eps - (s + -(T - eps)) = T - s := by ring
      have hsource : (s + -(T - eps)) + (T - eps) = s := by ring
      rw [htime, hsource]
    have hIntComp := hIntShift'.comp_add_right (-d)
    rw [hqcomp] at hIntComp
    have hInt : IntervalIntegrable q volume d T := by
      convert hIntComp using 1 <;> dsimp [d] <;> ring
    have hqadd : (fun r => q (r + d)) = qshift := by
      funext r
      dsimp [q, qshift, Fshift, d]
      apply integral_congr_ae
      filter_upwards [] with y
      have htime : T - (r + (T - eps)) = eps - r := by ring
      rw [htime]
    have hchange : (∫ s in d..T, q s) = ∫ r in (0 : ℝ)..eps, qshift r := by
      calc
        (∫ s in d..T, q s) = ∫ r in (0 : ℝ)..eps, q (r + d) := by
          have h := intervalIntegral.integral_comp_add_right
            (f := q) (a := (0 : ℝ)) (b := eps) d
          symm
          convert h using 1 <;> dsimp [d] <;> ring
        _ = ∫ r in (0 : ℝ)..eps, qshift r := by
          exact congrArg (fun f => ∫ r in (0 : ℝ)..eps, f r) hqadd
    refine ⟨?_, ?_⟩
    · change IntervalIntegrable q volume d T
      exact hInt
    · change |∫ s in d..T, q s| ≤ C * L * eps^(alpha/2)
      rw [hchange]
      exact hTailShift'
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
