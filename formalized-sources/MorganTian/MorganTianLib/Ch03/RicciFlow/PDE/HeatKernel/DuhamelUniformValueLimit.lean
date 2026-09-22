import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelBoundedForcing
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.DuhamelHessianTerminalTail
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual truncated Duhamel values converge uniformly in space to the full integral. -/
theorem duhamel_uniform_value_limit (F : (ℝ × E3) →ᵇ ℝ) (T : ℝ) (hT : 0<T) :
    TendstoUniformly (fun n : ℕ => fun x : E3 =>
      ∫ s in (0:ℝ)..(T-T/((n:ℝ)+2)), ∫ y : E3, euclideanHeatKernel 3 (T-s) (x-y)*F (s,y))
      (fun x : E3 => ∫ s in (0:ℝ)..T, ∫ y : E3, euclideanHeatKernel 3 (T-s) (x-y)*F (s,y)) atTop :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (T * ‖F‖ / ε)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro x
  let δ : ℝ := T / ((n : ℝ) + 2)
  let a : ℝ := T - δ
  let q : ℝ → ℝ := fun s => ∫ y : E3,
    euclideanHeatKernel 3 (T-s) (x-y) * F (s,y)
  let G : (ℝ × E3) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => F (p.1 + a, p.2))
      (F.continuous.comp
        ((continuous_fst.add (continuous_const : Continuous (fun _ : ℝ × E3 => a))).prodMk
          continuous_snd))
      ‖F‖ (by
        intro p
        exact F.norm_coe_le_norm (p.1 + a, p.2))
  have hTpos : 0 < T := hT
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδleT : δ ≤ T := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
    nlinarith [hT]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have haT : a ≤ T := by
    dsimp [a]
    linarith [le_of_lt hδpos]
  have hGnorm : ‖G‖ ≤ ‖F‖ := by
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (F.continuous.comp
        ((continuous_fst.add (continuous_const : Continuous (fun _ : ℝ × E3 => a))).prodMk
          continuous_snd)) (norm_nonneg F) (by
        intro p
        exact F.norm_coe_le_norm (p.1 + a, p.2))
  have hreflect (H : (ℝ × E3) →ᵇ ℝ) (τ r : ℝ) :
      (∫ y : E3, euclideanHeatKernel 3 (τ-r) (x-y) * H (r,y)) =
        ∫ y : E3, euclideanHeatKernel 3 (τ-r) y * H (r,x-y) := by
    have hmap :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding
        (fun z : E3 => euclideanHeatKernel 3 (τ-r) z * H (r,x-z))
    simpa [sub_sub_cancel] using hmap
  have hfull := euclideanHeatKernel_three_bounded_duhamel F T
    (le_of_lt hTpos) x
  have hqfull : IntervalIntegrable q volume 0 T := by
    have heq : q = fun s => ∫ y : E3,
        euclideanHeatKernel 3 (T-s) y * F (s,x-y) := by
      funext s
      exact hreflect F T s
    rw [heq]
    exact hfull.1
  let qshift : ℝ → ℝ := fun r => ∫ y : E3,
    euclideanHeatKernel 3 (δ-r) (x-y) * G (r,y)
  let qorient : ℝ → ℝ := fun r => ∫ y : E3,
    euclideanHeatKernel 3 (δ-r) y * G (r,x-y)
  have hshift := euclideanHeatKernel_three_bounded_duhamel G δ
    (le_of_lt hδpos) x
  have hqshift : IntervalIntegrable qshift volume 0 δ := by
    have heq : qshift = qorient := by
      funext r
      exact hreflect G δ r
    rw [heq]
    exact hshift.1
  have hqtail : IntervalIntegrable q volume a T := by
    have hcomp := hqshift.comp_add_right (-a)
    have heq : (fun s => qshift (s + -a)) = q := by
      funext s
      dsimp [qshift, q, G, a]
      apply integral_congr_ae
      filter_upwards [] with y
      have htime : δ - (s + - (T - δ)) = T - s := by ring
      have hsource : s + -(T - δ) + (T - δ) = s := by ring
      rw [htime, hsource]
    rw [heq] at hcomp
    convert hcomp using 1 <;> dsimp [a, δ] <;> ring
  have hqtrunc : IntervalIntegrable q volume 0 a := by
    apply hqfull.mono_set
    rw [uIcc_of_le ha0, uIcc_of_le (le_of_lt hTpos)]
    exact Icc_subset_Icc le_rfl haT
  have hqchange : (∫ s in a..T, q s) = ∫ r in (0 : ℝ)..δ, qshift r := by
    calc
      (∫ s in a..T, q s) = ∫ r in (0 : ℝ)..δ, q (r + a) := by
        have h := intervalIntegral.integral_comp_add_right
          (f := q) (a := (0 : ℝ)) (b := δ) a
        symm
        convert h using 1 <;> dsimp [a] <;> ring
      _ = ∫ r in (0 : ℝ)..δ, qshift r := by
        apply intervalIntegral.integral_congr
        intro r hr
        dsimp [qshift, q, G, a]
        apply integral_congr_ae
        filter_upwards [] with y
        have htime : T - (r + (T - δ)) = δ - r := by ring
        rw [htime]
  have hshift_eq : (∫ r in (0 : ℝ)..δ, qshift r) =
      ∫ r in (0 : ℝ)..δ, qorient r := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact hreflect G δ r
  have htail : |∫ s in a..T, q s| ≤ δ * ‖F‖ := by
    rw [hqchange, hshift_eq]
    calc
      |∫ r in (0 : ℝ)..δ, qorient r| ≤ δ * ‖G‖ := by
        simpa [qorient] using hshift.2
      _ ≤ δ * ‖F‖ := mul_le_mul_of_nonneg_left hGnorm (le_of_lt hδpos)
  have hsmall : δ * ‖F‖ < ε := by
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hN' : T * ‖F‖ / ε < (N : ℝ) := hN
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hden' : T * ‖F‖ / ε < (n : ℝ) + 2 := by linarith
    dsimp [δ]
    rw [show T / ((n : ℝ) + 2) * ‖F‖ =
      (T * ‖F‖) / ((n : ℝ) + 2) by ring]
    apply (div_lt_iff₀ hden).2
    have hmul : T * ‖F‖ < ((n : ℝ) + 2) * ε :=
      (div_lt_iff₀ hε).mp hden'
    nlinarith
  have hdiff := intervalIntegral.integral_interval_sub_left hqfull hqtrunc
  change |(∫ s in (0 : ℝ)..T, q s) - ∫ s in (0 : ℝ)..a, q s| < ε
  rw [hdiff]
  exact htail.trans_lt hsmall
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
