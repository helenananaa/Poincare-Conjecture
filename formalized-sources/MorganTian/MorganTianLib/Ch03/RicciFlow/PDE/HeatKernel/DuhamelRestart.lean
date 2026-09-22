import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FixedDomainDuhamel
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedDuhamelOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedHeatSemigroup
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearLocalMildIVP
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual Duhamel integral obeys the heat-semigroup restart identity. -/
theorem duhamel_restart_identity (F : (ℝ × E3) →ᵇ ℝ) (S t : ℝ)
    (hS : 0≤S) (ht : 0<t) (x : E3) :
    (∫ s in (0:ℝ)..(S+t), ∫ y : E3, euclideanHeatKernel 3 (S+t-s) y * F (s,x-y)) =
      (∫ z : E3, euclideanHeatKernel 3 t z *
        (∫ s in (0:ℝ)..S, ∫ y : E3, euclideanHeatKernel 3 (S-s) y * F (s,x-z-y))) +
      ∫ s in S..(S+t), ∫ y : E3, euclideanHeatKernel 3 (S+t-s) y * F (s,x-y) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hS0 : S = 0
  · subst S
    simp
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    let g : ℝ → ℝ := fun s =>
      ∫ y : E3, euclideanHeatKernel 3 (S + t - s) y * F (s, x - y)
    let H : (ℝ × E3) × E3 → ℝ := fun p =>
      euclideanHeatKernel 3 t p.1.2 *
        euclideanHeatKernel 3 (S - p.1.1) p.2 *
        F (p.1.1, x - p.1.2 - p.2)
    let M : (ℝ × E3) × E3 → ℝ := fun p =>
      euclideanHeatKernel 3 t p.1.2 *
        euclideanHeatKernel 3 (S - p.1.1) p.2 * ‖F‖
    let μS : Measure ℝ := volume.restrict (Ioc (0 : ℝ) S)
    have hkt : Integrable (euclideanHeatKernel 3 t) (volume : Measure E3) :=
      (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.1
    have hktmass : (∫ z : E3, euclideanHeatKernel 3 t z) = 1 :=
      (euclideanHeatKernel_mass_semigroup 3).1 t ht |>.2
    have htime : Integrable (fun _ : ℝ => ‖F‖) μS := by
      exact (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) S)
        (C := ‖F‖) (by simp)).integrable
    have hgoodS : ∀ᵐ s ∂μS, s ∈ Ioc (0 : ℝ) S ∧ s ≠ S := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne S)] with s hs hne
      exact ⟨hs, hne⟩
    have hgood : ∀ᵐ p : ℝ × E3 ∂(μS.prod (volume : Measure E3)),
        p.1 ∈ Ioc (0 : ℝ) S ∧ p.1 ≠ S := by
      refine (Measure.ae_prod_iff_ae_ae (μ := μS) (ν := (volume : Measure E3))
        (by measurability)).2 ?_
      filter_upwards [hgoodS] with s hs
      exact Eventually.of_forall (fun z => hs)
    have hMmeas : Measurable M := by
      dsimp [M]
      unfold euclideanHeatKernel gaussianHeatKernel
      measurability
    have hN : Integrable
        (fun p : ℝ × E3 => euclideanHeatKernel 3 t p.2 * ‖F‖)
        (μS.prod (volume : Measure E3)) := by
      have h := htime.mul_prod hkt
      simpa [mul_comm] using h
    have hM : Integrable M
        ((μS.prod (volume : Measure E3)).prod (volume : Measure E3)) := by
      apply (integrable_prod_iff hMmeas.aestronglyMeasurable).2
      refine ⟨?_, ?_⟩
      · filter_upwards [hgood] with p hp
        rcases p with ⟨s, z⟩
        have hka : Integrable (euclideanHeatKernel 3 (S - s))
            (volume : Measure E3) :=
          (euclideanHeatKernel_mass_semigroup 3).1 (S - s)
            (sub_pos.mpr (lt_of_le_of_ne hp.1.2 hp.2)) |>.1
        have h := hka.const_mul
          (euclideanHeatKernel 3 t z * ‖F‖)
        simpa [M, mul_assoc, mul_left_comm, mul_comm] using h
      · have hnorm :
            (fun p : ℝ × E3 =>
              ∫ w : E3, ‖M (p, w)‖) =ᵐ[μS.prod (volume : Measure E3)]
            (fun p : ℝ × E3 => euclideanHeatKernel 3 t p.2 * ‖F‖) := by
          filter_upwards [hgood] with p hp
          rcases p with ⟨s, z⟩
          have hts : 0 < S - s := sub_pos.mpr (lt_of_le_of_ne hp.1.2 hp.2)
          have hka : Integrable (euclideanHeatKernel 3 (S - s))
              (volume : Measure E3) :=
            (euclideanHeatKernel_mass_semigroup 3).1 (S - s) hts |>.1
          have hkamass :
              (∫ w : E3, euclideanHeatKernel 3 (S - s) w) = 1 :=
            (euclideanHeatKernel_mass_semigroup 3).1 (S - s) hts |>.2
          have hktpos (z : E3) : 0 ≤ euclideanHeatKernel 3 t z :=
            (euclideanHeatKernel_pos 3 ht z).le
          have hkapos (w : E3) : 0 ≤ euclideanHeatKernel 3 (S - s) w :=
            (euclideanHeatKernel_pos 3 hts w).le
          calc
            (∫ w : E3, ‖M ((s, z), w)‖) =
                ∫ w : E3,
                  euclideanHeatKernel 3 t z *
                    euclideanHeatKernel 3 (S - s) w * ‖F‖ := by
              apply integral_congr_ae
              filter_upwards [] with w
              dsimp [M]
              rw [abs_mul, abs_mul,
                abs_of_nonneg (hktpos z), abs_of_nonneg (hkapos w),
                abs_of_nonneg (norm_nonneg F)]
            _ = (∫ w : E3,
                euclideanHeatKernel 3 t z *
                  euclideanHeatKernel 3 (S - s) w) * ‖F‖ := by
              rw [integral_mul_const]
            _ = euclideanHeatKernel 3 t z * ‖F‖ := by
              rw [integral_const_mul, hkamass, mul_one]
        exact hN.congr hnorm.symm
    have hHmeas : Measurable H := by
      dsimp [H]
      unfold euclideanHeatKernel gaussianHeatKernel
      measurability
    have hH : Integrable H
        ((μS.prod (volume : Measure E3)).prod (volume : Measure E3)) := by
      have hgood' : ∀ᵐ p : (ℝ × E3) × E3 ∂
          ((μS.prod (volume : Measure E3)).prod (volume : Measure E3)),
          p.1.1 ∈ Ioc (0 : ℝ) S ∧ p.1.1 ≠ S := by
        refine (Measure.ae_prod_iff_ae_ae
          (μ := μS.prod (volume : Measure E3)) (ν := (volume : Measure E3))
          (by measurability)).2 ?_
        filter_upwards [hgood] with p hp
        exact Eventually.of_forall (fun w => hp)
      apply hM.mono' hHmeas.aestronglyMeasurable
      filter_upwards [hgood'] with p hp
      rcases p with ⟨⟨s, z⟩, w⟩
      have hts : 0 < S - s := sub_pos.mpr (lt_of_le_of_ne hp.1.2 hp.2)
      have hkp (z : E3) : 0 ≤ euclideanHeatKernel 3 t z :=
        (euclideanHeatKernel_pos 3 ht z).le
      have hka (w : E3) : 0 ≤ euclideanHeatKernel 3 (S - s) w :=
        (euclideanHeatKernel_pos 3 hts w).le
      dsimp [H, M]
      rw [abs_mul, abs_mul, abs_of_nonneg (hkp z), abs_of_nonneg (hka w)]
      exact mul_le_mul_of_nonneg_left
        (F.norm_coe_le_norm (s, x - z - w))
        (mul_nonneg (hkp z) (hka w))
    have hslice (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) S) (hsne : s ≠ S) :
        (∫ y : E3, euclideanHeatKernel 3 (S + t - s) y * F (s, x - y)) =
          ∫ z : E3, ∫ w : E3, H ((s, z), w) := by
      have hts : 0 < S - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsne)
      have hka : Integrable (euclideanHeatKernel 3 (S - s))
          (volume : Measure E3) :=
        (euclideanHeatKernel_mass_semigroup 3).1 (S - s) hts |>.1
      have hconv (y : E3) :
          (∫ z : E3, euclideanHeatKernel 3 t z *
            euclideanHeatKernel 3 (S - s) (y - z)) =
            euclideanHeatKernel 3 (t + (S - s)) y := by
        simpa [mul_comm, add_comm] using
          ((euclideanHeatKernel_mass_semigroup 3).2 (S - s) t hts ht y).2
      have hRbase : Integrable
          (fun p : E3 × E3 =>
            euclideanHeatKernel 3 t p.2 *
              euclideanHeatKernel 3 (S - s) (p.1 - p.2))
          ((volume : Measure E3).prod (volume : Measure E3)) := by
        simpa using
          (hkt.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hka)
      have hR : Integrable
          (fun p : E3 × E3 =>
            euclideanHeatKernel 3 t p.2 *
              euclideanHeatKernel 3 (S - s) (p.1 - p.2) * F (s, x - p.1))
          ((volume : Measure E3).prod (volume : Measure E3)) := by
        have hmeas : AEStronglyMeasurable
            (fun p : E3 × E3 => F (s, x - p.1))
            ((volume : Measure E3).prod (volume : Measure E3)) := by
          fun_prop
        simpa [mul_assoc] using hRbase.mul_bdd hmeas
          (Eventually.of_forall (fun p => F.norm_coe_le_norm (s, x - p.1)))
      have hQbase : Integrable
          (fun p : E3 × E3 =>
            euclideanHeatKernel 3 t p.1 *
              euclideanHeatKernel 3 (S - s) p.2)
          ((volume : Measure E3).prod (volume : Measure E3)) := by
        exact hkt.mul_prod hka
      have hQ : Integrable
          (fun p : E3 × E3 =>
            euclideanHeatKernel 3 t p.1 *
              euclideanHeatKernel 3 (S - s) p.2 * F (s, x - p.1 - p.2))
          ((volume : Measure E3).prod (volume : Measure E3)) := by
        have hmeas : AEStronglyMeasurable
            (fun p : E3 × E3 => F (s, x - p.1 - p.2))
            ((volume : Measure E3).prod (volume : Measure E3)) := by
          fun_prop
        simpa [mul_assoc] using hQbase.mul_bdd hmeas
          (Eventually.of_forall (fun p =>
            F.norm_coe_le_norm (s, x - p.1 - p.2)))
      calc
        (∫ y : E3, euclideanHeatKernel 3 (S + t - s) y * F (s, x - y)) =
            ∫ y : E3,
              (∫ z : E3, euclideanHeatKernel 3 t z *
                euclideanHeatKernel 3 (S - s) (y - z)) * F (s, x - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [hconv y]
          congr 1
          ring_nf
        _ = ∫ y : E3, ∫ z : E3,
            euclideanHeatKernel 3 t z *
              euclideanHeatKernel 3 (S - s) (y - z) * F (s, x - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [integral_mul_const]
        _ = ∫ z : E3, ∫ y : E3,
            euclideanHeatKernel 3 t z *
              euclideanHeatKernel 3 (S - s) (y - z) * F (s, x - y) := by
          exact integral_integral_swap hR
        _ = ∫ z : E3, ∫ w : E3,
            euclideanHeatKernel 3 t z *
              euclideanHeatKernel 3 (S - s) w * F (s, x - z - w) := by
          apply integral_congr_ae
          filter_upwards [] with z
          have hshift :=
            (measurePreserving_add_right (volume : Measure E3) (-z)).integral_comp
              (measurableEmbedding_addRight (-z))
              (fun w : E3 => euclideanHeatKernel 3 t z *
                euclideanHeatKernel 3 (S - s) w * F (s, x - z - w))
          simpa [Function.comp_def, sub_eq_add_neg, add_assoc, add_left_comm,
            add_comm] using hshift
        _ = ∫ z : E3, ∫ w : E3, H ((s, z), w) := by
          rfl
    have hEq : ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ uIoc (0 : ℝ) S →
          (∫ y : E3, euclideanHeatKernel 3 (S + t - s) y * F (s, x - y)) =
            ∫ z : E3, ∫ w : E3, H ((s, z), w) := by
      filter_upwards [volume.ae_ne S] with s hsne hs
      rw [uIoc_of_le hS] at hs
      exact hslice s hs (by exact hsne)
    have hEarly :
        (∫ s in (0 : ℝ)..S,
          ∫ y : E3, euclideanHeatKernel 3 (S + t - s) y * F (s, x - y)) =
          ∫ s in (0 : ℝ)..S, ∫ z : E3, ∫ w : E3, H ((s, z), w) := by
      exact intervalIntegral.integral_congr_ae hEq
    have hJ : Integrable
        (fun p : ℝ × E3 => ∫ w : E3, H (p, w))
        (μS.prod (volume : Measure E3)) :=
      hH.integral_prod_left
    have hswap :
        (∫ s in (0 : ℝ)..S, ∫ z : E3, ∫ w : E3, H ((s, z), w)) =
          ∫ z : E3, ∫ s in (0 : ℝ)..S, ∫ w : E3, H ((s, z), w) := by
      have h := integral_integral_swap
        (f := fun s z => ∫ w : E3, H ((s, z), w)) hJ
      simpa [μS, intervalIntegral.integral_of_le hS] using h
    have hfactor (z : E3) :
        (∫ s in (0 : ℝ)..S, ∫ w : E3, H ((s, z), w)) =
          euclideanHeatKernel 3 t z *
            (∫ s in (0 : ℝ)..S, ∫ w : E3,
              euclideanHeatKernel 3 (S - s) w * F (s, x - z - w)) := by
      calc
        (∫ s in (0 : ℝ)..S, ∫ w : E3, H ((s, z), w)) =
            ∫ s in (0 : ℝ)..S, euclideanHeatKernel 3 t z *
              (∫ w : E3, euclideanHeatKernel 3 (S - s) w *
                F (s, x - z - w)) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [] with s hs
          dsimp [H]
          rw [show (fun w : E3 =>
              euclideanHeatKernel 3 t z *
                euclideanHeatKernel 3 (S - s) w * F (s, x - z - w)) =
            (fun w : E3 => euclideanHeatKernel 3 t z *
              (euclideanHeatKernel 3 (S - s) w * F (s, x - z - w))) by
                funext w
                ring]
          rw [integral_const_mul]
        _ = euclideanHeatKernel 3 t z *
            (∫ s in (0 : ℝ)..S, ∫ w : E3,
              euclideanHeatKernel 3 (S - s) w * F (s, x - z - w)) := by
          rw [intervalIntegral.integral_const_mul]
    have hEarlyConv :
        (∫ s in (0 : ℝ)..S,
          ∫ y : E3, euclideanHeatKernel 3 (S + t - s) y * F (s, x - y)) =
          ∫ z : E3, euclideanHeatKernel 3 t z *
            (∫ s in (0 : ℝ)..S, ∫ w : E3,
              euclideanHeatKernel 3 (S - s) w * F (s, x - z - w)) := by
      rw [hEarly, hswap]
      apply integral_congr_ae
      filter_upwards [] with z
      exact hfactor z
    obtain ⟨hfullInt, _⟩ :=
      euclideanHeatKernel_three_bounded_duhamel F (S + t)
        (by linarith) x
    have hmem : S ∈ uIcc (0 : ℝ) (S + t) := by
      rw [uIcc_of_le (by linarith)]
      exact ⟨hS, by linarith⟩
    have hparts := (IntervalIntegrable.trans_iff hmem).mp hfullInt
    have hleft : IntervalIntegrable g volume 0 S := by
      simpa [g] using hparts.1
    have hright : IntervalIntegrable g volume S (S + t) := by
      simpa [g] using hparts.2
    calc
      (∫ s in (0 : ℝ)..(S+t),
          ∫ y : E3, euclideanHeatKernel 3 (S+t-s) y * F (s,x-y)) =
          (∫ s in (0 : ℝ)..S, g s) +
            ∫ s in S..(S+t), g s := by
              symm
              exact intervalIntegral.integral_add_adjacent_intervals hleft hright
      _ = (∫ z : E3, euclideanHeatKernel 3 t z *
            (∫ s in (0 : ℝ)..S, ∫ w : E3,
              euclideanHeatKernel 3 (S-s) w * F (s,x-z-w))) +
            ∫ s in S..(S+t), ∫ y : E3,
              euclideanHeatKernel 3 (S+t-s) y * F (s,x-y) := by
              rw [hEarlyConv]
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
