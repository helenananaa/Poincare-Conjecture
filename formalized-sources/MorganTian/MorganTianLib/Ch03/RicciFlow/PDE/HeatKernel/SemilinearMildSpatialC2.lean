import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.MildSourceUniformHolder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.TruncatedDuhamelHessian
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.WideBoundedHessianIdentification
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.BoundedNemytskiiOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearMildSpatialRegularization
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.SemilinearLocalMildIVP
import Mathlib
open Set MeasureTheory Filter Function
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
noncomputable section
namespace MorganTianLib.ParabolicPDE
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Actual positive-time spatial C2 regularity of the already constructed mild semilinear solution. -/
theorem semilinear_mild_spatial_C2 (f : E3 →ᵇ ℝ) (N : ℝ → ℝ) (L T : ℝ) (hL : 0≤L) (hT : 0≤T)
    (hN : ∀ a b : ℝ, |N a-N b|≤L*|a-b|) (u : (ℝ × E3) →ᵇ ℝ)
    (hu : ∀ t : ℝ, 0<t → t≤T → ∀ x : E3,
      u (t,x)=(∫ y : E3, euclideanHeatKernel 3 t y*f (x-y))+
        ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) y*N (u (s,x-y))) :
    ∀ t : ℝ, 0<t → t≤T → ContDiff ℝ 2 (fun x : E3 => u (t,x)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro t ht htT
  obtain ⟨A, hA, hAnorm, hAlip⟩ := bounded_nemytskii_operator N L hL hN
  let F : (ℝ × E3) →ᵇ ℝ := A u
  have hF_apply (s : ℝ) (x : E3) : F (s,x) = N (u (s,x)) := by
    dsimp [F]
    exact hA u (s,x)
  let δ : ℝ := t / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  have hδlet : δ ≤ t := by
    dsimp [δ]
    linarith
  have hδleT : δ ≤ T := by
    dsimp [δ]
    linarith
  obtain ⟨C, hC, hHolder⟩ :=
    mild_source_uniform_holder_away_zero f N L T hL hT hN u hu
      δ (1 / 2 : ℝ) hδpos hδleT (by norm_num) (by norm_num)
  let G : (ℝ × E3) →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p : ℝ × E3 => F (p.1 + δ, p.2))
      (F.continuous.comp
        ((continuous_fst.add (continuous_const : Continuous (fun _ : ℝ × E3 => δ))).prodMk
          continuous_snd))
      ‖F‖ (by
        intro p
        exact F.norm_coe_le_norm (p.1 + δ, p.2))
  have hG_apply (s : ℝ) (x : E3) : G (s,x) = F (s + δ,x) := by
    rfl
  have hGholder : ∀ s ∈ Icc (0 : ℝ) δ, ∀ x y : E3,
      |G (s,x)-G (s,y)| ≤ C*‖x-y‖^(1 / 2 : ℝ) := by
    intro s hs x y
    have hsT : s + δ ∈ Icc δ T := by
      constructor
      · linarith [hs.1, hδpos.le]
      · have hst : s + δ ≤ δ + δ := by
          simpa [add_comm] using (add_le_add_right hs.2 δ)
        calc
          s + δ ≤ δ + δ := hst
          _ = t := by dsimp [δ]; ring
          _ ≤ T := htT
    calc
      |G (s,x)-G (s,y)| = |F (s + δ,x)-F (s + δ,y)| := by
        rw [hG_apply, hG_apply]
      _ = |N (u (s + δ,x))-N (u (s + δ,y))| := by
        rw [hF_apply, hF_apply]
      _ ≤ C*‖x-y‖^(1 / 2 : ℝ) := hHolder (s + δ) hsT x y
  obtain ⟨Cfull, hCfull, hfull⟩ :=
    full_duhamel_spatial_C2 (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hlateC2 : ContDiff ℝ 2 (fun x : E3 =>
      ∫ r in (0:ℝ)..δ, ∫ y : E3,
        euclideanHeatKernel 3 (δ-r) (x-y)*G (r,y)) := by
    simpa using (hfull G C δ hC hδpos hGholder).1
  have hearlyC2 : ContDiff ℝ 2 (fun x : E3 =>
      ∫ s in (0:ℝ)..δ, ∫ y : E3,
        euclideanHeatKernel 3 (t-s) (x-y)*F (s,y)) := by
    have htdelta : t - δ = δ := by
      dsimp [δ]
      ring
    simpa [htdelta] using (truncated_duhamel_hessian F t δ hδpos hδlet).1
  have hfreeC2 : ContDiff ℝ 2 (fun x : E3 =>
      ∫ y : E3, euclideanHeatKernel 3 t (x-y)*f y) := by
    simpa using (euclideanHeatKernel_bounded_hessian_identification f ht).1
  have hreflect (H : (ℝ × E3) →ᵇ ℝ) (τ r : ℝ) (x : E3) :
      (∫ y : E3, euclideanHeatKernel 3 (τ-r) y * H (r,x-y)) =
        ∫ y : E3, euclideanHeatKernel 3 (τ-r) (x-y) * H (r,y) := by
    let p : E3 → ℝ := fun y => euclideanHeatKernel 3 (τ-r) y * H (r,x-y)
    have hmap :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding p
    calc
      (∫ y : E3, euclideanHeatKernel 3 (τ-r) y * H (r,x-y)) = ∫ y : E3, p y := by
        rfl
      _ = ∫ y : E3, p (x-y) := hmap.symm
      _ = ∫ y : E3, euclideanHeatKernel 3 (τ-r) (x-y) * H (r,y) := by
        congr 1
        funext y
        dsimp [p]
        rw [sub_sub_cancel]
  have hfree_eq (x : E3) :
      (∫ y : E3, euclideanHeatKernel 3 t y * f (x-y)) =
        ∫ y : E3, euclideanHeatKernel 3 t (x-y) * f y := by
    let p : E3 → ℝ := fun y => euclideanHeatKernel 3 t y * f (x-y)
    have hmap :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding p
    calc
      (∫ y : E3, euclideanHeatKernel 3 t y * f (x-y)) = ∫ y : E3, p y := by
        rfl
      _ = ∫ y : E3, p (x-y) := hmap.symm
      _ = ∫ y : E3, euclideanHeatKernel 3 t (x-y) * f y := by
        congr 1
        funext y
        dsimp [p]
        rw [sub_sub_cancel]
  have hearly_eq (x : E3) :
      (∫ s in (0:ℝ)..δ, ∫ y : E3,
        euclideanHeatKernel 3 (t-s) y * F (s,x-y)) =
        ∫ s in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) (x-y) * F (s,y) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hreflect F t s x
  have hlate_eq (x : E3) :
      (∫ s in δ..t, ∫ y : E3,
        euclideanHeatKernel 3 (t-s) y * F (s,x-y)) =
        ∫ r in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (δ-r) (x-y) * G (r,y) := by
    let q : ℝ → ℝ := fun s => ∫ y : E3,
      euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)
    calc
      (∫ s in δ..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * F (s,x-y)) =
          ∫ s in δ..t, q s := by
            apply intervalIntegral.integral_congr
            intro s hs
            exact hreflect F t s x
      _ = ∫ r in (0:ℝ)..δ, q (r + δ) := by
        have h := intervalIntegral.integral_comp_add_right
          (f := q) (a := (0 : ℝ)) (b := δ) δ
        symm
        convert h using 1 <;> dsimp [δ] <;> ring
      _ = ∫ r in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (δ-r) (x-y) * G (r,y) := by
        apply intervalIntegral.integral_congr
        intro r hr
        dsimp [q]
        apply integral_congr_ae
        filter_upwards [] with y
        rw [show t - (r + δ) = δ - r by dsimp [δ]; ring,
          ← hG_apply r y]
  have hsplit (x : E3) :
      (∫ s in (0:ℝ)..t, ∫ y : E3,
        euclideanHeatKernel 3 (t-s) y * F (s,x-y)) =
        (∫ s in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * F (s,x-y)) +
          ∫ s in δ..t, ∫ y : E3,
            euclideanHeatKernel 3 (t-s) y * F (s,x-y) := by
    let q : ℝ → ℝ := fun s => ∫ y : E3,
      euclideanHeatKernel 3 (t-s) y * F (s,x-y)
    have hfullInt := euclideanHeatKernel_three_bounded_duhamel F t
      (le_of_lt ht) x
    have hmem : δ ∈ uIcc (0 : ℝ) t := by
      rw [uIcc_of_le (le_of_lt ht)]
      exact ⟨by dsimp [δ]; linarith, hδlet⟩
    have hparts := (IntervalIntegrable.trans_iff hmem).mp hfullInt.1
    have hleft : IntervalIntegrable q volume 0 δ := by
      simpa [q] using hparts.1
    have hright : IntervalIntegrable q volume δ t := by
      simpa [q] using hparts.2
    calc
      (∫ s in (0:ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * F (s,x-y)) =
          ∫ s in (0:ℝ)..t, q s := by rfl
      _ = (∫ s in (0:ℝ)..δ, q s) + ∫ s in δ..t, q s := by
        symm
        exact intervalIntegral.integral_add_adjacent_intervals hleft hright
      _ = (∫ s in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * F (s,x-y)) +
          ∫ s in δ..t, ∫ y : E3,
            euclideanHeatKernel 3 (t-s) y * F (s,x-y) := by
        rfl
  have hsource (x : E3) :
      (∫ s in (0:ℝ)..t, ∫ y : E3,
        euclideanHeatKernel 3 (t-s) y * N (u (s,x-y))) =
        ∫ s in (0:ℝ)..t, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) y * F (s,x-y) := by
    apply intervalIntegral.integral_congr
    intro s hs
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hF_apply]
  have hsum : ContDiff ℝ 2 (fun x : E3 =>
      (∫ y : E3, euclideanHeatKernel 3 t (x-y) * f y) +
        (∫ s in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)) +
        ∫ r in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (δ-r) (x-y) * G (r,y)) := by
    exact (hfreeC2.add hearlyC2).add hlateC2
  have hfun : (fun x : E3 => u (t,x)) = (fun x : E3 =>
      (∫ y : E3, euclideanHeatKernel 3 t (x-y) * f y) +
        (∫ s in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)) +
        ∫ r in (0:ℝ)..δ, ∫ y : E3,
          euclideanHeatKernel 3 (δ-r) (x-y) * G (r,y)) := by
    funext x
    have hu' := hu t ht htT x
    rw [hsource x, hsplit x, hfree_eq x, hearly_eq x, hlate_eq x] at hu'
    simpa [add_assoc] using hu'
  rw [hfun]
  exact hsum
/- SWARM_PROOF_END -/
end MorganTianLib.ParabolicPDE
