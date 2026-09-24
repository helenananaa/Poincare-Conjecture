import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF
import PoincareConjecture.ParallelImplementation.SixComponentDuhamelClassical
import PoincareConjecture.ParallelImplementation.SixComponentDuhamelHessian
import PoincareConjecture.ParallelImplementation.VectorDuhamelBoundedLinear
import PoincareConjecture.ParallelImplementation.JointGradientContinuity
import PoincareConjecture.ParallelImplementation.GradientSupInterpolation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.EuclideanSemigroup
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullVectorDuhamelJet
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Lift the actual vector Duhamel solution into the full parabolic graph with a uniform norm bound. -/
theorem full_vector_duhamel_jet (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T H : ℝ) (hT : 0 < T), T ≤ 1 → 0 ≤ H →
      ∀ F : (ℝ × E3) →ᵇ E6,
      (∀ p q : Slab T, ‖F ((p.1:ℝ),p.2)-F ((q.1:ℝ),q.2)‖ ≤ H*parabolicRho p q ^ alpha) →
      let u : ℝ → E3 → E6 := fun t x => WithLp.toLp 2 (fun k : Fin 6 =>
        ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y)*(F (s,y) k))
      ∃ z : FullJet T, z ∈ fullParabolicJetSet T alpha hT.le ∧
        (∀ p : Slab T, z.1.1.1.1 p = u (p.1:ℝ) p.2) ∧
        (∀ p : Slab T, z.1.2 p =
          (∑ i : Fin 3, fderiv ℝ (fderiv ℝ (u (p.1:ℝ))) p.2
            (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))+F ((p.1:ℝ),p.2)) ∧
        ‖z‖ ≤ C*(‖F‖+H) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₀, hC₀pos, hSchauderAll⟩ :=
    PoincareConjecture.ParallelImplementation.SixComponentDuhamelHessian.six_component_duhamel_hessian_schauder
      alpha ha ha1
  let C : ℝ := 20 + 10*C₀
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro T H hT hT1 hH F hF
  dsimp only
  let u : ℝ → E3 → E6 := fun t x => WithLp.toLp 2 (fun k : Fin 6 =>
    ∫ s in (0:ℝ)..t, ∫ y : E3,
      euclideanHeatKernel 3 (t-s) (x-y) * (F (s,y) k))
  let ei : Fin 3 → E3 := fun i => EuclideanSpace.single i 1
  obtain ⟨D, hDnorm, hDvalue⟩ :=
    PoincareConjecture.ParallelImplementation.VectorDuhamelBoundedLinear.exists_vector_duhamel_boundedLinear
      T hT.le
  let value : Slab T →ᵇ E6 := D F
  have hvaluePoint (p : Slab T) : value p = u (p.1 : ℝ) p.2 := by
    ext k
    change (D F p) k = _
    exact hDvalue F p k
  have hvalueNorm : ‖value‖ ≤ 6 * ‖F‖ := by
    calc
      ‖value‖ = ‖D F‖ := rfl
      _ ≤ ‖D‖ * ‖F‖ := ContinuousLinearMap.le_opNorm D F
      _ ≤ (6*T) * ‖F‖ := mul_le_mul_of_nonneg_right hDnorm (norm_nonneg _)
      _ ≤ 6 * ‖F‖ := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)

  have hspatial : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ x y : E3,
      ‖F (t,x)-F (t,y)‖ ≤ H*‖x-y‖^alpha := by
    intro t ht x y
    let p : Slab T := (⟨t, ht⟩, x)
    let q : Slab T := (⟨t, ht⟩, y)
    have hh := hF p q
    simpa [p, q, parabolicRho] using hh

  have hSch := hSchauderAll F H T hH hT.le hspatial
  have hclass :=
    PoincareConjecture.ParallelImplementation.SixComponentDuhamelClassical.six_component_duhamel_classical
      T alpha H hT ha ha1 hH F hspatial
  have hTnonneg : 0 ≤ T := hT.le
  have hTleone : T ≤ 1 := hT1
  have hMnonneg : 0 ≤ C₀ * H := mul_nonneg hC₀pos.le hH
  let hessRaw : Slab T → E3 →L[ℝ] E3 →L[ℝ] E6 := fun p =>
    fderiv ℝ (fderiv ℝ (u (p.1 : ℝ))) p.2
  have hessPointBound (p : Slab T) : ‖hessRaw p‖ ≤ C₀ * H := by
    have hs := hSch.2.1 (p.1 : ℝ) p.1.2 p.2
    have hpow : (p.1 : ℝ)^(alpha/2) ≤ 1 :=
      Real.rpow_le_one p.1.2.1 (p.1.2.2.trans hTleone) (by positivity)
    calc
      ‖hessRaw p‖ ≤ C₀ * H * (p.1 : ℝ)^(alpha/2) := by
        change ‖fderiv ℝ (fderiv ℝ (u (p.1:ℝ))) p.2‖ ≤ _
        exact hs
      _ ≤ C₀ * H := by nlinarith [mul_nonneg hMnonneg (sub_nonneg.mpr hpow)]

  have hessCont : Continuous hessRaw := by
    apply continuous_iff_continuousAt.mpr
    intro p
    rw [Metric.continuousAt_iff']
    intro ε hε
    let modulus : Slab T → ℝ := fun q => C₀ * H *
      (‖p.2-q.2‖^alpha + |(p.1:ℝ)-(q.1:ℝ)|^(alpha/2))
    have hspaceCont : Continuous (fun q : Slab T => ‖p.2-q.2‖^alpha) := by
      exact (Real.continuous_rpow_const ha.le).comp
        (continuous_norm.comp (continuous_const.sub continuous_snd))
    have htimeCont : Continuous (fun q : Slab T =>
        |(p.1:ℝ)-(q.1:ℝ)|^(alpha/2)) := by
      have hexp : 0 ≤ alpha/2 := by positivity
      exact (Real.continuous_rpow_const hexp).comp
        (continuous_abs.comp
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))
    have hmodCont : Continuous modulus := by
      dsimp [modulus]
      exact continuous_const.mul (hspaceCont.add htimeCont)
    have hmodZero : modulus p = 0 := by
      simp [modulus, ha.ne', (by positivity : alpha/2 ≠ 0)]
    have hmodSmall : ∀ᶠ q : Slab T in 𝓝 p, dist (modulus q) 0 < ε := by
      have htend : Filter.Tendsto modulus (𝓝 p) (𝓝 0) := by
        have ht : Filter.Tendsto modulus (𝓝 p) (𝓝 (modulus p)) := hmodCont.continuousAt
        rw [hmodZero] at ht
        exact ht
      exact (Metric.tendsto_nhds.mp htend) ε hε
    filter_upwards [hmodSmall] with q hq
    have hmodNonneg : 0 ≤ modulus q := by
      exact mul_nonneg hMnonneg (add_nonneg
        (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (abs_nonneg _) _))
    have hq' : modulus q < ε := by
      simpa [dist_eq_norm, Real.norm_of_nonneg hmodNonneg] using hq
    have hraw := hSch.2.2 (p.1:ℝ) p.1.2 (q.1:ℝ) q.1.2 p.2 q.2
    have hraw' : dist (hessRaw q) (hessRaw p) ≤ modulus q := by
      rw [dist_eq_norm, norm_sub_rev]
      change ‖hessRaw p-hessRaw q‖ ≤
        C₀*H*(‖p.2-q.2‖^alpha+|(p.1:ℝ)-(q.1:ℝ)|^(alpha/2))
      exact hraw
    exact lt_of_le_of_lt hraw' hq'

  let hess : Slab T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    BoundedContinuousFunction.ofNormedAddCommGroup hessRaw hessCont (C₀*H) hessPointBound
  have hhessPoint (p : Slab T) : hess p = hessRaw p := rfl
  have hessNorm : ‖hess‖ ≤ C₀ * H :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hessCont hMnonneg hessPointBound

  have hgradCont : Continuous (fun p : Slab T => fderiv ℝ (u (p.1:ℝ)) p.2) := by
    let f : Set.Icc (0:ℝ) T → E3 → E6 := fun t x => u (t:ℝ) x
    have hf : Continuous (fun p : Set.Icc (0:ℝ) T × E3 => f p.1 p.2) := by
      change Continuous (fun p : Slab T => u (p.1:ℝ) p.2)
      exact value.continuous.congr fun p => hvaluePoint p
    have hC2 : ∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (f t) := by
      intro t
      exact hSch.1 (t:ℝ) t.2
    have hHbound : ∀ t : Set.Icc (0:ℝ) T, ∀ x : E3,
        ‖fderiv ℝ (fderiv ℝ (f t)) x‖ ≤ C₀*H := by
      intro t x
      have hs := hSch.2.1 (t:ℝ) t.2 x
      have hpow : (t:ℝ)^(alpha/2) ≤ 1 :=
        Real.rpow_le_one t.2.1 (t.2.2.trans hTleone) (by positivity)
      calc
        ‖fderiv ℝ (fderiv ℝ (f t)) x‖ ≤ C₀*H*(t:ℝ)^(alpha/2) := by
          change ‖fderiv ℝ (fderiv ℝ (u (t:ℝ))) x‖ ≤ _
          exact hs
        _ ≤ C₀*H := by nlinarith [mul_nonneg hMnonneg (sub_nonneg.mpr hpow)]
    exact PoincareConjecture.ParallelImplementation.JointGradientContinuity.joint_gradient_continuity
      f hf hC2 (C₀*H) hMnonneg hHbound

  let gradRaw : Slab T → E3 →L[ℝ] E6 := fun p =>
    fderiv ℝ (u (p.1:ℝ)) p.2
  have hvalueSlice (t : Set.Icc (0:ℝ) T) (x : E3) :
      ‖u (t:ℝ) x‖ ≤ 6*‖F‖ := by
    have hp := hvalueNorm
    have hx := BoundedContinuousFunction.norm_coe_le_norm value (t,x)
    calc
      ‖u (t:ℝ) x‖ = ‖value (t,x)‖ := by rw [hvaluePoint]
      _ ≤ ‖value‖ := hx
      _ ≤ 6*‖F‖ := hvalueNorm
  have hgradPointBound (p : Slab T) :
      ‖gradRaw p‖ ≤ 12*‖F‖ + C₀*H := by
    let f : E3 → E6 := fun x => u (p.1:ℝ) x
    have hval : ∀ x, ‖f x‖ ≤ 6*‖F‖ := fun x => hvalueSlice p.1 x
    have hhess : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₀*H := by
      intro x
      change ‖hessRaw (p.1,x)‖ ≤ C₀*H
      exact hessPointBound (p.1,x)
    have hAnonneg : 0 ≤ 6*‖F‖ := by positivity
    have hinterp :=
      PoincareConjecture.ParallelImplementation.GradientSupInterpolation.gradient_sup_interpolation
        f (hSch.1 (p.1:ℝ) p.1.2)
        (6*‖F‖) (C₀*H) 1 hAnonneg hMnonneg (by norm_num) hval hhess p.2
    calc
      ‖gradRaw p‖ ≤ 2*(6*‖F‖)/1 + (C₀*H)*1 := by
        change ‖fderiv ℝ f p.2‖ ≤ _
        exact hinterp
      _ = 12*‖F‖ + C₀*H := by ring
  let grad : Slab T →ᵇ (E3 →L[ℝ] E6) :=
    BoundedContinuousFunction.ofNormedAddCommGroup gradRaw hgradCont
      (12*‖F‖ + C₀*H) (by intro p; exact hgradPointBound p)
  have hgradPoint (p : Slab T) : grad p = gradRaw p := rfl
  have hgradNorm : ‖grad‖ ≤ 12*‖F‖ + C₀*H :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hgradCont (by positivity)
      (fun p => hgradPointBound p)

  let lapRaw : Slab T → E6 := fun p => ∑ i : Fin 3, hessRaw p (ei i) (ei i)
  let qRaw : Slab T → E6 := fun p => lapRaw p + F ((p.1:ℝ),p.2)
  have hqCont : Continuous qRaw := by
    dsimp [qRaw, lapRaw]
    have hEval1 : Continuous (fun p : Slab T => hessRaw p) := hessCont
    have hEval1' (i : Fin 3) : Continuous (fun p : Slab T => hessRaw p (ei i)) := by
      exact hEval1.clm_apply continuous_const
    have hEval2 (i : Fin 3) : Continuous (fun p : Slab T => hessRaw p (ei i) (ei i)) := by
      exact (hEval1' i).clm_apply continuous_const
    have hsum : Continuous (fun p : Slab T => ∑ i : Fin 3, hessRaw p (ei i) (ei i)) :=
      continuous_finsetSum Finset.univ (fun i hi => hEval2 i)
    have hFp : Continuous (fun p : Slab T => F ((p.1:ℝ),p.2)) := by
      exact F.continuous.comp
        (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd)
    exact hsum.add hFp
  have hqPointBound (p : Slab T) : ‖qRaw p‖ ≤ ‖F‖ + 3*C₀*H := by
    have hterm (i : Fin 3) : ‖hessRaw p (ei i) (ei i)‖ ≤ C₀*H := by
      have hi1 : ‖ei i‖ = 1 := by simp [ei]
      have hi2 : ‖(hessRaw p) (ei i)‖ ≤ ‖hessRaw p‖ := by
        simpa [hi1] using (ContinuousLinearMap.le_opNorm (hessRaw p) (ei i))
      have hi3 : ‖(hessRaw p) (ei i) (ei i)‖ ≤ ‖(hessRaw p) (ei i)‖ := by
        simpa [hi1] using
          (ContinuousLinearMap.le_opNorm ((hessRaw p) (ei i)) (ei i))
      calc
        ‖hessRaw p (ei i) (ei i)‖ ≤ ‖(hessRaw p) (ei i)‖ := hi3
        _ ≤ ‖hessRaw p‖ := hi2
        _ ≤ C₀*H := hessPointBound p
    have hlap : ‖lapRaw p‖ ≤ 3*C₀*H := by
      calc
        ‖lapRaw p‖ ≤ ∑ i : Fin 3, ‖hessRaw p (ei i) (ei i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin 3, C₀*H := Finset.sum_le_sum (fun i hi => hterm i)
        _ = 3*C₀*H := by simp [Finset.sum_const, Fintype.card_fin]; ring
    calc
      ‖qRaw p‖ ≤ ‖lapRaw p‖ + ‖F ((p.1:ℝ),p.2)‖ := norm_add_le _ _
      _ ≤ 3*C₀*H + ‖F‖ := add_le_add hlap
        (BoundedContinuousFunction.norm_coe_le_norm F ((p.1:ℝ),p.2))
      _ = ‖F‖ + 3*C₀*H := by ring
  let qField : Slab T →ᵇ E6 := BoundedContinuousFunction.ofNormedAddCommGroup
    qRaw hqCont (‖F‖+3*C₀*H) hqPointBound
  have hqPoint (p : Slab T) : qField p = qRaw p := rfl
  have hqNorm : ‖qField‖ ≤ ‖F‖+3*C₀*H :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hqCont (by positivity)
      (fun p => hqPointBound p)

  have hpowSum (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
      a^alpha + b^alpha ≤ 2*(a+b)^alpha := by
    have haa : a^alpha ≤ (a+b)^alpha :=
      Real.rpow_le_rpow ha0 (le_add_of_nonneg_right hb0) ha.le
    have hbb : b^alpha ≤ (a+b)^alpha :=
      Real.rpow_le_rpow hb0 (le_add_of_nonneg_left ha0) ha.le
    nlinarith
  have hhessHolder : ∀ p q : Slab T,
      ‖hessRaw p-hessRaw q‖ ≤ (2*C₀*H)*parabolicRho p q^alpha := by
    intro p q
    have hs := hSch.2.2 (p.1:ℝ) p.1.2 (q.1:ℝ) q.1.2 p.2 q.2
    have htime : |(p.1:ℝ)-(q.1:ℝ)|^(alpha/2) =
        (Real.sqrt |(p.1:ℝ)-(q.1:ℝ)|)^alpha :=
      Real.rpow_div_two_eq_sqrt alpha (abs_nonneg _)
    have hpow := hpowSum ‖p.2-q.2‖ (Real.sqrt |(p.1:ℝ)-(q.1:ℝ)|)
      (norm_nonneg _) (Real.sqrt_nonneg _)
    have hrho : parabolicRho p q = ‖p.2-q.2‖ +
        Real.sqrt |(p.1:ℝ)-(q.1:ℝ)| := rfl
    calc
      ‖hessRaw p-hessRaw q‖ ≤ C₀*H*(‖p.2-q.2‖^alpha+
          |(p.1:ℝ)-(q.1:ℝ)|^(alpha/2)) := by
        change ‖fderiv ℝ (fderiv ℝ (u (p.1:ℝ))) p.2 -
          fderiv ℝ (fderiv ℝ (u (q.1:ℝ))) q.2‖ ≤ _
        exact hs
      _ ≤ C₀*H*(2*(parabolicRho p q)^alpha) := by
        rw [htime, hrho]
        exact mul_le_mul_of_nonneg_left hpow hMnonneg
      _ = (2*C₀*H)*parabolicRho p q^alpha := by ring

  obtain ⟨hessInc, hessIncNorm, hessIncEq⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF.exists_bounded_parabolic_increment
      T alpha (2*C₀*H) ha (by positivity) hess hess.continuous (by
        intro p q
        simpa [hhessPoint p, hhessPoint q] using hhessHolder p q)

  have hlapHolder (p q : Slab T) :
      ‖lapRaw p-lapRaw q‖ ≤ (6*C₀*H)*parabolicRho p q^alpha := by
    have hsumEq : lapRaw p-lapRaw q =
        ∑ i : Fin 3, (hessRaw p-hessRaw q) (ei i) (ei i) := by
      ext k
      simp [lapRaw, hessRaw, Finset.sum_sub_distrib]
    have hterm (i : Fin 3) :
        ‖(hessRaw p-hessRaw q) (ei i) (ei i)‖ ≤ ‖hessRaw p-hessRaw q‖ := by
      have hi : ‖ei i‖ = 1 := by simp [ei]
      have hi1 : ‖(hessRaw p-hessRaw q) (ei i)‖ ≤ ‖hessRaw p-hessRaw q‖ := by
        simpa [hi] using (ContinuousLinearMap.le_opNorm
          (hessRaw p-hessRaw q) (ei i))
      have hi2 : ‖(hessRaw p-hessRaw q) (ei i) (ei i)‖ ≤
          ‖(hessRaw p-hessRaw q) (ei i)‖ := by
        simpa [hi] using (ContinuousLinearMap.le_opNorm
          ((hessRaw p-hessRaw q) (ei i)) (ei i))
      exact hi2.trans hi1
    calc
      ‖lapRaw p-lapRaw q‖ = ‖∑ i : Fin 3,
          (hessRaw p-hessRaw q) (ei i) (ei i)‖ := by rw [hsumEq]
      _ ≤ ∑ i : Fin 3, ‖(hessRaw p-hessRaw q) (ei i) (ei i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, ‖hessRaw p-hessRaw q‖ :=
        Finset.sum_le_sum (fun i hi => hterm i)
      _ = 3*‖hessRaw p-hessRaw q‖ := by simp [Finset.sum_const, Fintype.card_fin]
      _ ≤ 3*((2*C₀*H)*parabolicRho p q^alpha) :=
        mul_le_mul_of_nonneg_left (hhessHolder p q) (by positivity)
      _ = (6*C₀*H)*parabolicRho p q^alpha := by ring
  have hqHolder : ∀ p q : Slab T,
      ‖qRaw p-qRaw q‖ ≤ ((6*C₀+1)*H)*parabolicRho p q^alpha := by
    intro p q
    have hFdiff := hF p q
    have hqdiff : qRaw p-qRaw q =
        (lapRaw p-lapRaw q) + (F ((p.1:ℝ),p.2)-F ((q.1:ℝ),q.2)) := by
      dsimp [qRaw]
      abel
    calc
      ‖qRaw p-qRaw q‖ = ‖(lapRaw p-lapRaw q) +
          (F ((p.1:ℝ),p.2)-F ((q.1:ℝ),q.2))‖ := by rw [hqdiff]
      _ ≤ ‖lapRaw p-lapRaw q‖ +
          ‖F ((p.1:ℝ),p.2)-F ((q.1:ℝ),q.2)‖ := norm_add_le _ _
      _ ≤ (6*C₀*H)*parabolicRho p q^alpha + H*parabolicRho p q^alpha :=
        add_le_add (hlapHolder p q) hFdiff
      _ = ((6*C₀+1)*H)*parabolicRho p q^alpha := by ring
  obtain ⟨qInc, qIncNorm, qIncEq⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF.exists_bounded_parabolic_increment
      T alpha ((6*C₀+1)*H) ha (by positivity) qField qField.continuous (by
        intro p q
        simpa [hqPoint p, hqPoint q] using hqHolder p q)

  have hC2 (t : Set.Icc (0:ℝ) T) : ContDiff ℝ 2 (u (t:ℝ)) := by
    exact hSch.1 (t:ℝ) t.2
  have hjetBase :
      (value, (grad, hess)) ∈ spaceTimeC2JetSet T := by
    intro t
    constructor
    · intro x
      have hfd := ((hC2 t).differentiable (by norm_num) x).hasFDerivAt
      have hv : (fun y : E3 => value (t,y)) = fun y => u (t:ℝ) y := by
        funext y
        exact hvaluePoint (t,y)
      have hg : grad (t,x) = fderiv ℝ (u (t:ℝ)) x := hgradPoint (t,x)
      rw [hv, hg]
      exact hfd
    · intro x
      have hfd : ContDiff ℝ 1 (fun y : E3 => fderiv ℝ (u (t:ℝ)) y) :=
        (hC2 t).fderiv_right (m := 1) (by norm_num)
      have hfd' := (hfd.differentiable (by norm_num) x).hasFDerivAt
      have hg : (fun y : E3 => grad (t,y)) =
          fun y => fderiv ℝ (u (t:ℝ)) y := by
        funext y
        exact hgradPoint (t,y)
      have hh : hess (t,x) = fderiv ℝ (fderiv ℝ (u (t:ℝ))) x := by
        exact hhessPoint (t,x)
      rw [hg, hh]
      exact hfd'

  have hdiag (t : Set.Icc (0:ℝ) T) (x : E3) (i : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ (u (t:ℝ)) y (ei i)) x (ei i) =
        fderiv ℝ (fderiv ℝ (u (t:ℝ))) x (ei i) (ei i) := by
    let ev : (E3 →L[ℝ] E6) →L[ℝ] E6 :=
      ContinuousLinearMap.apply ℝ E6 (ei i)
    have hgradDiff : DifferentiableAt ℝ
        (fun y : E3 => fderiv ℝ (u (t:ℝ)) y) x :=
      ((hC2 t).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) x
    have hclm := fderiv_clm_apply
      (differentiableAt_const (c := ev) (x := x)) hgradDiff
    have happly := congrArg (fun L : E3 →L[ℝ] E6 => L (ei i)) hclm
    simpa [ev] using happly

  have hgraph : (value, qField) ∈
      PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.slabTimeDerivativeGraph T := by
    change ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ x : E3,
      HasDerivAt
        (PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
          value x) (qField (t,x)) (t:ℝ)
    intro t ht0 htT x
    let ts : Set.Icc (0:ℝ) T := ⟨(t:ℝ), ⟨ht0.le, htT.le⟩⟩
    have hderiv := hclass.2.2.2.2 (t:ℝ) ⟨ht0, htT⟩ x
    have hevent :
        PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension
          value x =ᶠ[𝓝 (t:ℝ)] (fun s => u s x) := by
      have hnear : ∀ᶠ s : ℝ in 𝓝 (t:ℝ), s ∈ Set.Ioo (0:ℝ) T :=
        isOpen_Ioo.mem_nhds ⟨ht0, htT⟩
      filter_upwards [hnear] with s hs
      have hmem : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1.le, hs.2.le⟩
      simp [PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.timeExtension,
        hmem, hvaluePoint]
    have hderivExt := hderiv.congr_of_eventuallyEq hevent
    have hq : qField (ts,x) =
        (∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u (t:ℝ)) y (ei i)) x (ei i)) +
          F ((t:ℝ),x) := by
      rw [hqPoint]
      simp only [qRaw, lapRaw, hessRaw]
      simp_rw [← hdiag ts x]
      rfl
    rw [hq]
    simpa [ei] using hderivExt

  have hzero (x : E3) : value (⟨0, le_rfl, hT.le⟩,x) = 0 := by
    calc
      value (⟨0, le_rfl, hT.le⟩,x) = u 0 x := hvaluePoint _
      _ = 0 := by
        have hz : u 0 = 0 := by
          simpa [u] using hclass.1
        exact congrFun hz x
  ·
    let jet : Jet T := (value, (grad,hess))
    let holder : HolderJet T := (jet,hessInc)
    let z : FullJet T := ((holder,qField),qInc)
    have hholder : holder ∈ parabolicC2HolderSet T alpha := by
      change jet ∈ spaceTimeC2JetSet T ∧ ∀ p : Pair T,
        hessInc p = (parabolicRho p.1.1 p.1.2^alpha)⁻¹ •
          (hess p.1.1-hess p.1.2)
      refine ⟨hjetBase, ?_⟩
      intro p
      simpa [hhessPoint p.1.1, hhessPoint p.1.2] using hessIncEq p
    have htrace : ∀ x : E3, value (⟨0, le_rfl, hT.le⟩,x)=0 := hzero
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · change z.1.1 ∈ parabolicC2HolderSet T alpha ∧
        (z.1.1.1.1,z.1.2) ∈
          PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph.slabTimeDerivativeGraph T ∧
        (∀ p : Pair T, z.2 p = (parabolicRho p.1.1 p.1.2^alpha)⁻¹ •
          (z.1.2 p.1.1-z.1.2 p.1.2)) ∧
        ∀ x : E3, z.1.1.1.1 (⟨0, le_rfl, hT.le⟩,x)=0
      exact ⟨hholder, hgraph, qIncEq, htrace⟩
    · intro p
      exact hvaluePoint p
    · intro p
      rfl
    ·
      let S : ℝ := C*(‖F‖+H)
      have hFnonneg : 0 ≤ ‖F‖ := norm_nonneg _
      have hSval : 6*‖F‖ ≤ S := by
        dsimp [S,C]
        nlinarith [mul_nonneg hC₀pos.le hFnonneg, mul_nonneg hC₀pos.le hH]
      have hSgrad : 12*‖F‖+C₀*H ≤ S := by
        dsimp [S,C]
        nlinarith [mul_nonneg hC₀pos.le hFnonneg, mul_nonneg hC₀pos.le hH]
      have hShess : C₀*H ≤ S := by
        dsimp [S,C]
        nlinarith [mul_nonneg hC₀pos.le hFnonneg, mul_nonneg hC₀pos.le hH]
      have hShessInc : 2*C₀*H ≤ S := by
        dsimp [S,C]
        nlinarith [mul_nonneg hC₀pos.le hFnonneg, mul_nonneg hC₀pos.le hH]
      have hSq : ‖F‖+3*C₀*H ≤ S := by
        dsimp [S,C]
        nlinarith [mul_nonneg hC₀pos.le hFnonneg, mul_nonneg hC₀pos.le hH]
      have hSqInc : (6*C₀+1)*H ≤ S := by
        dsimp [S,C]
        nlinarith [mul_nonneg hC₀pos.le hFnonneg, mul_nonneg hC₀pos.le hH]
      have hjetNorm : ‖(value,(grad,hess))‖ ≤ S := by
        rw [Prod.norm_def, Prod.norm_def]
        apply max_le
        · exact hvalueNorm.trans hSval
        · apply max_le
          · exact hgradNorm.trans hSgrad
          · exact hessNorm.trans hShess
      have hholderNorm : ‖(jet,hessInc)‖ ≤ S := by
        rw [Prod.norm_def]
        apply max_le
        · exact hjetNorm
        · exact hessIncNorm.trans hShessInc
      have hzNorm : ‖((holder,qField),qInc)‖ ≤ S := by
        rw [Prod.norm_def, Prod.norm_def]
        apply max_le
        · apply max_le
          · exact hholderNorm
          · exact hqNorm.trans hSq
        · exact qIncNorm.trans hSqInc
      simpa [S, z] using hzNorm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullVectorDuhamelJet
