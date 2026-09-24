import PoincareConjecture.ParallelImplementation.DuhamelForcedHeatEquation
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedDuhamelOperator
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.FullDuhamelSpatialC2
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixComponentDuhamelClassical
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The coordinate-defined vector Duhamel integral is an actual classical six-component solution. -/
theorem six_component_duhamel_classical (T alpha H : ℝ)
    (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1) (hH : 0 ≤ H)
    (F : (ℝ × E3) →ᵇ E6)
    (hholder : ∀ t ∈ Icc (0:ℝ) T, ∀ x y, ‖F (t,x)-F (t,y)‖ ≤ H*‖x-y‖^alpha) :
    let u : ℝ → E3 → E6 := fun t x => WithLp.toLp 2 (fun k : Fin 6 =>
      ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y)*(F (s,y) k))
    u 0 = 0 ∧ ContinuousOn (fun p : ℝ × E3 => u p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) ∧
      (∀ t ∈ Icc (0:ℝ) T, ContDiff ℝ 2 (u t)) ∧
      (∀ t ∈ Icc (0:ℝ) T, ∀ x, ‖u t x‖ ≤ 6*T*‖F‖) ∧
      ∀ t ∈ Ioo (0:ℝ) T, ∀ x,
        HasDerivAt (fun s => u s x)
          ((∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u t) y
            (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1))+F (t,x)) t :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  let u : ℝ → E3 → E6 := fun t x => WithLp.toLp 2 (fun k : Fin 6 =>
    ∫ s in (0:ℝ)..t, ∫ y : E3,
      euclideanHeatKernel 3 (t-s) (x-y) * (F (s,y) k))
  let e : E6 ≃L[ℝ] (Fin 6 → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 => ℝ)
  let Fk : Fin 6 → (ℝ × E3) →ᵇ ℝ := fun k =>
    BoundedContinuousFunction.mk
      (ContinuousMap.mk (fun p : ℝ × E3 => F p k)
        (((ContinuousLinearMap.proj k).comp e.toContinuousLinearMap).continuous.comp F.continuous))
      ⟨2 * ‖F‖, by
        intro p q
        calc
          dist (F p k) (F q k) ≤ ‖F p k‖ + ‖F q k‖ := dist_le_norm_add_norm _ _
          _ ≤ ‖F p‖ + ‖F q‖ := add_le_add
            (by simpa using (PiLp.norm_apply_le (p := 2) (x := F p) k))
            (by simpa using (PiLp.norm_apply_le (p := 2) (x := F q) k))
          _ ≤ ‖F‖ + ‖F‖ := add_le_add
            (BoundedContinuousFunction.norm_coe_le_norm F p)
            (BoundedContinuousFunction.norm_coe_le_norm F q)
          _ = 2 * ‖F‖ := by ring⟩
  have hFkNorm (k : Fin 6) : ‖Fk k‖ ≤ ‖F‖ := by
    apply (BoundedContinuousFunction.norm_le (f := Fk k) (C := ‖F‖)
      (norm_nonneg _)).2
    intro p
    calc
      ‖Fk k p‖ = ‖F p k‖ := by rfl
      _ ≤ ‖F p‖ := by simpa using (PiLp.norm_apply_le (p := 2) (x := F p) k)
      _ ≤ ‖F‖ := BoundedContinuousFunction.norm_coe_le_norm F p
  have hholderK (k : Fin 6) : ∀ t ∈ Icc (0:ℝ) T, ∀ x y : E3,
      |Fk k (t,x) - Fk k (t,y)| ≤ H * ‖x-y‖^alpha := by
    intro t ht x y
    have hc : ‖(F (t,x) - F (t,y)) k‖ ≤ ‖F (t,x) - F (t,y)‖ := by
      simpa using (PiLp.norm_apply_le (p := 2) (x := F (t,x) - F (t,y)) k)
    calc
      |Fk k (t,x) - Fk k (t,y)| = ‖(F (t,x) - F (t,y)) k‖ := by
        simp [Fk, Real.norm_eq_abs]
      _ ≤ ‖F (t,x) - F (t,y)‖ := hc
      _ ≤ H * ‖x-y‖^alpha := hholder t ht x y
  obtain ⟨D, hD, hDbound, _⟩ := clipped_duhamel_operator T hT.le
  have hchange (s a : ℝ) (x : E3) (k : Fin 6) :
      (∫ y : E3, euclideanHeatKernel 3 a (x-y) * (F (s,y) k)) =
        ∫ y : E3, euclideanHeatKernel 3 a y * (F (s,x-y) k) := by
    let g : E3 → ℝ := fun y => euclideanHeatKernel 3 a y * (F (s,x-y) k)
    have hMP : MeasurePreserving (fun y : E3 => x-y) volume volume :=
      MeasureTheory.Measure.measurePreserving_sub_left volume x
    have hME : MeasurableEmbedding (fun y : E3 => x-y) :=
      (MeasurableEquiv.subLeft x).measurableEmbedding
    calc
      (∫ y : E3, euclideanHeatKernel 3 a (x-y) * (F (s,y) k)) =
          ∫ y : E3, g (x-y) := by
            congr 1
            funext y
            simp [g]
      _ = ∫ y : E3, g y := (hMP.integral_comp hME g)
      _ = ∫ y : E3, euclideanHeatKernel 3 a y * (F (s,x-y) k) := rfl
  have hpoint (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (x : E3) (k : Fin 6) :
      D (Fk k) (t,x) = (u t x) k := by
    rw [hD (Fk k) (t,x)]
    simp only [min_eq_right ht.2, max_eq_right ht.1]
    dsimp [u]
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hchange s (t-s) x k).symm
  let W : ℝ × E3 → E6 := fun p =>
    WithLp.toLp 2 (fun k : Fin 6 => D (Fk k) p)
  have hWcont : Continuous W := by
    have hcoords : Continuous (fun p : ℝ × E3 => fun k : Fin 6 => D (Fk k) p) :=
      continuous_pi fun k => (D (Fk k)).continuous
    change Continuous (fun p : ℝ × E3 => e.symm (fun k : Fin 6 => D (Fk k) p))
    exact e.symm.continuous.comp hcoords
  have hWpoint (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (x : E3) :
      W (t,x) = u t x := by
    apply e.injective
    change (fun k : Fin 6 => D (Fk k) (t,x)) = fun k => (u t x) k
    funext k
    exact hpoint t ht x k
  have hzero : u 0 = 0 := by
    funext x
    ext k
    simp [u]
  have hcontinuous :
      ContinuousOn (fun p : ℝ × E3 => u p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
    apply hWcont.continuousOn.congr
    intro p hp
    exact (hWpoint p.1 hp.1 p.2).symm
  obtain ⟨C, hCpos, hC⟩ := full_duhamel_spatial_C2 alpha ha ha1
  have hC2 : ∀ t ∈ Icc (0:ℝ) T, ContDiff ℝ 2 (u t) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hu0 : u 0 = fun _ : E3 => (0 : E6) := by
        funext x
        simpa using congrFun hzero x
      rw [hu0]
      exact contDiff_const
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      apply (contDiff_piLp 2).2
      intro k
      have htemp := hC (Fk k) H t hH htpos (by
        intro s hs x y
        apply hholderK k s
        exact ⟨hs.1, hs.2.trans ht.2⟩)
      simpa [u, Fk] using htemp.1
  let ei : Fin 3 → E3 := fun i => EuclideanSpace.single i 1
  let pk : Fin 6 → E6 →L[ℝ] ℝ := fun k =>
    (ContinuousLinearMap.proj k).comp e.toContinuousLinearMap
  have hsecondCoord (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (x : E3)
      (i : Fin 3) (k : Fin 6) :
      (fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) k =
        fderiv ℝ (fun y => fderiv ℝ (fun z => (u t z) k) y (ei i)) x (ei i) := by
    have hct := hC2 t ht
    have hfirst (z : E3) :
        fderiv ℝ (fun y => (u t y) k) z = (pk k).comp (fderiv ℝ (u t) z) := by
      have hh := fderiv_clm_apply
        (differentiableAt_const (c := pk k) (x := z))
        (hct.differentiable (by norm_num) z)
      simpa [pk, e] using hh
    have hfirstDir (z : E3) :
        fderiv ℝ (fun y => (u t y) k) z (ei i) =
          pk k (fderiv ℝ (u t) z (ei i)) := by
      have hh := congrArg (fun L : E3 →L[ℝ] ℝ => L (ei i)) (hfirst z)
      simpa [pk, e] using hh
    have hgradEq :
        (fun y : E3 => fderiv ℝ (fun z => (u t z) k) y (ei i)) =
          (fun y => pk k (fderiv ℝ (u t) y (ei i))) := by
      funext y
      exact hfirstDir y
    have hgradCD : ContDiff ℝ 1 (fun y : E3 => fderiv ℝ (u t) y (ei i)) := by
      have hfd : ContDiff ℝ 1 (fderiv ℝ (u t)) :=
        hct.fderiv_right (m := 1) (by norm_num)
      exact hfd.clm_apply contDiff_const
    have hgradDiff := hgradCD.differentiable (by norm_num) x
    have hsecond := fderiv_clm_apply
      (differentiableAt_const (c := pk k) (x := x)) hgradDiff
    rw [hgradEq]
    have hh := congrArg (fun L : E3 →L[ℝ] ℝ => L (ei i)) hsecond
    simpa [pk, e] using hh.symm
  have hlapCoord (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (x : E3) (k : Fin 6) :
      (∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) k =
        ∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ (fun z => (u t z) k) y (ei i)) x (ei i) := by
    change pk k (∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) = _
    calc
      pk k (∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) =
          ∑ i : Fin 3,
            pk k (fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) := by
              exact map_sum (pk k)
                (fun i : Fin 3 => fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i))
                Finset.univ
      _ = ∑ i : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ (fun z => (u t z) k) y (ei i)) x (ei i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hsecondCoord t ht x i k
  have hnorm : ∀ t ∈ Icc (0:ℝ) T, ∀ x : E3, ‖u t x‖ ≤ 6*T*‖F‖ := by
    intro t ht x
    let ei6 : Fin 6 → E6 := fun k => EuclideanSpace.single k 1
    have hcoord (k : Fin 6) : |(u t x) k| ≤ T * ‖F‖ := by
      have hv : ‖D (Fk k) (t,x)‖ ≤ T * ‖F‖ := by
        calc
          ‖D (Fk k) (t,x)‖ ≤ ‖D (Fk k)‖ :=
            BoundedContinuousFunction.norm_coe_le_norm (D (Fk k)) (t,x)
          _ ≤ T * ‖Fk k‖ := hDbound (Fk k)
          _ ≤ T * ‖F‖ := mul_le_mul_of_nonneg_left (hFkNorm k) hT.le
      calc
        |(u t x) k| = ‖D (Fk k) (t,x)‖ := by rw [← hpoint t ht x k]; simp
        _ ≤ T * ‖F‖ := hv
    have hdecomp (v : E6) : v = ∑ k : Fin 6, v k • ei6 k := by
      simpa [ei6, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin 6) ℝ).sum_repr v).symm
    calc
      ‖u t x‖ = ‖∑ k : Fin 6, (u t x) k • ei6 k‖ :=
        congrArg norm (hdecomp (u t x))
      _ ≤ ∑ k : Fin 6, ‖(u t x) k • ei6 k‖ := norm_sum_le _ _
      _ = ∑ k : Fin 6, |(u t x) k| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [norm_smul]
        simp [ei6, PiLp.norm_single, Real.norm_eq_abs]
      _ ≤ ∑ k : Fin 6, T * ‖F‖ := Finset.sum_le_sum (fun k hk => hcoord k)
      _ = 6*T*‖F‖ := by simp [Finset.sum_const, Fintype.card_fin]; ring
  have hcoordDeriv (k : Fin 6) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) T) (x : E3) :
      HasDerivAt (fun s => (u s x) k)
        (((∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) k) + F (t,x) k) t := by
    have hPDE :=
      PoincareConjecture.ParallelImplementation.DuhamelForcedHeatEquation.duhamel_forced_heat_equation
        alpha ha ha1 (Fk k) H T hH hT (by
          intro s hs y z
          exact hholderK k s hs y z)
    have hs := hPDE.2 t ht x
    have htcc : t ∈ Icc (0:ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hlap := hlapCoord t htcc x k
    simpa [u, Fk, hlap] using hs
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) T) (x : E3) :
      HasDerivAt (fun s => u s x)
        ((∑ i : Fin 3,
          fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) + F (t,x)) t := by
    let d : E6 :=
      (∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (u t) y (ei i)) x (ei i)) + F (t,x)
    have hpi : HasDerivAt (fun s : ℝ => e (u s x)) (e d) t := by
      apply hasDerivAt_pi.mpr
      intro k
      simpa [e, d] using hcoordDeriv k t ht x
    have hback :=
      ((e.symm : (Fin 6 → ℝ) →L[ℝ] E6).hasFDerivAt).comp_hasDerivAt t hpi
    convert hback using 1
    all_goals try rfl
  refine ⟨?_, hcontinuous, hC2, hnorm, ?_⟩
  · exact hzero
  · intro t ht x
    simpa [ei] using hderiv t ht x
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixComponentDuhamelClassical
