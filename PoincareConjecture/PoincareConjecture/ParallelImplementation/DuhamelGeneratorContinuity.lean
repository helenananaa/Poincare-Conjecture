import PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ClippedDuhamelOperator
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.DuhamelGeneratorContinuity
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Time continuity of the actual heat solution and its Laplacian-plus-source expression. -/
theorem duhamel_generator_continuity
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 < T)
    (hholder : ∀ s ∈ Icc (0:ℝ) T, ∀ x y : E3,
      |F (s,x)-F (s,y)| ≤ L*‖x-y‖^alpha) :
    let u : ℝ → E3 → ℝ := fun t x => ∫ s in (0:ℝ)..t,
      ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)
    ∀ x : E3, ContinuousOn (fun t => u t x) (Ioo (0:ℝ) T) ∧
      ContinuousOn (fun t => (∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + F (t,x)) (Ioo (0:ℝ) T) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  intro x
  let u : ℝ → E3 → ℝ := fun t x => ∫ s in (0:ℝ)..t,
    ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)
  obtain ⟨D, hD, _, _⟩ := clipped_duhamel_operator T (le_of_lt hT)
  have hchange (s t : ℝ) (x : E3) :
      (∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)) =
        ∫ y : E3, euclideanHeatKernel 3 (t-s) y * F (s,x-y) := by
    let g : E3 → ℝ := fun y => euclideanHeatKernel 3 (t-s) y * F (s,x-y)
    have hcomp :=
      (Measure.measurePreserving_sub_left (volume : Measure E3) x).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding g
    calc
      (∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)) =
          ∫ y : E3, g (x-y) := by
            congr 1
            funext y
            simp [g]
      _ = ∫ y : E3, g y := hcomp
      _ = ∫ y : E3, euclideanHeatKernel 3 (t-s) y * F (s,x-y) := rfl
  have hpoint : ∀ t : ℝ, t ∈ Icc (0:ℝ) T → ∀ z : E3,
      D F (t,z) = ∫ s in (0:ℝ)..t,
        ∫ y : E3, euclideanHeatKernel 3 (t-s) (z-y) * F (s,y) := by
    intro t ht z
    rw [hD]
    simp only [min_eq_right ht.2, max_eq_right ht.1]
    apply intervalIntegral.integral_congr
    intro s hs
    exact (hchange s t z).symm
  have hDF : Continuous (fun p : ℝ × E3 => D F p) := (D F).continuous
  have hDFx : Continuous (fun t : ℝ => D F (t,x)) :=
    hDF.comp (continuous_id.prodMk continuous_const)
  have hvalue : ContinuousOn (fun t : ℝ => u t x) (Ioo (0:ℝ) T) := by
    apply hDFx.continuousOn.congr
    intro t ht
    symm
    exact hpoint t ⟨le_of_lt ht.1, le_of_lt ht.2⟩ x

  obtain ⟨C, hC, htemp⟩ :=
    PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder.actual_duhamel_temporal_schauder
      alpha ha ha1
  have hβ : 0 < alpha / 2 := by linarith
  let H : Fin 3 → ℝ → ℝ := fun i t =>
    fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)
  have hHbound : ∀ (i : Fin 3) (s t : ℝ), s ∈ Ioo (0:ℝ) T →
      t ∈ Ioo (0:ℝ) T → |H i s - H i t| ≤ C * L * |t-s|^(alpha/2) := by
    intro i s t hs ht
    rcases le_total s t with hst | hts
    · by_cases heq : s = t
      · subst t
        simp [Real.zero_rpow (ne_of_gt hβ)]
      · have hlt : s < t := lt_of_le_of_ne hst heq
        have hh : 0 < t-s := sub_pos.mpr hlt
        have hsum : s + (t-s) = t := by ring
        have hhold : ∀ q ∈ Icc (0:ℝ) (s+(t-s)), ∀ y z : E3,
            |F (q,y)-F (q,z)| ≤ L*‖y-z‖^alpha := by
          intro q hq y z
          apply hholder q
          exact ⟨hq.1, hq.2.trans (by rw [hsum]; exact le_of_lt ht.2)⟩
        have hb := htemp F L s (t-s) hL (le_of_lt hs.1) hh hhold x i i
        have hb' : |H i t - H i s| ≤ C * L * (t-s)^(alpha/2) := by
          simpa [H, hsum] using hb
        calc
          |H i s - H i t| = |H i t - H i s| := abs_sub_comm _ _
          _ ≤ C * L * (t-s)^(alpha/2) := hb'
          _ = C * L * |t-s|^(alpha/2) := by rw [abs_of_pos hh]
    · by_cases heq : t = s
      · subst s
        simp [Real.zero_rpow (ne_of_gt hβ)]
      · have hlt : t < s := lt_of_le_of_ne hts heq
        have hh : 0 < s-t := sub_pos.mpr hlt
        have hsum : t + (s-t) = s := by ring
        have hhold : ∀ q ∈ Icc (0:ℝ) (t+(s-t)), ∀ y z : E3,
            |F (q,y)-F (q,z)| ≤ L*‖y-z‖^alpha := by
          intro q hq y z
          apply hholder q
          exact ⟨hq.1, hq.2.trans (by rw [hsum]; exact le_of_lt hs.2)⟩
        have hb := htemp F L t (s-t) hL (le_of_lt ht.1) hh hhold x i i
        have hb' : |H i s - H i t| ≤ C * L * (s-t)^(alpha/2) := by
          simpa [H, hsum] using hb
        calc
          |H i s - H i t| ≤ C * L * (s-t)^(alpha/2) := hb'
          _ = C * L * |t-s|^(alpha/2) := by
            rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]

  have hHcont : ∀ i : Fin 3, ContinuousOn (fun t : ℝ => H i t) (Ioo (0:ℝ) T) := by
    intro i t ht
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    let w : ℝ → ℝ := fun z => (C*L) * |z-t|^(alpha/2)
    have hw : ContinuousAt w t := by
      have hpow : Continuous (fun z : ℝ => |z-t|^(alpha/2)) :=
        (Real.continuous_rpow_const hβ.le).comp
          ((continuous_id.sub continuous_const).abs)
      change ContinuousAt ((fun z : ℝ => C*L) * (fun z => |z-t|^(alpha/2))) t
      exact continuousAt_const.mul hpow.continuousAt
    have hw0 : w t = 0 := by
      simp [w, Real.zero_rpow (ne_of_gt hβ)]
    obtain ⟨δ, hδ, hδw⟩ := Metric.continuousAt_iff.mp hw ε hε
    refine ⟨δ, hδ, ?_⟩
    intro z hz hdist
    have hwz : w z < ε := by
      have hnonneg : 0 ≤ w z := by
        apply mul_nonneg
        · exact mul_nonneg hC.le hL
        · exact Real.rpow_nonneg (abs_nonneg _) _
      simpa [Real.dist_eq, hw0, abs_of_nonneg hnonneg] using hδw hdist
    have hdistH : dist (H i z) (H i t) ≤ w z := by
      rw [Real.dist_eq]
      calc
        |H i z - H i t| ≤ C * L * |t-z|^(alpha/2) := hHbound i z t hz ht
        _ = w z := by
          dsimp [w]
          rw [abs_sub_comm t z]
    exact lt_of_le_of_lt hdistH hwz

  have htrace : ContinuousOn (fun t : ℝ => ∑ i : Fin 3, H i t) (Ioo (0:ℝ) T) := by
    simpa using continuousOn_finsetSum (Finset.univ : Finset (Fin 3))
      (t := Ioo (0:ℝ) T) (fun i hi => hHcont i)
  have hFcont : ContinuousOn (fun t : ℝ => F (t,x)) (Ioo (0:ℝ) T) := by
    have hF : Continuous (fun p : ℝ × E3 => F p) := F.continuous
    exact (hF.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨?_, ?_⟩
  · simpa [u] using hvalue
  · convert htrace.add hFcont using 1
    ext t
    simp [H, u]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.DuhamelGeneratorContinuity
