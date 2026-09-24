import PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SlabTimeLipschitz
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The genuine interior time derivative controls all closed-slab time differences. -/
theorem slab_time_lipschitz (T : ℝ) (hT : 0 ≤ T)
    (f g : Slab T →ᵇ E6) (hderiv : (f,g) ∈ slabTimeDerivativeGraph T) :
    ∀ s t : Set.Icc (0:ℝ) T, ∀ x : E3,
      ‖f (t,x)-f (s,x)‖ ≤ ‖g‖ * |(t:ℝ)-(s:ℝ)| :=
/- SWARM_PROOF_BEGIN -/
by
  change ∀ u : Set.Icc (0 : ℝ) T, 0 < (u : ℝ) → (u : ℝ) < T → ∀ x : E3,
    HasDerivAt (timeExtension f x) (g (u,x)) (u : ℝ) at hderiv
  intro s t x
  by_cases hTzero : T = 0
  · have hsval : (s : ℝ) = 0 :=
      le_antisymm (by simpa [hTzero] using s.2.2) s.2.1
    have htval : (t : ℝ) = 0 :=
      le_antisymm (by simpa [hTzero] using t.2.2) t.2.1
    have hst : s = t := Subtype.ext (hsval.trans htval.symm)
    subst t
    simp
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hTzero)
    let F : ℝ → E6 := fun r => timeExtension f x r
    have hFcont : ContinuousOn F (Set.Icc (0 : ℝ) T) := by
      apply continuousOn_iff_continuous_restrict.mpr
      let slice : Set.Icc (0 : ℝ) T → Slab T := fun u => (u,x)
      have hslice : Continuous slice := by
        change Continuous (fun u : Set.Icc (0 : ℝ) T => (u,x))
        exact continuous_id.prodMk continuous_const
      have heq : (Set.Icc (0 : ℝ) T).restrict F =
          fun u : Set.Icc (0 : ℝ) T => f (u,x) := by
        funext u
        change (if h : (u : ℝ) ∈ Set.Icc (0 : ℝ) T then
          f (⟨(u : ℝ), h⟩,x) else 0) = _
        rw [dif_pos u.2]
      rw [heq]
      exact f.continuous.comp hslice
    have hinterior (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
        ‖F b - F a‖ ≤ ‖g‖ * |b-a| := by
      have hsegcont : ContinuousOn F (Set.Icc a b) :=
        hFcont.mono (by
          intro u hu
          exact ⟨(le_trans ha.le hu.1), (le_trans hu.2 hb.le)⟩)
      have hderiv' : ∀ u ∈ Set.Ico a b,
          HasDerivWithinAt F (timeExtension g x u) (Set.Ici u) u := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
        have huT : u < T := lt_of_lt_of_le hu.2 hb.le
        let v : Set.Icc (0 : ℝ) T := ⟨u, ⟨hu0.le, huT.le⟩⟩
        have hd := hderiv v hu0 huT x
        have hvalue : timeExtension g x u = g (v,x) := by
          simp [timeExtension, v, Set.mem_Icc, hu0.le, huT.le]
        have hd' : HasDerivAt F (timeExtension g x u) u := by
          change HasDerivAt (timeExtension f x) (timeExtension g x u) u
          rw [← hvalue] at hd
          exact hd
        exact hd'.hasDerivWithinAt
      have hderivBound : ∀ u ∈ Set.Ico a b,
          ‖timeExtension g x u‖ ≤ ‖g‖ := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
        have huT : u < T := lt_of_lt_of_le hu.2 hb.le
        let v : Set.Icc (0 : ℝ) T := ⟨u, ⟨hu0.le, huT.le⟩⟩
        have hvalue : timeExtension g x u = g (v,x) := by
          simp [timeExtension, v, Set.mem_Icc, hu0.le, huT.le]
        rw [hvalue]
        exact BoundedContinuousFunction.norm_coe_le_norm g (v,x)
      have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment
        hsegcont hderiv' hderivBound
      have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
      have h := hseg b hbmem
      simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using h
    let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    let approx : Set.Icc (0 : ℝ) T → ℕ → ℝ :=
      fun u n => (1 - eps n) * (u : ℝ) + eps n * (T / 2)
    have heps : Filter.Tendsto eps Filter.atTop (𝓝 0) := by
      change Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have heps_pos (n : ℕ) : 0 < eps n := by
      dsimp [eps]
      positivity
    have heps_le_one (n : ℕ) : eps n ≤ 1 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      dsimp [eps]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    have happrox_mem (u : Set.Icc (0 : ℝ) T) (n : ℕ) :
        approx u n ∈ Set.Ioo (0 : ℝ) T := by
      have hc : 0 ≤ 1 - eps n := sub_nonneg.mpr (heps_le_one n)
      have hleft : 0 ≤ (1 - eps n) * (u : ℝ) := mul_nonneg hc u.2.1
      have hright : 0 < eps n * (T / 2) := mul_pos (heps_pos n) (half_pos hTpos)
      have hupper1 : (1 - eps n) * (u : ℝ) ≤ (1 - eps n) * T :=
        mul_le_mul_of_nonneg_left u.2.2 hc
      have hupper2 : eps n * (T / 2) < eps n * T :=
        mul_lt_mul_of_pos_left (by linarith) (heps_pos n)
      constructor
      · change 0 < (1 - eps n) * (u : ℝ) + eps n * (T / 2)
        linarith
      · change (1 - eps n) * (u : ℝ) + eps n * (T / 2) < T
        calc
          _ < (1 - eps n) * T + eps n * T :=
            add_lt_add_of_le_of_lt hupper1 hupper2
          _ = T := by ring
    have happrox_tendsto (u : Set.Icc (0 : ℝ) T) :
        Filter.Tendsto (fun n => approx u n) Filter.atTop (𝓝 (u : ℝ)) := by
      have hconst1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
          Filter.atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
      have hcoef : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - eps n)
          Filter.atTop (𝓝 (1 : ℝ)) := by
        simpa using hconst1.sub heps
      have hleft : Filter.Tendsto (fun n : ℕ => (1 - eps n) * (u : ℝ))
          Filter.atTop (𝓝 ((1 : ℝ) * (u : ℝ))) :=
        hcoef.mul (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => (u : ℝ)) Filter.atTop (𝓝 (u : ℝ)))
      have hright : Filter.Tendsto (fun n : ℕ => eps n * (T / 2))
          Filter.atTop (𝓝 ((0 : ℝ) * (T / 2))) :=
        heps.mul (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => T / 2) Filter.atTop (𝓝 (T / 2)))
      simpa [approx] using hleft.add hright
    have happrox_within (u : Set.Icc (0 : ℝ) T) :
        Filter.Tendsto (fun n => approx u n) Filter.atTop
          (𝓝[Set.Icc (0 : ℝ) T] (u : ℝ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun n => approx u n) (happrox_tendsto u)
        (Filter.Eventually.of_forall fun n =>
          ⟨(happrox_mem u n).1.le, (happrox_mem u n).2.le⟩)
    have hordered (u v : Set.Icc (0 : ℝ) T) (huv : (u : ℝ) ≤ (v : ℝ)) :
        ‖f (v,x) - f (u,x)‖ ≤ ‖g‖ * |(v : ℝ)-(u : ℝ)| := by
      have hFu : Filter.Tendsto (fun n => F (approx u n)) Filter.atTop
          (𝓝 (F (u : ℝ))) :=
        (hFcont.continuousWithinAt u.2).tendsto.comp (happrox_within u)
      have hFv : Filter.Tendsto (fun n => F (approx v n)) Filter.atTop
          (𝓝 (F (v : ℝ))) :=
        (hFcont.continuousWithinAt v.2).tendsto.comp (happrox_within v)
      have happ_order (n : ℕ) : approx u n ≤ approx v n := by
        dsimp [approx]
        exact add_le_add
          (mul_le_mul_of_nonneg_left huv (sub_nonneg.mpr (heps_le_one n))) le_rfl
      have hleft : Filter.Tendsto
          (fun n => ‖F (approx v n) - F (approx u n)‖) Filter.atTop
          (𝓝 ‖F (v : ℝ) - F (u : ℝ)‖) := by
        have hsub := hFv.sub hFu
        simpa using hsub.norm
      have hright : Filter.Tendsto
          (fun n => ‖g‖ * |approx v n - approx u n|) Filter.atTop
          (𝓝 (‖g‖ * |(v : ℝ)-(u : ℝ)|)) := by
        have hdiff := (happrox_tendsto v).sub (happrox_tendsto u)
        simpa using tendsto_const_nhds.mul hdiff.abs
      have hineq (n : ℕ) :
          ‖F (approx v n) - F (approx u n)‖ ≤
            ‖g‖ * |approx v n - approx u n| := by
        exact hinterior (approx u n) (approx v n) (happrox_mem u n).1
          (happ_order n) (happrox_mem v n).2
      have hlim := le_of_tendsto_of_tendsto hleft hright
        (Filter.Eventually.of_forall hineq)
      have hval (w : Set.Icc (0 : ℝ) T) : F (w : ℝ) = f (w,x) := by
        change timeExtension f x (w : ℝ) = f (w,x)
        rw [timeExtension, dif_pos w.2]
      simpa [hval] using hlim
    by_cases hstEq : s = t
    · subst t
      simp
    · by_cases hst : (s : ℝ) ≤ (t : ℝ)
      · exact hordered s t hst
      · have hrev := hordered t s (le_of_not_ge hst)
        simpa [norm_sub_rev, abs_sub_comm] using hrev
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SlabTimeLipschitz
