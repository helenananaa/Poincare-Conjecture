import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetJointC1
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped ContDiff Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual continuous spatial/time jet fields give joint C1 regularity on the
open time strip. The zero extension outside the strip is not claimed smooth. -/
theorem contDiffOn_one_of_actual_full_jet
    (T alpha : ℝ) (hT : 0 < T) (z : FullJet T)
    (hzSpace : z.1.1 ∈ parabolicC2HolderSet T alpha)
    (hzTime : (z.1.1.1.1, z.1.2) ∈ slabTimeDerivativeGraph T) :
    ContDiffOn ℝ 1 (fun q : ℝ × E3 => timeExtension z.1.1.1.1 q.2 q.1)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set E3)) :=
/- SWARM_PROOF_BEGIN -/
by
  let U : Set (ℝ × E3) := Set.Ioo (0 : ℝ) T ×ˢ Set.univ
  let val : Slab T →ᵇ E6 := z.1.1.1.1
  let grad : Slab T →ᵇ (E3 →L[ℝ] E6) := z.1.1.1.2.1
  let time : Slab T →ᵇ E6 := z.1.2
  let clamp : ℝ → Set.Icc (0 : ℝ) T := fun s =>
    ⟨max 0 (min s T), ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩⟩
  have hclamp : Continuous clamp := by
    apply Continuous.subtype_mk
    exact continuous_const.max (continuous_id.min continuous_const)
  have hclampInterior (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
      clamp s = ⟨s, ⟨hs.1.le, hs.2.le⟩⟩ := by
    apply Subtype.ext
    simp [clamp, min_eq_left hs.2.le, max_eq_right hs.1.le]
  let f : ℝ → E3 → E6 := fun t x => timeExtension val x t
  let dtime : ℝ → E3 → ℝ →L[ℝ] E6 := fun t x =>
    ContinuousLinearMap.toSpanSingleton ℝ (time (clamp t, x))
  let dspace : ℝ → E3 → E3 →L[ℝ] E6 := fun t x => grad (clamp t, x)
  have htimeEval : Continuous (fun p : ℝ × E3 => time (clamp p.1, p.2)) := by
    exact time.continuous.comp ((hclamp.comp continuous_fst).prodMk continuous_snd)
  have hgradEval : Continuous (fun p : ℝ × E3 => grad (clamp p.1, p.2)) := by
    exact grad.continuous.comp ((hclamp.comp continuous_fst).prodMk continuous_snd)
  have hdtime : Continuous (Function.uncurry dtime) := by
    change Continuous (fun p : ℝ × E3 =>
      ContinuousLinearMap.toSpanSingleton ℝ (time (clamp p.1, p.2)))
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E6)).continuous.comp htimeEval
  have hdspace : Continuous (Function.uncurry dspace) := by
    exact hgradEval
  have hfclamp : Continuous (fun p : ℝ × E3 => val (clamp p.1, p.2)) := by
    exact val.continuous.comp ((hclamp.comp continuous_fst).prodMk continuous_snd)
  have hopen : IsOpen U := isOpen_Ioo.prod isOpen_univ
  have hmem (t : ℝ) (x : E3) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
      (t, x) ∈ U := by
    exact ⟨ht, Set.mem_univ x⟩
  have hcont : ContinuousOn (Function.uncurry f) U := by
    apply hfclamp.continuousOn.congr
    intro p hp
    rcases p with ⟨t, x⟩
    have ht : t ∈ Set.Ioo (0 : ℝ) T := hp.1
    change timeExtension val x t = val (clamp t, x)
    rw [hclampInterior t ht]
    simp [timeExtension, Set.mem_Icc, ht.1.le, ht.2.le]
  have hderiv (p : ℝ × E3) (hp : p ∈ U) :
      HasFDerivAt (Function.uncurry f)
        ((Function.uncurry dtime p).coprod (Function.uncurry dspace p)) p := by
    rcases p with ⟨t, x⟩
    have ht : t ∈ Set.Ioo (0 : ℝ) T := hp.1
    let ts : Set.Icc (0 : ℝ) T := ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
    have hpartialTime : ∀ᶠ q in 𝓝 (t, x),
        HasFDerivAt (f · q.2) (Function.uncurry dtime q) q.1 := by
      filter_upwards [hopen.mem_nhds (hmem t x ht)] with q hq
      rcases q with ⟨s, y⟩
      have hs : s ∈ Set.Ioo (0 : ℝ) T := hq.1
      let us : Set.Icc (0 : ℝ) T := ⟨s, ⟨hs.1.le, hs.2.le⟩⟩
      have hactual : HasDerivAt (timeExtension val y) (time (us, y)) s := by
        simpa [val, time] using hzTime us hs.1 hs.2 y
      have hclampS : clamp s = us := by
        apply Subtype.ext
        simp [us, clamp, min_eq_left hs.2.le, max_eq_right hs.1.le]
      have hfa : HasFDerivAt (fun r : ℝ => timeExtension val y r)
          (ContinuousLinearMap.toSpanSingleton ℝ (time (clamp s, y))) s := by
        simpa [hclampS] using hactual.hasFDerivAt
      change HasFDerivAt (f · y) (Function.uncurry dtime (s, y)) s
      exact hfa
    have hpartialSpace : ∀ᶠ q in 𝓝 (t, x),
        HasFDerivAt (f q.1 ·) (Function.uncurry dspace q) q.2 := by
      filter_upwards [hopen.mem_nhds (hmem t x ht)] with q hq
      rcases q with ⟨s, y⟩
      have hs : s ∈ Set.Ioo (0 : ℝ) T := hq.1
      let us : Set.Icc (0 : ℝ) T := ⟨s, ⟨hs.1.le, hs.2.le⟩⟩
      have hactual : HasFDerivAt (fun w : E3 => val (us, w)) (grad (us, y)) y := by
        simpa [val, grad] using (hzSpace.1 us).1 y
      have hclampS : clamp s = us := by
        apply Subtype.ext
        simp [us, clamp, min_eq_left hs.2.le, max_eq_right hs.1.le]
      have hEq : (fun w : E3 => f s w) = fun w => val (us, w) := by
        funext w
        simp [f, timeExtension, us, Set.mem_Icc, hs.1.le, hs.2.le]
      have hfa := hactual.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => congrFun hEq w)
      change HasFDerivAt (f s ·) (Function.uncurry dspace (s, y)) y
      simpa [dspace, hclampS] using hfa
    have hstrict : HasStrictFDerivAt (Function.uncurry f)
        ((dtime t x).coprod (dspace t x)) (t, x) := by
      exact hasStrictFDerivAt_uncurry_coprod
        (𝕜 := ℝ) (E₁ := ℝ) (E₂ := E3) (F := E6)
        (f := f) (f₁ := dtime) (f₂ := dspace) hpartialTime hpartialSpace
        (hdtime.continuousAt) (hdspace.continuousAt)
    exact hstrict.hasFDerivAt
  have hdiff : DifferentiableOn ℝ (Function.uncurry f) U := by
    intro p hp
    exact (hderiv p hp).differentiableAt.differentiableWithinAt
  have hderivFormula (p : ℝ × E3) (hp : p ∈ U) :
      fderiv ℝ (Function.uncurry f) p =
        (Function.uncurry dtime p).coprod (Function.uncurry dspace p) :=
    (hderiv p hp).fderiv
  have hderivContinuous : ContinuousOn (fderiv ℝ (Function.uncurry f)) U := by
    apply (hdtime.continuousLinearMapCoprod hdspace).continuousOn.congr
    intro p hp
    simpa using hderivFormula p hp
  have hC1 : ContDiffOn ℝ ((0 : ℕ∞) + 1) (Function.uncurry f) U := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := (0 : ℕ)) hopen).2
    refine ⟨hdiff, ?_, ?_⟩
    · intro hzero
      norm_num at hzero
    · exact contDiffOn_zero.mpr hderivContinuous
  change ContDiffOn ℝ 1 (Function.uncurry f) U
  simpa using hC1
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetJointC1
