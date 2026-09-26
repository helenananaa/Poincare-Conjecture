import PoincareConjecture.ParallelImplementation.SmoothPicardOperator
import PoincareConjecture.ParallelImplementation.SmoothContractionFixedPoint
import DoCarmoLib.Riemannian.Geodesic.FlowDependence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CenteredSmoothPicardSolution
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
/-- Smooth initial-value dependence in the path Banach space, with a genuine
ordinary time derivative around an interior initial time. -/
theorem exists_centered_smooth_solution
    {T a : ℝ} (hT : 0 < T) (ha : a ∈ Set.Ioo (0 : ℝ) T)
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (K : ℝ≥0) (hsmall : 2 * T * (K : ℝ) < 1)
    (hlip : ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzWith K (fun x : E => f (t, x))) :
    ∃ Φ : E → C(Set.Icc (0 : ℝ) T, E),
      ContDiff ℝ ∞ Φ ∧
      (∀ x : E, Φ x ⟨a, le_of_lt ha.1, le_of_lt ha.2⟩ = x) ∧
      (∀ (x : E) (t : Set.Icc (0 : ℝ) T),
        Φ x t = x + ∫ s in a..(t : ℝ),
          f (s, Φ x (Set.projIcc 0 T hT.le s))) ∧
      (∀ (x : E) (t : ℝ), t ∈ Set.Ioo (0 : ℝ) T →
        HasDerivAt (fun s : ℝ => Φ x (Set.projIcc 0 T hT.le s))
          (f (t, Φ x (Set.projIcc 0 T hT.le t))) t) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S : Set ℝ := Set.Icc (0 : ℝ) T
  letI : CompactSpace S := isCompact_iff_compactSpace.mp (by
    simpa [S] using (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) T)))
  let X := C(S, E)
  let pa : S := ⟨a, ha.1.le, ha.2.le⟩
  let J : X → X := fun u =>
    PoincareConjecture.ParallelImplementation.SmoothPicardOperator.picardOperator
      hT.le f hf.continuous (0, u)
  let init : E →L[ℝ] X := ContinuousLinearMap.const ℝ S
  let eva : X →L[ℝ] E := ContinuousMap.evalCLM ℝ pa
  let F : E × X → X := fun q => init q.1 + J q.2 - init (eva (J q.2))
  let g : X → ℝ → E := fun u s =>
    f (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState u
      (Set.projIcc 0 T hT.le s))

  have hg (u : X) : Continuous (g u) := by
    apply hf.continuous.comp
    exact (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState u).continuous.comp
      continuous_projIcc

  have hJapply (u : X) (t : S) :
      J u t = ∫ s in (0 : ℝ)..(t : ℝ), g u s := by
    change (ContinuousMap.const S (0 : E) +
      Riemannian.FlowDependence.intervalPrimitive hT.le
        (PoincareConjecture.ParallelImplementation.SmoothPathSuperposition.superposition
          f hf.continuous
          (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState u))) t = _
    rw [ContinuousMap.add_apply, ContinuousMap.const_apply, zero_add,
      Riemannian.FlowDependence.intervalPrimitive_apply]
    rfl

  have hJpoint (u v : X) (t : S) :
      ‖(J u - J v) t‖ ≤ T * (K : ℝ) * ‖u - v‖ := by
    rw [ContinuousMap.sub_apply, hJapply u t, hJapply v t,
      ← intervalIntegral.integral_sub
        ((hg u).intervalIntegrable (μ := MeasureTheory.volume) 0 (t : ℝ))
        ((hg v).intervalIntegrable (μ := MeasureTheory.volume) 0 (t : ℝ))]
    let y := Set.projIcc 0 T hT.le
    have hbound (s : ℝ) : ‖g u s - g v s‖ ≤ (K : ℝ) * ‖u - v‖ := by
      let z : S := y s
      have hl := (hlip (z : ℝ) z.property).dist_le_mul (u z) (v z)
      have hl' : ‖f (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState u z) -
          f (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState v z)‖ ≤
          (K : ℝ) * ‖u z - v z‖ := by
        simpa [dist_eq_norm,
          PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState] using hl
      calc
        ‖g u s - g v s‖ =
            ‖f (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState u z) -
              f (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState v z)‖ := by
                rfl
        _ ≤ (K : ℝ) * ‖u z - v z‖ := hl'
        _ ≤ (K : ℝ) * ‖u - v‖ := by
          change (K : ℝ) * ‖(u - v) z‖ ≤ (K : ℝ) * ‖u - v‖
          exact mul_le_mul_of_nonneg_left ((u - v).norm_coe_le_norm z)
            (NNReal.coe_nonneg K)
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    calc
      ‖∫ s in (0 : ℝ)..(t : ℝ), g u s - g v s‖ ≤
          ((K : ℝ) * ‖u - v‖) * |(t : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hbound s
      _ = ((K : ℝ) * ‖u - v‖) * (t : ℝ) := by simp [abs_of_nonneg ht0]
      _ ≤ ((K : ℝ) * ‖u - v‖) * T :=
        mul_le_mul_of_nonneg_left t.property.2 (mul_nonneg (NNReal.coe_nonneg K) (norm_nonneg _))
      _ = T * (K : ℝ) * ‖u - v‖ := by ring

  have hJnorm (u v : X) : ‖J u - J v‖ ≤ T * (K : ℝ) * ‖u - v‖ := by
    apply (ContinuousMap.norm_le (f := J u - J v)
      (C := T * (K : ℝ) * ‖u - v‖) (by positivity)).2
    intro t
    exact hJpoint u v t

  let L : ℝ≥0 := ⟨2 * T * (K : ℝ), by positivity⟩
  have hL : (L : ℝ) < 1 := by
    change 2 * T * (K : ℝ) < 1
    exact hsmall

  have hFdiff (x : E) (u v : X) :
      F (x, u) - F (x, v) =
        (J u - J v) - init (eva (J u - J v)) := by
    ext t
    change (x + J u t - J u pa) - (x + J v t - J v pa) =
      (J u t - J v t) - (J u pa - J v pa)
    abel

  have hcenterBound (x : E) (u v : X) :
      ‖F (x, u) - F (x, v)‖ ≤ 2 * ‖J u - J v‖ := by
    apply (ContinuousMap.norm_le (f := F (x, u) - F (x, v))
      (C := 2 * ‖J u - J v‖) (by positivity)).2
    intro t
    rw [hFdiff]
    change ‖(J u - J v) t - (J u - J v) pa‖ ≤ 2 * ‖J u - J v‖
    calc
      ‖(J u - J v) t - (J u - J v) pa‖ ≤
          ‖(J u - J v) t‖ + ‖(J u - J v) pa‖ := norm_sub_le _ _
      _ ≤ ‖J u - J v‖ + ‖J u - J v‖ :=
        add_le_add ((J u - J v).norm_coe_le_norm t) ((J u - J v).norm_coe_le_norm pa)
      _ = 2 * ‖J u - J v‖ := by ring

  have hcontract : ∀ x : E, ContractingWith L (fun u : X => F (x, u)) := by
    intro x
    refine ⟨hL, LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    rw [dist_eq_norm]
    calc
      ‖F (x, u) - F (x, v)‖ ≤ 2 * ‖J u - J v‖ := hcenterBound x u v
      _ ≤ 2 * (T * (K : ℝ) * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (hJnorm u v) (by norm_num)
      _ = (L : ℝ) * dist u v := by
        rw [dist_eq_norm]
        change 2 * (T * (K : ℝ) * ‖u - v‖) =
          (2 * T * (K : ℝ)) * ‖u - v‖
        ring

  have hF : ContDiff ℝ ∞ F := by
    have hJ : ContDiff ℝ ∞ J := by
      exact (PoincareConjecture.ParallelImplementation.SmoothPicardOperator.contDiff_picardOperator
        hT.le f hf).comp (contDiff_const.prodMk contDiff_id)
    have hpath : ContDiff ℝ ∞ (fun q : E × X => J q.2) := by
      exact hJ.comp (ContinuousLinearMap.snd ℝ E X).contDiff
    have hinit : ContDiff ℝ ∞ (fun q : E × X => init q.1) := by
      exact init.contDiff.comp (ContinuousLinearMap.fst ℝ E X).contDiff
    have heval : ContDiff ℝ ∞ (fun q : E × X => eva (J q.2)) :=
      eva.contDiff.comp hpath
    have hcenter : ContDiff ℝ ∞ (fun q : E × X => init (eva (J q.2))) :=
      init.contDiff.comp heval
    exact hinit.add hpath |>.sub hcenter

  let Φ : E → X := fun x =>
    ContractingWith.fixedPoint (fun u : X => F (x, u)) (hcontract x)
  have hΦ : ContDiff ℝ ∞ Φ := by
    exact PoincareConjecture.ParallelImplementation.SmoothContractionFixedPoint.contDiff_fixedPoint
      F L hF hcontract

  have hcenterIntegral (u : X) (t : S) :
      J u t - J u pa = ∫ s in a..(t : ℝ), g u s := by
    rw [hJapply u t, hJapply u pa]
    have hsub := intervalIntegral.integral_interval_sub_left
      ((hg u).intervalIntegrable (μ := MeasureTheory.volume) 0 (t : ℝ))
      ((hg u).intervalIntegrable (μ := MeasureTheory.volume) 0 (pa : ℝ))
    simpa [pa] using hsub

  have hfixed (x : E) : F (x, Φ x) = Φ x :=
    ContractingWith.fixedPoint_isFixedPt (hcontract x)

  have hidentity (x : E) (t : S) :
      Φ x t = x + ∫ s in a..(t : ℝ), g (Φ x) s := by
    have hp := congrArg (fun w : X => w t) (hfixed x).symm
    have hp' : Φ x t = x + (J (Φ x) t - J (Φ x) pa) := by
      calc
        Φ x t = (F (x, Φ x)) t := hp
        _ = x + (J (Φ x) t - J (Φ x) pa) := by
          change (init x + J (Φ x) - init (eva (J (Φ x)))) t = _
          change x + J (Φ x) t - J (Φ x) pa = _
          abel
    rw [hcenterIntegral (Φ x) t] at hp'
    exact hp'

  have hrawIntegral (u : X) (t : S) :
      (∫ s in a..(t : ℝ), g u s) =
        ∫ s in a..(t : ℝ), f (s, u (Set.projIcc 0 T hT.le s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsS : s ∈ S := Set.uIcc_subset_Icc
      (show a ∈ Set.Icc (0 : ℝ) T from ⟨ha.1.le, ha.2.le⟩) t.property hs
    have hclamp := Set.projIcc_of_mem hT.le hsS
    change g u s = f (s, u (Set.projIcc 0 T hT.le s))
    dsimp [g, PoincareConjecture.ParallelImplementation.SmoothPicardOperator.timeState]
    rw [hclamp]

  refine ⟨Φ, hΦ, ?_, ?_, ?_⟩
  · intro x
    have h := hidentity x pa
    simpa [pa] using h
  · intro x t
    rw [hidentity x t, hrawIntegral]
  · intro x t ht
    let tS : S := ⟨t, ht.1.le, ht.2.le⟩
    have hderIntegral : HasDerivAt
        (fun s : ℝ => x + ∫ r in a..s, g (Φ x) r) (g (Φ x) t) t := by
      have hder := intervalIntegral.integral_hasDerivAt_right
        ((hg (Φ x)).intervalIntegrable a t)
        ((hg (Φ x)).aestronglyMeasurable.stronglyMeasurableAtFilter)
        ((hg (Φ x)).continuousAt)
      simpa using hder.const_add x
    have heq : (fun s : ℝ => Φ x (Set.projIcc 0 T hT.le s)) =ᶠ[𝓝 t]
        (fun s : ℝ => x + ∫ r in a..s, g (Φ x) r) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hsS : s ∈ S := ⟨hs.1.le, hs.2.le⟩
      have hclamp := Set.projIcc_of_mem hT.le hsS
      have hpoint := hidentity x (Set.projIcc 0 T hT.le s)
      simpa [hclamp] using hpoint
    have hder := hderIntegral.congr_of_eventuallyEq heq
    have hgt : g (Φ x) t = f (t, Φ x (Set.projIcc 0 T hT.le t)) := by
      have hclamp := Set.projIcc_of_mem hT.le ⟨ht.1.le, ht.2.le⟩
      change f ((Set.projIcc 0 T hT.le t : ℝ), Φ x (Set.projIcc 0 T hT.le t)) = _
      rw [hclamp]
    exact hder.congr_deriv hgt
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CenteredSmoothPicardSolution
