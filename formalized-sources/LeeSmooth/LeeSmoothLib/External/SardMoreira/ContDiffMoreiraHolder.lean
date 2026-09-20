import Mathlib
import LeeSmoothLib.External.SardMoreira.ContDiff
import LeeSmoothLib.External.SardMoreira.ContinuousMultilinearMap

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-!
`ContDiffMoreiraHolderAt` was the name used by the source repository before the same
definition was merged into Mathlib as `ContDiffPointwiseHolderAt`.  Keep the source-facing
name as a compatibility abbreviation; all basic closure properties below delegate to Mathlib.
-/
abbrev ContDiffMoreiraHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop :=
  ContDiffPointwiseHolderAt k α f a

theorem ContDiffAt.contDiffMoreiraHolderAt {n : WithTop ℕ∞} {k : ℕ} {f : E → F} {a : E}
    (h : ContDiffAt ℝ n f a) (hk : k < n) (α : I) : ContDiffMoreiraHolderAt k α f a :=
  h.contDiffPointwiseHolderAt hk α

namespace ContDiffMoreiraHolderAt

theorem continuousAt {k : ℕ} {α : I} {f : E → F} {a : E}
    (h : ContDiffMoreiraHolderAt k α f a) : ContinuousAt f a :=
  ContDiffPointwiseHolderAt.continuousAt h

theorem differentiableAt {k : ℕ} {α : I} {f : E → F} {a : E}
    (h : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) : DifferentiableAt ℝ f a :=
  ContDiffPointwiseHolderAt.differentiableAt h hk

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt k 0 f a ↔ ContDiffAt ℝ k f a :=
  ContDiffPointwiseHolderAt.zero_exponent_iff

theorem zero_left_iff {α : I} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt 0 α f a ↔
      ContDiffAt ℝ 0 f a ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
  ContDiffPointwiseHolderAt.zero_order_iff

theorem of_exponent_le {k : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hle : β ≤ α) :
    ContDiffMoreiraHolderAt k β f a :=
  ContDiffPointwiseHolderAt.of_exponent_le hf hle

theorem of_lt {k l : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hlt : l < k) :
    ContDiffMoreiraHolderAt l β f a :=
  ContDiffPointwiseHolderAt.of_order_lt hf hlt

theorem of_toLex_le {k l : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hle : toLex (l, β) ≤ toLex (k, α)) :
    ContDiffMoreiraHolderAt l β f a :=
  ContDiffPointwiseHolderAt.of_toLex_le hf hle

theorem of_le {k l : ℕ} {f : E → F} {a : E} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l ≤ k) :
    ContDiffMoreiraHolderAt l α f a :=
  ContDiffPointwiseHolderAt.of_order_le hf hl

theorem of_contDiffOn_holderWith {f : E → F} {s : Set E} {k : ℕ} {α : I} {a : E} {C : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffMoreiraHolderAt k α f a :=
  ContDiffPointwiseHolderAt.of_contDiffOn_holderOnWith hf hs hd

theorem fst {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.fst a :=
  ContDiffPointwiseHolderAt.fst

theorem snd {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.snd a :=
  ContDiffPointwiseHolderAt.snd

theorem prodMk {k : ℕ} {α : I} {f : E → F} {g : E → G} {a : E}
    (hf : ContDiffMoreiraHolderAt k α f a) (hg : ContDiffMoreiraHolderAt k α g a) :
    ContDiffMoreiraHolderAt k α (fun x ↦ (f x, g x)) a :=
  ContDiffPointwiseHolderAt.prodMk hf hg

theorem comp' {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hd : DifferentiableAt ℝ g (f a) ∨ DifferentiableAt ℝ f a) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  ContDiffPointwiseHolderAt.comp_of_differentiableAt a hg hf hd

theorem comp {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a)
    (hk : k ≠ 0) : ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  ContDiffPointwiseHolderAt.comp a hg hf hk

theorem _root_.ContinuousLinearMap.contDiffMoreiraHolderAt
    (f : E →L[ℝ] F) {a : E} {k : ℕ} {α : I} :
    ContDiffMoreiraHolderAt k α f a :=
  f.contDiffPointwiseHolderAt

theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt
    (f : E ≃L[ℝ] F) {a : E} {k : ℕ} {α : I} :
    ContDiffMoreiraHolderAt k α f a :=
  f.contDiffPointwiseHolderAt

theorem continuousLinearMap_comp {f : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  ContDiffPointwiseHolderAt.continuousLinearMap_comp hf g

@[simp]
theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  g.contDiffPointwiseHolderAt_left_comp

@[simp]
theorem _root_.LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp
    {f : E → F} {a : E} {k : ℕ} {α : I} (g : F ≃ₗᵢ[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  g.contDiffPointwiseHolderAt_left_comp

protected theorem id {k : ℕ} {α : I} {a : E} : ContDiffMoreiraHolderAt k α id a :=
  ContDiffPointwiseHolderAt.id

protected theorem const {k : ℕ} {α : I} {a : E} {b : F} :
    ContDiffMoreiraHolderAt k α (Function.const E b) a :=
  ContDiffPointwiseHolderAt.const

protected theorem fderiv {f : E → F} {a : E} {k l : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + 1 ≤ k) :
    ContDiffMoreiraHolderAt l α (fderiv ℝ f) a :=
  ContDiffPointwiseHolderAt.fderiv hf (Nat.add_one_le_iff.mp hl)

protected theorem iteratedFDeriv {f : E → F} {a : E} {k l m : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + m ≤ k) :
    ContDiffMoreiraHolderAt l α (iteratedFDeriv ℝ m f) a :=
  ContDiffPointwiseHolderAt.iteratedFDeriv hf hl

theorem congr_eventuallyEq {f g : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hfg : f =ᶠ[𝓝 a] g) :
    ContDiffMoreiraHolderAt k α g a :=
  ContDiffPointwiseHolderAt.congr_of_eventuallyEq hf hfg

end ContDiffMoreiraHolderAt

theorem OpenPartialHomeomorph.contDiffMoreiraHolderAt_symm [CompleteSpace E] {k : ℕ} {α : I}
    (f : OpenPartialHomeomorph E F) {a : F} (ha : a ∈ f.target)
    (hf' : (fderiv ℝ f (f.symm a)).IsInvertible)
    (hf : ContDiffMoreiraHolderAt k α f (f.symm a)) :
    ContDiffMoreiraHolderAt k α f.symm a where
  contDiffAt := contDiffAt_symm' f ha hf' hf.contDiffAt
  isBigO := by
    have hrpow : (‖· - a‖) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      (IsBigO.id_rpow_of_le_one α.2.2).comp_tendsto <| tendsto_norm_sub_self_nhdsGE _
    rcases eq_or_ne k 0 with rfl | hk₀
    · calc
        _ =O[𝓝 a] fun x ↦ f.symm x - f.symm a := by
          rw [← isBigO_norm_left]
          simp_rw [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          exact isBigO_refl _ _
        _ =O[𝓝 a] fun x ↦ x - a :=
          (f.hasFDerivAt_symm ha hf'.hasFDerivAt).isBigO_sub
        _ =O[𝓝 a] fun x ↦ ‖x - a‖ := .norm_right (isBigO_refl _ _)
        _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := hrpow
    · have hinv : ∀ᶠ x in 𝓝 (f.symm a), (fderiv ℝ f x).IsInvertible :=
        (hf.contDiffAt.continuousAt_fderiv <| mod_cast hk₀).eventually <|
           ContinuousLinearEquiv.isOpen.mem_nhds hf'
      have hinv' : ∀ᶠ x in 𝓝 a, (fderiv ℝ f (f.symm x)).IsInvertible :=
        f.continuousAt_symm ha |>.eventually hinv
      have hfderiv_isBigO :
          (fun x ↦ fderiv ℝ f.symm x - fderiv ℝ f.symm a) =O[𝓝 a]
            fun x ↦ fderiv ℝ f (f.symm x) - fderiv ℝ f (f.symm a) := by
        refine EventuallyEq.trans_isBigO ?_
          (ContinuousLinearMap.isBigO_inverse_sub_inverse hinv' ?_ ?_ ?_)
        · filter_upwards [f.continuousAt_symm ha hinv, f.open_target.mem_nhds ha] with x hfx hx
          rw [f.fderiv_symm hx hfx, f.fderiv_symm ha hf']
        · refine f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
            |>.norm |>.isBoundedUnder_le |>.mono_le ?_
          filter_upwards [hinv', f.open_target.mem_nhds ha] with x hfx hx
          simp [f.fderiv_symm hx hfx]
        · simp [hinv.self_of_nhds]
        · apply isBoundedUnder_const
      have hsymm_isBigO : (f.symm · - f.symm a) =O[𝓝 a] (· - a) := by
        simpa using f.hasFDerivAt_symm ha hf'.hasFDerivAt |>.isBigO_sub
      have hsymm_rpow_isBigO :
          (‖f.symm · - f.symm a‖ ^ (α : ℝ)) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
        hsymm_isBigO.norm_norm.rpow α.2.1 (by simp [EventuallyLE])
      obtain rfl | hk₁ : k = 1 ∨ 1 < k := by grind
      · calc
          _ =O[𝓝 a] fun x ↦ fderiv ℝ f.symm x - fderiv ℝ f.symm a :=
            .of_norm_left <| by simp [iteratedFDeriv_one_eq, ← map_sub, isBigO_refl]
          _ =O[𝓝 a] fun x ↦ fderiv ℝ f (f.symm x) - fderiv ℝ f (f.symm a) :=
            hfderiv_isBigO
          _ =O[𝓝 a] fun x ↦ ‖f.symm x - f.symm a‖ ^ (α : ℝ) := by
            have h := hf.isBigO.comp_tendsto (f.continuousAt_symm ha) |>.norm_left
            rcases h.bound with ⟨C, hC⟩
            apply IsBigO.of_bound C
            filter_upwards [hC] with x hx
            simpa [Function.comp_def, iteratedFDeriv_one_eq, ← map_sub] using hx
          _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := hsymm_rpow_isBigO
      · calc
          (fun x ↦ iteratedFDeriv ℝ k f.symm x - iteratedFDeriv ℝ k f.symm a)
            =ᶠ[𝓝 a] fun x ↦
              (FormalMultilinearSeries.id ℝ E (f.symm x) k -
                ∑ c ≠ OrderedFinpartition.atomic k,
                  c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm x)
                    (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm x))).compContinuousLinearMap
                      (fun _ ↦ fderiv ℝ f.symm x) -
              (FormalMultilinearSeries.id ℝ E (f.symm a) k -
                ∑ c ≠ OrderedFinpartition.atomic k,
                  c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm a)
                    (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm a))).compContinuousLinearMap
                      (fun _ ↦ fderiv ℝ f.symm a) := by
            rw [← f.symm.symm_map_nhds_eq ha, f.symm_symm, eventuallyEq_map]
            filter_upwards [hf.contDiffAt.eventually (by simp),
              f.open_source.mem_nhds (f.mapsTo_symm ha), hinv]
              with x hx hfx hinv
            simp only [Function.comp_apply]
            rw [f.iteratedFDeriv_symm_eq_rec ha hf.contDiffAt le_rfl (fun _ ↦ hf'),
              f.iteratedFDeriv_symm_eq_rec (f.mapsTo hfx) (by simpa [hfx]) le_rfl (by simp [*])]
          _ = fun x ↦
            -∑ c ≠ OrderedFinpartition.atomic k,
              ((c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm x)
                (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm x))).compContinuousLinearMap
                  (fun _ ↦ fderiv ℝ f.symm x) -
                (c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm a)
                  (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm a))).compContinuousLinearMap
                    (fun _ ↦ fderiv ℝ f.symm a)) := by
            simp only [hk₁, FormalMultilinearSeries.id_apply_of_one_lt, zero_sub, neg_sub_neg,
              Finset.sum_sub_distrib, ContinuousMultilinearMap.compContinuousLinearMap_neg_left,
              ContinuousMultilinearMap.compContinuousLinearMap_sum_left, neg_sub]
          _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := .neg_left <| .sum fun c hc ↦ ?_
        simp only [OrderedFinpartition.compContinuousLinearMap_compAlongOrderedFinpartition_left]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ← c.length_lt_iff] at hc
        apply c.compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
        · exact f.contDiffAt_symm' ha hf' hf.contDiffAt
            |>.continuousAt_iteratedFDeriv (mod_cast hc.le) |>.norm |>.isBoundedUnder_le
        · refine .trans (.norm_right ?_) hrpow
          exact f.contDiffAt_symm' ha hf' hf.contDiffAt
            |>.differentiableAt_iteratedFDeriv (mod_cast hc) |>.isBigO_sub
        · intro m
          refine (ContinuousAt.tendsto <| .norm ?_).isBoundedUnder_le
          simp only [← ContinuousMultilinearMap.compContinuousLinearMapL_apply]
          refine .clm_apply ?_ ?_
          · refine map_continuous
              (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ _ _ _)
              |>.continuousAt.comp ?_
            refine continuousAt_pi.2 fun _ ↦ ?_
            exact f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
          · refine hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast c.partSize_le _) |>.comp ?_
            exact f.continuousAt_symm ha
        · exact fun _ ↦ isBoundedUnder_const
        · intro m
          apply ContinuousMultilinearMap.compContinuousLinearMap_sub_compContinuousLinearMap_isBigO
          · apply isBoundedUnder_const
          · exact (hf.of_le (c.partSize_le m) |>.isBigO |>.comp_tendsto <| f.continuousAt_symm ha)
              |>.trans hsymm_rpow_isBigO
          · intro i
            exact f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
              |>.norm |>.isBoundedUnder_le
          · exact fun _ ↦ isBoundedUnder_const
          · refine fun i ↦ hfderiv_isBigO.trans (.trans (.trans ?_ hsymm_isBigO.norm_right) hrpow)
            exact hf.contDiffAt.fderiv_right (mod_cast hk₁) |>.differentiableAt one_ne_zero
              |>.isBigO_sub |>.comp_tendsto <| f.continuousAt_symm ha
