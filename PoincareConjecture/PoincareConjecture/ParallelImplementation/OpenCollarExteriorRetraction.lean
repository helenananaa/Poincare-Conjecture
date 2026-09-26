import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OpenCollarExteriorRetraction
open Set
/-- Retract the complement of the central slice onto the exterior of the
smaller open tube. Construct the map from the actual open embedding. -/
theorem exists_collar_exterior_retraction
    {Y M : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace M] [T2Space M]
    (f : Y × Set.Ioo (-2 : ℝ) 2 → M) (hf : Topology.IsOpenEmbedding f) :
    let S : Set M := Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩))
    let O : Set M := f '' {q : Y × Set.Ioo (-2 : ℝ) 2 | |(q.2 : ℝ)| < 1}
    ∃ r : M → M,
      ContinuousOn r Sᶜ ∧ MapsTo r Sᶜ Oᶜ ∧ EqOn r id Oᶜ ∧
      ∀ (y : Y) (t : Set.Ioo (-2 : ℝ) 2), (t : ℝ) ≠ 0 → |(t : ℝ)| ≤ 1 →
        r (f (y,t)) = if 0 < (t : ℝ) then f (y, ⟨1, by norm_num⟩)
          else f (y, ⟨-1, by norm_num⟩) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S : Set M := Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩))
  let O : Set M := f '' {q : Y × Set.Ioo (-2 : ℝ) 2 | |(q.2 : ℝ)| < 1}
  change ∃ r : M → M,
      ContinuousOn r Sᶜ ∧ MapsTo r Sᶜ Oᶜ ∧ EqOn r id Oᶜ ∧
      ∀ (y : Y) (t : Set.Ioo (-2 : ℝ) 2), (t : ℝ) ≠ 0 → |(t : ℝ)| ≤ 1 →
        r (f (y,t)) = if 0 < (t : ℝ) then f (y, ⟨1, by norm_num⟩)
          else f (y, ⟨-1, by norm_num⟩)
  by_cases hY : Nonempty Y
  · letI : Nonempty Y := hY
    let A := Y × Set.Ioo (-2 : ℝ) 2
    haveI : Nonempty A := ⟨(Classical.choice hY, ⟨0, by norm_num⟩)⟩
    let e := hf.toOpenPartialHomeomorph f
    let c : ℝ → ℝ := fun t => if t < 0 then min t (-1) else max t 1
    have hc_mem (t : Set.Ioo (-2 : ℝ) 2) : c t ∈ Set.Ioo (-2 : ℝ) 2 := by
      have ht := t.property
      by_cases hn : (t : ℝ) < 0
      · change (if (t : ℝ) < 0 then min (t : ℝ) (-1) else max (t : ℝ) 1) ∈ _
        rw [if_pos hn]
        constructor
        · exact lt_min ht.1 (by norm_num)
        · exact lt_of_le_of_lt (min_le_left _ _) ht.2
      · change (if (t : ℝ) < 0 then min (t : ℝ) (-1) else max (t : ℝ) 1) ∈ _
        rw [if_neg hn]
        constructor
        · exact lt_of_lt_of_le (by norm_num : (-2 : ℝ) < 1) (le_max_right _ _)
        · exact max_lt ht.2 (by norm_num)
    let ρ : A → A := fun q => (q.1, ⟨c q.2, hc_mem q.2⟩)
    have hc_cont : ContinuousOn c {t : ℝ | t ≠ 0} := by
      have hn : ContinuousOn c (Set.Iio (0 : ℝ)) := by
        apply (continuous_id.min continuous_const).continuousOn.congr
        intro t ht
        change t < 0 at ht
        change c t = min t (-1)
        simp [c, ht]
      have hp : ContinuousOn c (Set.Ioi (0 : ℝ)) := by
        apply (continuous_id.max continuous_const).continuousOn.congr
        intro t ht
        change 0 < t at ht
        change c t = max t 1
        simp [c, not_lt.mpr (le_of_lt ht)]
      have hcover : {t : ℝ | t ≠ 0} ⊆ Set.Iio (0 : ℝ) ∪ Set.Ioi (0 : ℝ) := by
        intro t ht
        rcases lt_or_gt_of_ne ht with h | h
        · exact Or.inl h
        · exact Or.inr h
      exact (hn.union_of_isOpen hp isOpen_Iio isOpen_Ioi).mono hcover
    have hc_abs_ge (t : ℝ) : 1 ≤ |c t| := by
      by_cases hn : t < 0
      · have hle : min t (-1 : ℝ) ≤ -1 := min_le_right _ _
        have hnon : min t (-1 : ℝ) ≤ 0 := le_trans hle (by norm_num)
        change 1 ≤ |if t < 0 then min t (-1) else max t 1|
        rw [if_pos hn, abs_of_nonpos hnon]
        linarith
      · have hle : (1 : ℝ) ≤ max t 1 := le_max_right _ _
        have hnon : 0 ≤ max t 1 := le_trans (by norm_num) hle
        change 1 ≤ |if t < 0 then min t (-1) else max t 1|
        rw [if_neg hn, abs_of_nonneg hnon]
        exact hle
    have hc_eq_id (t : ℝ) (ht : 1 ≤ |t|) : c t = t := by
      by_cases hn : t < 0
      · have hle : t ≤ -1 := by
          rw [abs_of_neg hn] at ht
          linarith
        simp [c, hn, min_eq_left hle]
      · have hnon : 0 ≤ t := le_of_not_gt hn
        have hge : 1 ≤ t := by
          rw [abs_of_nonneg hnon] at ht
          exact ht
        simp [c, hn, max_eq_left hge]
    have hc_pos (t : ℝ) (ht : 0 < t) (ha : |t| ≤ 1) : c t = 1 := by
      have htle : t ≤ 1 := by
        rw [abs_of_nonneg (le_of_lt ht)] at ha
        exact ha
      simp [c, not_lt_of_ge (le_of_lt ht), max_eq_right htle]
    have hc_neg (t : ℝ) (ht : t < 0) (ha : |t| ≤ 1) : c t = -1 := by
      have htge : -1 ≤ t := by
        rw [abs_of_neg ht] at ha
        linarith
      simp [c, ht, min_eq_right htge]
    let ρDomain : Set A := {q | (q.2 : ℝ) ≠ 0}
    have hρ_cont : ContinuousOn ρ ρDomain := by
      rw [continuousOn_iff_continuous_restrict]
      change Continuous (fun q : ρDomain => ρ q.1)
      have hpair : Continuous (fun q : ρDomain => (q.val : Y × Set.Ioo (-2 : ℝ) 2)) :=
        continuous_subtype_val
      have hinterval : Continuous (fun q : ρDomain => ((q.val : Y × Set.Ioo (-2 : ℝ) 2).2)) :=
        continuous_snd.comp hpair
      have hreal : Continuous (fun q : ρDomain => (((q.val : Y × Set.Ioo (-2 : ℝ) 2).2 : Set.Ioo (-2 : ℝ) 2) : ℝ)) :=
        continuous_subtype_val.comp hinterval
      have hcoord : Continuous (fun q : ρDomain =>
          (⟨(((q.val : Y × Set.Ioo (-2 : ℝ) 2).2 : Set.Ioo (-2 : ℝ) 2) : ℝ), q.property⟩ : {t : ℝ // t ≠ 0})) :=
        Continuous.subtype_mk hreal (fun q => q.property)
      have hc_restrict : Continuous (fun t : {t : ℝ // t ≠ 0} => c t.1) := by
        exact hc_cont.restrict
      have hsecond : Continuous (fun q : ρDomain =>
          (⟨c (((q.val : Y × Set.Ioo (-2 : ℝ) 2).2 : Set.Ioo (-2 : ℝ) 2)),
            hc_mem ((q.val : Y × Set.Ioo (-2 : ℝ) 2).2)⟩ : Set.Ioo (-2 : ℝ) 2)) :=
        Continuous.subtype_mk (hc_restrict.comp hcoord) (fun q => hc_mem ((q.val : A).2))
      exact Continuous.prodMk (continuous_fst.comp continuous_subtype_val) hsecond
    let F : A → M := fun q => f (ρ q)
    have hF : ContinuousOn F ρDomain := hf.continuous.comp_continuousOn hρ_cont
    let B : Set A := {q | |(q.2 : ℝ)| < (7 / 4 : ℝ)}
    let U : Set M := f '' B
    have hBopen : IsOpen B := by
      have hcoord : Continuous (fun q : A => |(q.2 : ℝ)|) :=
        continuous_abs.comp (continuous_subtype_val.comp continuous_snd)
      exact isOpen_lt hcoord continuous_const
    have hUopen : IsOpen U := hf.isOpenMap B hBopen
    have hUrange : U ⊆ Set.range f := by
      rintro x ⟨q, hq, rfl⟩
      exact ⟨q, rfl⟩
    have hOsubU : O ⊆ U := by
      rintro x ⟨q, hq, rfl⟩
      refine ⟨q, ?_, rfl⟩
      have hq' : |(q.2 : ℝ)| < 1 := hq
      exact lt_trans hq' (by norm_num : (1 : ℝ) < 7 / 4)
    let C : Set A := {q | |(q.2 : ℝ)| ≤ (3 / 2 : ℝ)}
    let K : Set M := f '' C
    let P := Y × Set.Icc (-3 / 2 : ℝ) (3 / 2 : ℝ)
    let φ : P → A := fun p =>
      (p.1, ⟨(p.2 : ℝ), by
        have hp := p.2.property
        change (-3 / 2 : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 3 / 2 at hp
        constructor <;> linarith⟩)
    let G : P → M := fun p => f (φ p)
    have hφ_cont : Continuous φ := by
      have hsecond : Continuous (fun p : P =>
          (⟨(p.2 : ℝ), by
            have hp := p.2.property
            change (-3 / 2 : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 3 / 2 at hp
            constructor <;> linarith⟩ : Set.Ioo (-2 : ℝ) 2)) := by
        apply Continuous.subtype_mk (continuous_subtype_val.comp continuous_snd)
      exact Continuous.prodMk continuous_fst hsecond
    have hG_cont : Continuous G := hf.continuous.comp hφ_cont
    have hKC : K = Set.range G := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        have hbound : |(q.2 : ℝ)| ≤ 3 / 2 := hq
        have habs := abs_le.mp hbound
        have hIcc : (-3 / 2 : ℝ) ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ 3 / 2 := by
          constructor <;> norm_num at habs ⊢ <;> linarith
        refine ⟨(q.1, ⟨(q.2 : ℝ), hIcc⟩), ?_⟩
        simp [G, φ]
      · rintro ⟨p, rfl⟩
        refine ⟨φ p, ?_, rfl⟩
        dsimp [C, φ]
        have hp := p.2.property
        change (-3 / 2 : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 3 / 2 at hp
        change |(p.2 : ℝ)| ≤ (3 / 2 : ℝ)
        rw [abs_le]
        constructor <;> linarith
    have hKcompact : IsCompact K := by
      rw [hKC]
      exact isCompact_range hG_cont
    have hKclosed : IsClosed K := hKcompact.isClosed
    have hKsubU : K ⊆ U := by
      rintro x ⟨q, hq, rfl⟩
      refine ⟨q, ?_, rfl⟩
      have hbound : |(q.2 : ℝ)| ≤ 3 / 2 := hq
      exact lt_of_le_of_lt hbound (by norm_num : (3 / 2 : ℝ) < 7 / 4)
    have hOsub : O ⊆ U := hOsubU
    have htarget : Set.range f = e.target := by
      rw [← e.image_source_eq_target]
      simp [e]
    have hUtarget : U ⊆ e.target := by
      intro x hx
      rw [← htarget]
      exact hUrange hx
    let l : M → M := fun x => F (e.symm x)
    let r : M → M := fun x => if x ∈ U then l x else x
    have hVmap (x : M) (hx : x ∈ U ∩ Sᶜ) : e.symm x ∈ ρDomain := by
      change (↑((e.symm x : Y × Set.Ioo (-2 : ℝ) 2).2) : ℝ) ≠ (0 : ℝ)
      intro hz
      have hright : f (e.symm x) = x := by
        apply e.right_inv
        exact hUtarget hx.1
      apply hx.2
      refine ⟨(e.symm x).1, ?_⟩
      have hq : e.symm x = ((e.symm x).1, ⟨0, by norm_num⟩) := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact hz
      calc
        f ((e.symm x).1, ⟨0, by norm_num⟩) = f (e.symm x) := congrArg f hq.symm
        _ = x := hright
    have hInv : ContinuousOn (fun x => e.symm x) (U ∩ Sᶜ) := by
      apply e.continuousOn_invFun.mono
      exact fun x hx => hUtarget hx.1
    have hl : ContinuousOn l (U ∩ Sᶜ) := by
      exact hF.comp hInv (fun x hx => hVmap x hx)
    have hl_notO (x : M) (hxU : x ∈ U) (hxS : x ∈ Sᶜ) : l x ∉ O := by
      let q := e.symm x
      have hright : f q = x := by
        apply e.right_inv
        exact hUtarget hxU
      have hq0 : (q.2 : ℝ) ≠ 0 := hVmap x ⟨hxU, hxS⟩
      intro ho
      have hmem : f (ρ q) ∈ O := by
        simpa [l, F, q] using ho
      rcases hmem with ⟨q', hq', heq⟩
      have hfeq : f (ρ q) = f q' := by simpa using heq.symm
      have hp : ρ q = q' := hf.injective hfeq
      have hb : 1 ≤ |(q'.2 : ℝ)| := by
        rw [← congrArg (fun z : A => |(z.2 : ℝ)|) hp]
        exact hc_abs_ge (q.2 : ℝ)
      change |(q'.2 : ℝ)| < 1 at hq'
      linarith
    have hl_eq_id (x : M) (hxU : x ∈ U) (hxK : x ∉ K) : l x = x := by
      rcases hxU with ⟨q, hq, rfl⟩
      have hlarge : 1 ≤ |(q.2 : ℝ)| := by
        have hn : ¬ |(q.2 : ℝ)| ≤ 3 / 2 := fun h => hxK ⟨q, h, rfl⟩
        have hgt : (3 / 2 : ℝ) < |(q.2 : ℝ)| := lt_of_not_ge hn
        linarith
      have heq : e.symm (f q) = q := by
        apply e.left_inv
        simp [e]
      have hc := hc_eq_id (q.2 : ℝ) hlarge
      have hρq : ρ q = q := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          exact hc
      simp [l, F, heq, hρq]
    have hridK : EqOn r id Kᶜ := by
      intro x hxK
      by_cases hxU : x ∈ U
      · simp [r, hxU, hl_eq_id x hxU hxK]
      · simp [r, hxU]
    have hrcont : ContinuousOn r Sᶜ := by
      intro x hxS
      by_cases hxU : x ∈ U
      · have hloc := hl x ⟨hxU, hxS⟩
        have hloc' : ContinuousWithinAt l (Sᶜ ∩ U) x := by
          simpa [inter_comm] using hloc
        have hcont : ContinuousWithinAt r (Sᶜ ∩ U) x := by
          apply hloc'.congr
          · intro y hy
            simp [r, hy.2]
          · simp [r, hxU]
        exact (continuousWithinAt_inter (hUopen.mem_nhds hxU)).mp hcont
      · have hxK : x ∈ Kᶜ := by
          change x ∉ K
          intro hx
          exact hxU (hKsubU hx)
        have hcont : ContinuousWithinAt r (Sᶜ ∩ Kᶜ) x := by
          apply (continuousWithinAt_id.mono inter_subset_left).congr
          · intro y hy
            exact hridK (x := y) hy.2
          · exact hridK (x := x) hxK
        exact (continuousWithinAt_inter (hKclosed.isOpen_compl.mem_nhds hxK)).mp hcont
    refine ⟨r, hrcont, ?_, ?_, ?_⟩
    · intro x hxS
      rw [Set.mem_compl_iff]
      by_cases hxU : x ∈ U
      · have hnot : l x ∉ O := hl_notO x hxU hxS
        simpa [r, hxU] using hnot
      · intro hxO
        have hx : x ∈ O := by simpa [r, hxU] using hxO
        exact hxU (hOsub hx)
    · intro x hxO
      by_cases hxU : x ∈ U
      · let q := e.symm x
        have hright : f q = x := by
          apply e.right_inv
          exact hUtarget hxU
        have habs : 1 ≤ |(q.2 : ℝ)| := by
          by_contra hn
          have hlt : |(q.2 : ℝ)| < 1 := lt_of_not_ge hn
          apply hxO
          refine ⟨q, hlt, ?_⟩
          exact hright
        have heq : e.symm (f q) = q := by
          apply e.left_inv
          simp [e]
        have hc := hc_eq_id (q.2 : ℝ) habs
        have hρq : ρ q = q := by
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            exact hc
        have hlx : l x = x := by
          change f (ρ q) = x
          rw [hρq]
          exact hright
        simp [r, hxU, hlx]
      · simp [r, hxU]
    · intro y t ht ha
      have hxU : f (y,t) ∈ U := by
        refine ⟨(y,t), ?_, rfl⟩
        dsimp [B]
        exact lt_of_le_of_lt ha (by norm_num : (1 : ℝ) < 7 / 4)
      have hxS : f (y,t) ∈ Sᶜ := by
        change f (y,t) ∉ S
        intro hs
        rcases hs with ⟨z, hz⟩
        have hp : (z, ⟨0, by norm_num⟩) = (y,t) := hf.injective (by simpa using hz)
        have hv := congrArg (fun q : Y × Set.Ioo (-2 : ℝ) 2 => (q.2 : ℝ)) hp
        simp at hv
        exact ht hv.symm
      have hright : f (e.symm (f (y,t))) = f (y,t) := by
        apply e.right_inv
        exact hUtarget hxU
      have heq : e.symm (f (y,t)) = (y,t) := by
        apply e.left_inv
        simp [e]
      by_cases hp : 0 < (t : ℝ)
      · have hc := hc_pos (t : ℝ) hp ha
        simp [r, hxU, l, F, heq, ρ, c, hc, hp]
      · have hn : (t : ℝ) < 0 := lt_of_le_of_ne (le_of_not_gt hp) ht
        have hc := hc_neg (t : ℝ) hn ha
        simp [r, hxU, l, F, heq, ρ, c, hc, hp]
  · letI : IsEmpty Y := not_nonempty_iff.mp hY
    have hS : S = ∅ := by
      change Set.range (fun y : Y => f (y, ⟨0, by norm_num⟩)) = ∅
      exact Set.range_eq_empty_iff.mpr (not_nonempty_iff.mp hY)
    have hO : O = ∅ := by
      change f '' {q : Y × Set.Ioo (-2 : ℝ) 2 | |(q.2 : ℝ)| < 1} = ∅
      rw [Set.image_eq_empty]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact isEmptyElim x.1
    refine ⟨id, ?_, ?_, ?_, ?_⟩
    · simpa [hS] using (continuous_id.continuousOn : ContinuousOn id (Set.univ : Set M))
    · intro x hx
      simp [hO]
    · intro x hx
      rfl
    · intro y
      exact isEmptyElim y
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OpenCollarExteriorRetraction
