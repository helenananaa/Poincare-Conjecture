import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SimplexExposedSubfaces
/-- Every actual vertex subface of a simplex is exposed in that simplex.
This includes empty and full faces and lower-dimensional ambient spans. -/
theorem simplex_vertex_subface_isExposed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hind : AffineIndependent ℝ (fun v : s => (v : E)))
    (t : Finset E) (ht : t ⊆ s) :
    IsExposed ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set E)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases htne : t.Nonempty
  · let sSet : Set E := (s : Set E)
    have hindSet : AffineIndependent ℝ (fun v : sSet => (v : E)) := by
      simpa [sSet] using hind
    obtain ⟨u, hsu, hindU, hspan⟩ :=
      exists_subset_affineIndependent_affineSpan_eq_top hindSet
    let b : AffineBasis u ℝ E :=
      ⟨Subtype.val, hindU, by simpa using hspan⟩
    have hufin : u.Finite := finite_set_of_fin_dim_affineIndependent ℝ hindU
    letI : Fintype u := hufin.fintype
    letI : DecidableEq u := Classical.decEq u
    let embS : s → u := fun v => ⟨v, hsu v.property⟩
    let embT : t → u := fun v => ⟨v, hsu (ht v.property)⟩
    let F : E →ᵃ[ℝ] ℝ :=
      { toFun := fun x => ∑ i : t, b.coord (embT i) x
        linear := ∑ i : t, (b.coord (embT i)).linear
        map_vadd' := by
          intro p v
          calc
            (∑ i : t, b.coord (embT i) (v +ᵥ p)) =
                ∑ i : t, ((b.coord (embT i)).linear v + b.coord (embT i) p) := by
              apply Finset.sum_congr rfl
              intro i hi
              simpa [vadd_eq_add] using (b.coord (embT i)).map_vadd p v
            _ = (∑ i : t, (b.coord (embT i)).linear v) +
                ∑ i : t, b.coord (embT i) p := by rw [Finset.sum_add_distrib]
            _ = (∑ i : t, (b.coord (embT i)).linear) v +
                ∑ i : t, b.coord (embT i) p := by simp }
    have hcoord (i : t) (v : s) :
        b.coord (embT i) (v : E) = if (i : E) = v then 1 else 0 := by
      change b.coord (embT i) (b (embS v)) = _
      rw [b.coord_apply]
      simp [embT, embS]
    have hsumIndicator (v : s) :
        (∑ i : t, if (i : E) = v then (1 : ℝ) else 0) =
          if (v : E) ∈ (t : Set E) then 1 else 0 := by
      by_cases hv : (v : E) ∈ (t : Set E)
      · let i₀ : t := ⟨v, hv⟩
        have heq : ∀ i : t, ((i : E) = v) ↔ i = i₀ := by
          intro i
          constructor
          · intro hi
            exact Subtype.ext hi
          · intro hi
            exact congrArg (fun q : t => (q : E)) hi
        simp [heq, i₀, hv]
      · have hneq : ∀ i : t, (i : E) ≠ v := by
          intro i hi
          exact hv (hi ▸ i.property)
        simp [hneq, hv]
    have hFvertex (v : s) :
        F (v : E) = if (v : E) ∈ (t : Set E) then 1 else 0 := by
      change (∑ i : t, b.coord (embT i) (v : E)) = _
      rw [show (∑ i : t, b.coord (embT i) (v : E)) =
          ∑ i : t, if (i : E) = v then (1 : ℝ) else 0 by
            apply Finset.sum_congr rfl
            intro i hi
            exact hcoord i v]
      exact hsumIndicator v
    have hrangeS : Set.range (fun v : s => (v : E)) = (s : Set E) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact v.property
      · intro hx
        exact ⟨⟨x, by simpa using hx⟩, rfl⟩
    have hrangeT : Set.range (fun v : t => (v : E)) = (t : Set E) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact v.property
      · intro hx
        exact ⟨⟨x, by simpa using hx⟩, rfl⟩
    have hrepS (x : E) (hx : x ∈ convexHull ℝ (s : Set E)) :
        ∃ (q : Finset s) (w : s → ℝ), (∀ i ∈ q, 0 ≤ w i) ∧ q.sum w = 1 ∧
          q.affineCombination ℝ (fun i : s => (i : E)) w = x := by
      have hxR : x ∈ convexHull ℝ (Set.range fun v : s => (v : E)) := by
        rw [hrangeS]
        exact hx
      rw [convexHull_range_eq_exists_affineCombination] at hxR
      exact hxR
    have hrepT (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) :
        ∃ (q : Finset t) (w : t → ℝ), (∀ i ∈ q, 0 ≤ w i) ∧ q.sum w = 1 ∧
          q.affineCombination ℝ (fun i : t => (i : E)) w = x := by
      have hxR : x ∈ convexHull ℝ (Set.range fun v : t => (v : E)) := by
        rw [hrangeT]
        exact hx
      rw [convexHull_range_eq_exists_affineCombination] at hxR
      exact hxR
    have hFcombo (q : Finset s) (w : s → ℝ) (hw : q.sum w = 1) :
        F (q.affineCombination ℝ (fun i : s => (i : E)) w) =
          q.sum (fun i => w i * F (i : E)) := by
      rw [q.map_affineCombination (fun i : s => (i : E)) w hw F,
        q.affineCombination_eq_linear_combination _ _ hw]
      simp only [smul_eq_mul, Function.comp_apply]
    have hFbound (x : E) (hx : x ∈ convexHull ℝ (s : Set E)) : F x ≤ 1 := by
      obtain ⟨q, w, hw0, hw1, hcomb⟩ := hrepS x hx
      rw [← hcomb, hFcombo q w hw1]
      calc
        q.sum (fun i => w i * F (i : E)) ≤ q.sum (fun i => w i * 1) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (hw0 i hi)
          by_cases hit : (i : E) ∈ (t : Set E)
          · simp [hFvertex, hit]
          · simp [hFvertex, hit]
        _ = 1 := by simp [hw1]
    have hFoneOnT (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) : F x = 1 := by
      obtain ⟨q, w, hw0, hw1, hcomb⟩ := hrepT x hx
      have hmap := q.map_affineCombination (fun i : t => (i : E)) w hw1 F
      rw [hcomb] at hmap
      rw [hmap, q.affineCombination_eq_linear_combination _ _ hw1]
      calc
        q.sum (fun i => w i * F (i : E)) = q.sum (fun i => w i * 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiS : (i : E) ∈ (s : Set E) := ht i.property
          let j : s := ⟨i, hiS⟩
          have hj := hFvertex j
          have hji : (j : E) = (i : E) := rfl
          rw [hji] at hj
          have hji' : F (i : E) = 1 := by simpa [i.property] using hj
          rw [hji']
        _ = 1 := by simp [hw1]
    have hface (x : E) (hxS : x ∈ convexHull ℝ (s : Set E))
        (hFx : F x = 1) : x ∈ convexHull ℝ (t : Set E) := by
      obtain ⟨q, w, hw0, hw1, hcomb⟩ := hrepS x hxS
      have hFsum := hFcombo q w hw1
      rw [hcomb] at hFsum
      have hdef : q.sum (fun i => w i *
          (1 - if (i : E) ∈ (t : Set E) then (1 : ℝ) else 0)) = 0 := by
        calc
          q.sum (fun i => w i *
              (1 - if (i : E) ∈ (t : Set E) then (1 : ℝ) else 0)) =
              q.sum (fun i => w i - w i *
                (if (i : E) ∈ (t : Set E) then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = q.sum w - q.sum (fun i => w i *
                (if (i : E) ∈ (t : Set E) then (1 : ℝ) else 0)) :=
              by rw [Finset.sum_sub_distrib]
          _ = 1 - 1 := by
            rw [hw1]
            have hvalue : q.sum (fun i => w i *
                (if (i : E) ∈ (t : Set E) then (1 : ℝ) else 0)) = 1 := by
              calc
                q.sum (fun i => w i *
                    (if (i : E) ∈ (t : Set E) then (1 : ℝ) else 0)) =
                    q.sum (fun i => w i * F (i : E)) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  by_cases hit : (i : E) ∈ (t : Set E)
                  · simp [hFvertex, hit]
                  · simp [hFvertex, hit]
                _ = 1 := by rw [← hFsum, hFx]
            rw [hvalue]
          _ = 0 := by norm_num
      have hdef_nonneg : ∀ i ∈ q, 0 ≤ w i *
          (1 - if (i : E) ∈ (t : Set E) then (1 : ℝ) else 0) := by
        intro i hi
        apply mul_nonneg (hw0 i hi)
        by_cases hit : (i : E) ∈ (t : Set E) <;> simp [hit]
      have hwzero : ∀ i ∈ q, (i : E) ∉ (t : Set E) → w i = 0 := by
        intro i hi hit
        have hz := (Finset.sum_eq_zero_iff_of_nonneg hdef_nonneg).mp hdef i hi
        simpa [hit] using hz
      obtain ⟨v₀, hv₀⟩ := htne
      let z : s → E := fun i => if hi : (i : E) ∈ (t : Set E) then (i : E) else v₀
      let wfull : s → ℝ := fun i => if i ∈ q then w i else 0
      have hwfull0 : ∀ i : s, 0 ≤ wfull i := by
        intro i
        by_cases hi : i ∈ q
        · simpa [wfull, hi] using hw0 i hi
        · simp [wfull, hi]
      have hwfull1 : ∑ i : s, wfull i = 1 := by
        calc
          ∑ i : s, wfull i = q.sum w := by
            change (∑ i : s, if i ∈ q then w i else 0) = q.sum w
            rw [Finset.sum_ite_mem_eq]
          _ = 1 := hw1
      have hz : ∀ i : s, z i ∈ (t : Set E) := by
        intro i
        by_cases hi : (i : E) ∈ (t : Set E)
        · simp only [z, dif_pos hi]
          exact hi
        · simp only [z, dif_neg hi]
          exact hv₀
      have hpoint : ∑ i : s, wfull i • z i = x := by
        calc
          ∑ i : s, wfull i • z i = q.sum (fun i => w i • z i) := by
            calc
              ∑ i : s, wfull i • z i =
                  ∑ i : s, if i ∈ q then w i • z i else 0 := by
                apply Finset.sum_congr rfl
                intro i hi
                simp [wfull, ite_smul]
              _ = q.sum (fun i => w i • z i) := by rw [Finset.sum_ite_mem_eq]
          _ = q.sum (fun i => w i • (i : E)) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hit : (i : E) ∈ (t : Set E)
            · change w i • (if h : (i : E) ∈ (t : Set E) then (i : E) else v₀) = _
              rw [dif_pos hit]
            · have hwi := hwzero i hi hit
              change w i • (if h : (i : E) ∈ (t : Set E) then (i : E) else v₀) = _
              rw [dif_neg hit, hwi]
              simp
          _ = x := by
            rw [← hcomb, q.affineCombination_eq_linear_combination _ _ hw1]
      exact mem_convexHull_of_exists_fintype wfull z hwfull0 hwfull1 hz hpoint
    have hdecomp (x : E) : F x = F.linear x + F 0 := by
      simpa using congrFun (AffineMap.decomp F) x
    intro _
    refine ⟨(F.linear).toContinuousLinearMap, ?_⟩
    ext x
    constructor
    · intro hx
      refine ⟨convexHull_mono ht hx, ?_⟩
      intro y hy
      have hybound := hFbound y hy
      have hxone := hFoneOnT x hx
      change F.linear y ≤ F.linear x
      linarith [hdecomp y, hdecomp x]
    · rintro ⟨hxS, hmax⟩
      have hFxlower : 1 ≤ F x := by
        obtain ⟨v₀, hv₀⟩ := htne
        have hv₀T : (v₀ : E) ∈ convexHull ℝ (t : Set E) :=
          subset_convexHull ℝ _ hv₀
        have hv₀S : (v₀ : E) ∈ convexHull ℝ (s : Set E) :=
          convexHull_mono ht hv₀T
        have hmax₀ := hmax (v₀ : E) hv₀S
        have hone₀ := hFoneOnT (v₀ : E) hv₀T
        change F.linear (v₀ : E) ≤ F.linear x at hmax₀
        linarith [hdecomp (v₀ : E), hdecomp x]
      have hFx : F x = 1 := le_antisymm (hFbound x hxS) hFxlower
      exact hface x hxS hFx
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htne
    have htempty : (t : Set E) = (∅ : Set E) := by simp [ht0]
    rw [htempty, convexHull_empty]
    exact isExposed_empty
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SimplexExposedSubfaces
