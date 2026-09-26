import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SimplexFiniteHalfspaces
/-- An actual simplex has a finite ambient linear-inequality description,
including the affine-span constraints for lower-dimensional simplices. -/
theorem simplex_eq_finite_halfspaces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hs : s.Nonempty)
    (hind : AffineIndependent ℝ (fun v : s => (v : E))) :
    ∃ n : ℕ, ∃ l : Fin n → E →ₗ[ℝ] ℝ, ∃ a : Fin n → ℝ,
      ∀ x : E, x ∈ convexHull ℝ (s : Set E) ↔ ∀ i : Fin n, l i x ≤ a i :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let sSet : Set E := (s : Set E)
  have hindSet : AffineIndependent ℝ (fun v : sSet => (v : E)) := by
    simpa [sSet] using hind
  obtain ⟨t, hst, hindT, hspan⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hindSet
  let b : AffineBasis t ℝ E :=
    ⟨Subtype.val, hindT, by simpa using hspan⟩
  have htfin : t.Finite := finite_set_of_fin_dim_affineIndependent ℝ hindT
  letI : Fintype t := htfin.fintype
  let d := {q : t // (q : E) ∉ (s : Set E)}
  letI : Fintype d := Fintype.ofFinite d
  letI : DecidableEq d := Classical.decEq d
  let emb : s → t := fun v => ⟨v, hst (by simp)⟩
  let I := s ⊕ (d ⊕ d)
  letI : Fintype I := inferInstance
  let n : ℕ := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let L : I → E →ₗ[ℝ] ℝ := fun q =>
    match q with
    | Sum.inl i => -((b.coord (emb i)).linear)
    | Sum.inr (Sum.inl j) => (b.coord j.1).linear
    | Sum.inr (Sum.inr j) => -((b.coord j.1).linear)
  let A : I → ℝ := fun q =>
    match q with
    | Sum.inl i => b.coord (emb i) 0
    | Sum.inr (Sum.inl j) => -b.coord j.1 0
    | Sum.inr (Sum.inr j) => b.coord j.1 0
  have hdecomp (f : E →ᵃ[ℝ] ℝ) (x : E) : f x = f.linear x + f 0 := by
    simpa using congrFun (AffineMap.decomp f) x
  have hineq (x : E) :
      (∀ q : I, L q x ≤ A q) ↔
        (∀ i : s, 0 ≤ b.coord (emb i) x) ∧
        (∀ j : d, b.coord j.1 x = 0) := by
    constructor
    · intro h
      constructor
      · intro i
        have hi := h (Sum.inl i)
        change -((b.coord (emb i)).linear) x ≤ b.coord (emb i) 0 at hi
        linarith [hdecomp (b.coord (emb i)) x]
      · intro j
        have h₁ := h (Sum.inr (Sum.inl j))
        have h₂ := h (Sum.inr (Sum.inr j))
        change (b.coord j.1).linear x ≤ -b.coord j.1 0 at h₁
        change -((b.coord j.1).linear) x ≤ b.coord j.1 0 at h₂
        linarith [hdecomp (b.coord j.1) x]
    · rintro ⟨hS, hD⟩ q
      cases q with
      | inl i =>
          change -((b.coord (emb i)).linear) x ≤ b.coord (emb i) 0
          linarith [hS i, hdecomp (b.coord (emb i)) x]
      | inr q =>
          cases q with
          | inl j =>
              change (b.coord j.1).linear x ≤ -b.coord j.1 0
              linarith [hD j, hdecomp (b.coord j.1) x]
          | inr j =>
              change -((b.coord j.1).linear) x ≤ b.coord j.1 0
              linarith [hD j, hdecomp (b.coord j.1) x]
  have hvertex (q : t) (v : s) :
      b.coord q (v : E) = if q = emb v then 1 else 0 := by
    change b.coord q (b (emb v)) = _
    exact b.coord_apply q (emb v)
  have hrange : Set.range (fun v : s => (v : E)) = (s : Set E) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hx
      exact ⟨⟨x, by simpa using hx⟩, rfl⟩
  have hmem (x : E) :
      x ∈ convexHull ℝ (s : Set E) ↔
        (∀ i : s, 0 ≤ b.coord (emb i) x) ∧
        (∀ j : d, b.coord j.1 x = 0) := by
    constructor
    · intro hx
      have hxR : x ∈ convexHull ℝ (Set.range fun v : s => (v : E)) := by
        rw [hrange]
        exact hx
      rw [convexHull_range_eq_exists_affineCombination] at hxR
      rcases hxR with ⟨u, w, hw0, hw1, hcomb⟩
      constructor
      · intro i
        have hmap : b.coord (emb i) x =
            u.affineCombination ℝ (fun v : s => b.coord (emb i) (v : E)) w := by
          rw [← hcomb]
          exact u.map_affineCombination (fun v : s => (v : E)) w hw1 (b.coord (emb i))
        rw [hmap, u.affineCombination_eq_linear_combination _ _ hw1]
        apply Finset.sum_nonneg
        intro v hv
        apply mul_nonneg (hw0 v hv)
        rw [hvertex]
        split_ifs <;> norm_num
      · intro j
        have hmap : b.coord j.1 x =
            u.affineCombination ℝ (fun v : s => b.coord j.1 (v : E)) w := by
          rw [← hcomb]
          exact u.map_affineCombination (fun v : s => (v : E)) w hw1 (b.coord j.1)
        have hzero : ∀ v : s, b.coord j.1 (v : E) = 0 := by
          intro v
          rw [hvertex]
          have hne : j.1 ≠ emb v := by
            intro heq
            apply j.2
            have heq' : (j.1 : E) = (emb v : E) :=
              congrArg (fun z : t => (z : E)) heq
            rw [heq']
            change (v : E) ∈ (s : Set E)
            simp
          simp [hne]
        rw [hmap, u.affineCombination_eq_linear_combination _ _ hw1]
        apply Finset.sum_eq_zero
        intro v hv
        simp [hzero v]
    · rintro ⟨hS, hD⟩
      let w : t → ℝ := fun q => b.coord q x
      let v₀ : E := Classical.choose hs
      have hv₀ : (v₀ : E) ∈ (s : Set E) := by
        simpa [v₀] using Classical.choose_spec hs
      let z : t → E := fun q =>
        if hq : (q : E) ∈ (s : Set E) then (q : E) else v₀
      have hw0 : ∀ q : t, 0 ≤ w q := by
        intro q
        by_cases hq : (q : E) ∈ (s : Set E)
        · let i : s := ⟨q, by simpa using hq⟩
          have heq : emb i = q := by
            apply Subtype.ext
            rfl
          simpa [w, heq] using hS i
        · have hq0 : b.coord q x = 0 := hD ⟨q, hq⟩
          simp [w, hq0]
      have hw1 : ∑ q : t, w q = 1 := by
        simp [w]
      have hz : ∀ q : t, z q ∈ (s : Set E) := by
        intro q
        by_cases hq : (q : E) ∈ (s : Set E)
        · simp only [z, dif_pos hq]
          exact hq
        · simp only [z, dif_neg hq]
          exact hv₀
      have hsum : ∑ q : t, w q • z q = x := by
        calc
          ∑ q : t, w q • z q = ∑ q : t, b.coord q x • (q : E) := by
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hmem : (q : E) ∈ (s : Set E)
            · rw [show z q = (q : E) by
                dsimp [z]
                exact dif_pos hmem]
            · have hq0 : b.coord q x = 0 := hD ⟨q, hmem⟩
              change w q • z q = b.coord q x • (q : E)
              rw [show z q = v₀ by
                dsimp [z]
                exact dif_neg hmem]
              simp [w, hq0]
          _ = x := by
            change (∑ q : t, b.coord q x • b q) = x
            exact b.linear_combination_coord_eq_self x
      exact mem_convexHull_of_exists_fintype w z hw0 hw1 hz hsum
  have hfin (x : E) :
      (∀ i : Fin n, L (e.symm i) x ≤ A (e.symm i)) ↔
        (∀ q : I, L q x ≤ A q) := by
    constructor
    · intro h q
      simpa using h (e q)
    · intro h i
      simpa using h (e.symm i)
  refine ⟨n, fun i => L (e.symm i), fun i => A (e.symm i), ?_⟩
  intro x
  rw [hmem x]
  exact (hineq x).symm.trans (hfin x).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SimplexFiniteHalfspaces
