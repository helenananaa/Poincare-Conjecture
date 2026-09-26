import PoincareConjecture.ParallelImplementation.BarycentricSubdivisionRealization
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricGeometricSubdivision
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open PoincareConjecture.ParallelImplementation.BarycentricSubdivisionRealization
open scoped BigOperators Topology
variable {V : Type*} [Fintype V] [DecidableEq V]
def faceBarycenter (K : FiniteAbstractComplex V) (s : Face K) : V → ℝ :=
  fun v => (s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0
def geometricCell (K : FiniteAbstractComplex V) (c : Finset (Face K)) : Set (V → ℝ) :=
  convexHull ℝ (faceBarycenter K '' (c : Set (Face K)))
/-- Actual finite geometric subdivision data in the ORIGINAL ambient space.
Not merely another unspecified topological homeomorphism. -/
theorem barycentric_geometric_subdivision (K : FiniteAbstractComplex V) :
    (∀ c ∈ (barycentricSubdivision K).faces,
      AffineIndependent ℝ (fun s : c => faceBarycenter K s.val)) ∧
    (∀ c ∈ (barycentricSubdivision K).faces,
      ∀ d ∈ (barycentricSubdivision K).faces,
        geometricCell K c ∩ geometricCell K d = geometricCell K (c ∩ d)) ∧
    (⋃ c ∈ (barycentricSubdivision K).faces, geometricCell K c) = (realization K).space ∧
    (∀ c ∈ (barycentricSubdivision K).faces, ∃ s ∈ K.faces,
      geometricCell K c ⊆ convexHull ℝ (barycentricVertex '' (s : Set V))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let F := Face K
  let B : F → V → ℝ := fun s v =>
    ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0)
  let L : (F → ℝ) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun x => ∑ s : F, x s • B s
      map_add' := by
        intro x y
        simp_rw [Pi.add_apply, add_smul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro a x
        ext v
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        change a * x s * B s v = a * (x s * B s v)
        ring }
  have hL_apply (x : F → ℝ) (v : V) :
      L x v = ∑ s : F, x s * B s v := by
    simp [L, smul_eq_mul]
  have hLvertex (s : F) : L (barycentricVertex (V := F) s) =
      faceBarycenter K s := by
    ext v
    rw [hL_apply]
    change (∑ t : F, (barycentricVertex (V := F) s) t * B t v) = B s v
    simp only [barycentricVertex, Pi.single_apply]
    rw [Finset.sum_eq_single s]
    · simp [B, faceBarycenter]
    · intro t ht hts
      simp [hts]
    · simp
  have hLmap (x : F → ℝ) : L x = fun v => barycentricMap K x v := by
    ext v
    rw [hL_apply]
    simp [B, barycentricMap, faceBarycenter]
    rfl
  let sourceCell := fun c : Finset F =>
    convexHull ℝ (↑(c.image (barycentricVertex (V := F))) : Set (F → ℝ))
  have hvertices (c : Finset F) :
      L '' (↑(c.image (barycentricVertex (V := F))) : Set (F → ℝ)) =
        ↑(faceBarycenter K '' (c : Set F)) := by
    rw [Finset.coe_image, Set.image_image]
    ext s
    simp only [Set.mem_image]
    constructor
    · rintro ⟨t, ht, hts⟩
      subst s
      exact ⟨t, ht, (hLvertex t).symm⟩
    · rintro ⟨t, ht, hts⟩
      exact ⟨t, ht, (hLvertex t).trans hts⟩
  have hcell_image (c : Finset F) : L '' sourceCell c = geometricCell K c := by
    change L '' convexHull ℝ
      (↑(c.image (barycentricVertex (V := F))) : Set (F → ℝ)) = _
    rw [L.image_convexHull, hvertices]
    rfl

  have hsrc_mem (c : Finset F) (hc : c ∈ (barycentricSubdivision K).faces)
      {x : F → ℝ} (hx : x ∈ sourceCell c) :
      x ∈ (realization (barycentricSubdivision K)).space := by
    exact (realization (barycentricSubdivision K)).convexHull_subset_space
      (abstract_face_realizes (barycentricSubdivision K) hc) hx

  rcases barycentric_subdivision_realization_homeomorph K with ⟨e, he⟩
  have hL_injective_on_source {x y : F → ℝ}
      (hx : x ∈ (realization (barycentricSubdivision K)).space)
      (hy : y ∈ (realization (barycentricSubdivision K)).space)
      (hxy : L x = L y) : x = y := by
    let X : StandardRealization (barycentricSubdivision K) := ⟨x, hx⟩
    let Y : StandardRealization (barycentricSubdivision K) := ⟨y, hy⟩
    have hX : e X = e Y := by
      apply Subtype.ext
      funext v
      rw [he X v, he Y v]
      calc
        barycentricMap K x v = L x v := (congrFun (hLmap x) v).symm
        _ = L y v := congrFun hxy v
        _ = barycentricMap K y v := congrFun (hLmap y) v
    have hXY := e.injective hX
    exact congrArg Subtype.val hXY

  have hsum_extend (c : Finset F) (a : c → ℝ) (g : F → ℝ) :
      (∑ s : F, (if hs : s ∈ c then a ⟨s, hs⟩ else 0) * g s) =
        ∑ i : c, a i * g i.val := by
    let p : F → Prop := fun s => s ∈ c
    let term : F → ℝ := fun s => (if hs : p s then a ⟨s, hs⟩ else 0) * g s
    have hcompl : (∑ s : {s : F // ¬ p s}, term s.val) = 0 := by
      apply Fintype.sum_eq_zero
      intro s
      simp [term, p, s.property]
    have hdecomp := (Fintype.sum_subtype_add_sum_subtype p term).symm
    have hinst : Subtype.fintype p = (inferInstance : Fintype c) :=
      Subsingleton.elim _ _
    rw [hinst] at hdecomp
    have hsubtype :
        (∑ s : {s : F // p s}, term s.val) = ∑ i : c, a i * g i.val := by
      apply Fintype.sum_equiv (Equiv.refl c)
      intro i
      simp [term, p]
    calc
      (∑ s : F, term s) =
          (∑ s : {s : F // p s}, term s.val) +
            (∑ s : {s : F // ¬ p s}, term s.val) := hdecomp
      _ = ∑ i : c, a i * g i.val := by rw [hcompl, add_zero, hsubtype]

  have hweighted (c : Finset F) (hc : c ∈ (barycentricSubdivision K).faces)
      (a : c → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : (∑ i, a i) = 1) :
      ∃ x : StandardRealization (barycentricSubdivision K),
        (∀ v, barycentricMap K x.val v =
          ∑ i : c, a i * faceBarycenter K i.val v) ∧
        (∀ i : c, x.val i.val = a i) := by
    let f : F → ℝ := fun s => if hs : s ∈ c then a ⟨s, hs⟩ else 0
    have hf0 : ∀ s, 0 ≤ f s := by
      intro s
      by_cases hs : s ∈ c
      · simpa [f, hs] using ha0 ⟨s, hs⟩
      · simp [f, hs]
    have hsumf : (∑ s : F, f s) = 1 := by
      have h := hsum_extend c a (fun _ : F => 1)
      simpa [f] using h.trans (by simpa using ha1)
    let S := Finset.univ.filter fun s : F => 0 < f s
    have hSne : S.Nonempty := by
      have hpos : 0 < f := (Fintype.sum_pos_iff_of_nonneg hf0).mp
        (by rw [hsumf]; norm_num)
      obtain ⟨s, hs⟩ := (Pi.lt_def.mp hpos).2
      exact ⟨s, by simpa [S, Pi.zero_apply] using hs⟩
    have hSsub : S ⊆ c := by
      intro s hs
      have hspos := (Finset.mem_filter.mp hs).2
      by_contra hsc
      simp [f, hsc] at hspos
    have hSface : S ∈ (barycentricSubdivision K).faces :=
      ((barycentricSubdivision K).isRelLowerSet_faces hc).2 hSsub hSne
    have hmem : f ∈ (realization (barycentricSubdivision K)).space :=
      (FiniteRealizationCoordinates.mem_realization_iff_coordinates
        (barycentricSubdivision K) f).2 ⟨hf0, hsumf, hSface⟩
    refine ⟨⟨f, hmem⟩, ?_, ?_⟩
    · intro v
      rw [← hsum_extend c a (fun s => faceBarycenter K s v)]
      rfl
    · intro i
      simp [f, i.property]

  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ
      (fun i : c => faceBarycenter K i.val)]
    intro a b ha hb hab
    have hcomb : (∑ i : c, a i • faceBarycenter K i.val) =
        ∑ i : c, b i • faceBarycenter K i.val := by
      rw [← Finset.univ.affineCombination_eq_linear_combination _ _ ha,
        ← Finset.univ.affineCombination_eq_linear_combination _ _ hb]
      exact hab
    have hsumdiff : (∑ i : c, (a i - b i)) = 0 := by
      rw [Finset.sum_sub_distrib, ha, hb]
      ring
    have hzero : (∑ i : c, (a i - b i) • faceBarycenter K i.val) = 0 := by
      calc
        _ = (∑ i : c, a i • faceBarycenter K i.val) -
            (∑ i : c, b i • faceBarycenter K i.val) := by
          calc
            _ = ∑ i : c, (a i • faceBarycenter K i.val -
                b i • faceBarycenter K i.val) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact sub_smul _ _ _
            _ = _ := by
              change (∑ i : c, (a i • faceBarycenter K i.val -
                b i • faceBarycenter K i.val)) =
                  (∑ i : c, a i • faceBarycenter K i.val) -
                    (∑ i : c, b i • faceBarycenter K i.val)
              rw [Finset.sum_sub_distrib]
        _ = 0 := by rw [hcomb]; simp
    let p : c → ℝ := fun i => max (a i - b i) 0
    let n : c → ℝ := fun i => max (b i - a i) 0
    have hdiff (i : c) : a i - b i = p i - n i := by
      dsimp [p, n]
      by_cases h : 0 ≤ a i - b i
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
        linarith
    have hp0 : ∀ i, 0 ≤ p i := fun i => le_max_right _ _
    have hn0 : ∀ i, 0 ≤ n i := fun i => le_max_right _ _
    have hsumPN : (∑ i : c, p i) = ∑ i : c, n i := by
      have h : (∑ i : c, p i) - ∑ i : c, n i = 0 := by
        calc
          (∑ i : c, p i) - ∑ i : c, n i =
              ∑ i : c, (p i - n i) := by
                symm
                rw [Finset.sum_sub_distrib]
          _ = ∑ i : c, (a i - b i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (hdiff i).symm
          _ = 0 := hsumdiff
      linarith
    have hneq_support : ∀ i : c, a i ≠ b i →
        0 < ∑ i : c, p i := by
      intro i hi
      have hδ : a i - b i ≠ 0 := sub_ne_zero.mpr hi
      rcases lt_or_gt_of_ne hδ with hneg | hpos
      · have hnpos : 0 < n i := by
          dsimp [n]
          rw [max_eq_left (by linarith)]
          linarith
        have hsumN : 0 < ∑ j : c, n j :=
          (Fintype.sum_pos_iff_of_nonneg hn0).mpr
            (Pi.lt_def.mpr ⟨hn0, ⟨i, hnpos⟩⟩)
        rw [hsumPN]
        exact hsumN
      · have hppos : 0 < p i := by
          dsimp [p]
          rw [max_eq_left (le_of_lt hpos)]
          exact hpos
        exact (Fintype.sum_pos_iff_of_nonneg hp0).mpr
          (Pi.lt_def.mpr ⟨hp0, ⟨i, hppos⟩⟩)
    by_contra hne
    have hneq : ∃ i : c, a i ≠ b i := by
      by_contra hnone
      push Not at hnone
      apply hne
      funext i
      exact hnone i
    obtain ⟨i, hi⟩ := hneq
    let t : ℝ := ∑ i : c, p i
    have ht : 0 < t := by simpa [t] using hneq_support i hi
    let ap : c → ℝ := fun i => p i / t
    let an : c → ℝ := fun i => n i / t
    have hap0 : ∀ i, 0 ≤ ap i := fun i => div_nonneg (hp0 i) ht.le
    have han0 : ∀ i, 0 ≤ an i := fun i => div_nonneg (hn0 i) ht.le
    have hsum_div (g : c → ℝ) :
        (∑ i ∈ c.attach, g i / t) = (∑ i ∈ c.attach, g i) / t := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
    have hap1 : (∑ i : c, ap i) = 1 := by
      change (∑ i ∈ c.attach, p i / t) = 1
      rw [hsum_div]
      have hsumpt : (∑ i ∈ c.attach, p i) = t := by rfl
      rw [hsumpt]
      exact div_self (ne_of_gt ht)
    have han1 : (∑ i : c, an i) = 1 := by
      change (∑ i ∈ c.attach, n i / t) = 1
      rw [hsum_div]
      have hsumN : (∑ i ∈ c.attach, n i) = ∑ i ∈ c.attach, p i := by
        simpa using hsumPN.symm
      rw [hsumN]
      have hsumpt : (∑ i ∈ c.attach, p i) = t := by rfl
      rw [hsumpt]
      exact div_self (ne_of_gt ht)
    have hzero' := hzero
    simp_rw [hdiff, sub_smul] at hzero'
    have hcombPN : (∑ i : c, p i • faceBarycenter K i.val) =
        ∑ i : c, n i • faceBarycenter K i.val := by
      exact sub_eq_zero.mp (by simpa only [Finset.sum_sub_distrib] using hzero')
    have hnorm : (∑ i : c, ap i • faceBarycenter K i.val) =
        ∑ i : c, an i • faceBarycenter K i.val := by
      ext v
      have hcoord := congrFun hcombPN v
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hcoord' : (∑ i : c, p i * faceBarycenter K i.val v) =
          ∑ i : c, n i * faceBarycenter K i.val v := by
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hcoord
      rw [show (∑ i : c, p i / t * faceBarycenter K i.val v) =
          (∑ i : c, p i * faceBarycenter K i.val v) / t by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            ring]
      rw [show (∑ i : c, n i / t * faceBarycenter K i.val v) =
          (∑ i : c, n i * faceBarycenter K i.val v) / t by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            ring]
      rw [hcoord']
    obtain ⟨xp, hxp, hxpcoord⟩ := hweighted c hc ap hap0 hap1
    obtain ⟨xn, hxn, hxncoord⟩ := hweighted c hc an han0 han1
    have hmapEq : (fun v => barycentricMap K xp.val v) =
        fun v => barycentricMap K xn.val v := by
      ext v
      rw [hxp v, hxn v]
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hnorm v
    have hxy : xp.val = xn.val := by
      apply hL_injective_on_source
      · exact xp.property
      · exact xn.property
      · rw [hLmap, hLmap]
        exact hmapEq
    have hpn : ∀ i : c, p i = n i := by
      intro j
      have hval := congrFun hxy j.val
      have hratio : p j / t = n j / t := by
        simpa [hxpcoord j, hxncoord j, ap, an] using hval
      have htne : t ≠ 0 := ne_of_gt ht
      have := congrArg (fun z : ℝ => z * t) hratio
      field_simp [htne] at this
      linarith
    have hδzero : ∀ i : c, a i - b i = 0 := by
      intro j
      rw [hdiff j, hpn j]
      ring
    have heq : a i = b i := sub_eq_zero.mp (hδzero i)
    exact hne (funext fun j => by
      have := hδzero j
      linarith)
  · intro c hc d hd
    calc
      geometricCell K c ∩ geometricCell K d =
          (L '' sourceCell c) ∩ (L '' sourceCell d) := by
            rw [hcell_image, hcell_image]
      _ = L '' (sourceCell c ∩ sourceCell d) := by
        ext x
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, ⟨z, hz, hEq⟩⟩
          have hy' := hsrc_mem c hc hy
          have hz' := hsrc_mem d hd hz
          have hyz : y = z := hL_injective_on_source hy' hz' hEq.symm
          exact ⟨y, ⟨hy, hyz ▸ hz⟩, rfl⟩
        · rintro ⟨y, ⟨hy, hz⟩, rfl⟩
          exact ⟨⟨y, hy, rfl⟩, ⟨y, hz, rfl⟩⟩
      _ = L '' sourceCell (c ∩ d) := by
        rw [PoincareConjecture.ParallelImplementation.FinitePLRealization.convexHull_abstract_face_intersection
          (barycentricSubdivision K) hc hd]
      _ = geometricCell K (c ∩ d) := hcell_image _
  · ext x
    constructor
    · intro hx
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨c, hc, hx⟩
      rw [← hcell_image c] at hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy' := hsrc_mem c hc hy
      have hrange := (barycentric_map_range_and_continuous K).1 ⟨y, hy'⟩
      have hLval : L y = fun v => barycentricMap K y v := hLmap y
      rw [hLval]
      exact hrange
    · intro hx
      obtain ⟨z, hzy⟩ :=
        e.surjective (⟨x, hx⟩ : StandardRealization K)
      have hspace := z.property
      rcases Geometry.SimplicialComplex.mem_space_iff.mp hspace with ⟨t, ht, hzt⟩
      obtain ⟨c, hc, rfl⟩ := realized_face_originates (barycentricSubdivision K) ht
      have hxcell : z.val ∈ sourceCell c := by
        change z.val ∈ convexHull ℝ (↑(c.image (barycentricVertex (V := F))) : Set (F → ℝ))
        exact hzt
      have hxy : L z.val = x := by
        have hcoord : (e z).val = x := by
          simpa using congrArg Subtype.val hzy
        ext v
        calc
          L z.val v = barycentricMap K z.val v := congrFun (hLmap z.val) v
          _ = (e z).val v := (he z v).symm
          _ = x v := congrFun hcoord v
      apply Set.mem_iUnion.mpr
      refine ⟨c, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨hc, ?_⟩
      rw [← hcell_image c]
      exact ⟨z.val, hxcell, hxy⟩
  · intro c hc
    obtain ⟨s₀, hs₀c, hs₀max⟩ := Finset.exists_max_image c
      (fun s : F => s.val.card)
      ((barycentricSubdivision K).isRelLowerSet_faces hc).1
    have hsub : ∀ t ∈ c, t.val ⊆ s₀.val := by
      intro t ht
      rcases hc.2 t ht s₀ hs₀c with hts | hst
      · exact hts
      · have hcard : t.val.card ≤ s₀.val.card := hs₀max t ht
        have heq : s₀.val = t.val := Finset.eq_of_subset_of_card_le hst hcard
        exact heq.symm ▸ Finset.Subset.rfl
    have hs₀ : s₀.val ∈ K.faces := s₀.property
    have hs₀ne : s₀.val.Nonempty := (K.isRelLowerSet_faces hs₀).1
    obtain ⟨v₀, hv₀⟩ := hs₀ne
    have hcenter (t : F) (ht : t.val ⊆ s₀.val) :
        faceBarycenter K t ∈
          convexHull ℝ (↑(s₀.val.image barycentricVertex) : Set (V → ℝ)) := by
      let w : V → ℝ := fun v => B t v
      let z : V → V → ℝ := fun v =>
        if hv : v ∈ t.val then barycentricVertex v else barycentricVertex v₀
      have hw0 : ∀ v, 0 ≤ w v := by
        intro v
        dsimp [w, B]
        split_ifs <;> positivity
      have hw1 : (∑ v : V, w v) = 1 := by
        simp [w, B, Finset.sum_ite, (K.isRelLowerSet_faces t.property).1,
          Finset.card_ne_zero.mpr (K.isRelLowerSet_faces t.property).1,
          mul_comm, mul_left_comm, mul_assoc]
      have hz : ∀ v, z v ∈
          (↑(s₀.val.image barycentricVertex) : Set (V → ℝ)) := by
        intro v
        apply Finset.mem_coe.mpr
        rw [Finset.mem_image]
        by_cases hv : v ∈ t.val
        · exact ⟨v, ht hv, by simp [z, hv]⟩
        · exact ⟨v₀, hv₀, by simp [z, hv]⟩
      have hterm (v : V) : w v • z v = w v • barycentricVertex v := by
        by_cases hv : v ∈ t.val
        · simp [z, hv]
        · have hwv : w v = 0 := by simp [w, B, hv]
          simp [z, hv, hwv]
      have hcomb : (∑ v : V, w v • z v) = faceBarycenter K t := by
        ext u
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ v : V, w v * z v u) =
              ∑ v : V, w v * barycentricVertex v u := by
                apply Finset.sum_congr rfl
                intro v hv
                simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (hterm v) u
          _ = faceBarycenter K t u := by
            simp [w, B, faceBarycenter, barycentricVertex, Pi.single_apply]
      apply mem_convexHull_of_exists_fintype
        (w := w) (z := z)
      · exact hw0
      · exact hw1
      · exact hz
      · exact hcomb
    have himage : faceBarycenter K '' (c : Set F) ⊆
        convexHull ℝ (↑(s₀.val.image barycentricVertex) : Set (V → ℝ)) := by
      rintro y ⟨t, ht, rfl⟩
      exact hcenter t (hsub t ht)
    refine ⟨s₀.val, hs₀, ?_⟩
    simpa [geometricCell, Finset.coe_image] using
      (convexHull_mono (𝕜 := ℝ) himage)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricGeometricSubdivision
