import PoincareConjecture.ParallelImplementation.FiniteRealizationCoordinates
import PoincareConjecture.ParallelImplementation.BarycentricChainInjectivity
import PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse
import PoincareConjecture.ParallelImplementation.FinitePLRealization
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricSubdivisionRealization
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators Topology
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev Face (K : FiniteAbstractComplex V) := {s : Finset V // s ∈ K.faces}
noncomputable instance faceFintype (K : FiniteAbstractComplex V) : Fintype (Face K) :=
  Fintype.ofFinite (Face K)
/-- Faces of the subdivision are nonempty inclusion chains of nonempty original faces. -/
def barycentricSubdivision (K : FiniteAbstractComplex V) : FiniteAbstractComplex (Face K) where
  faces := {s | s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s, a.val ⊆ b.val ∨ b.val ⊆ a.val}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    refine ⟨ht, ?_⟩
    intro a ha b hb
    exact hs.2 a (hts ha) b (hts hb)
  singleton_mem := by
    intro a
    refine ⟨Finset.singleton_nonempty a, ?_⟩
    intro b hb c hc
    have hb' : b = a := Finset.mem_singleton.mp hb
    have hc' : c = a := Finset.mem_singleton.mp hc
    subst b
    subst c
    exact Or.inl (Finset.Subset.refl _)
abbrev StandardRealization (K : FiniteAbstractComplex V) :=
  {x : V → ℝ // x ∈ (realization K).space}
/-- Linear barycenter map on ambient coordinate spaces; the target theorem proves its restriction
is the genuine subdivision homeomorphism, not an unspecified topological equivalence. -/
def barycentricMap (K : FiniteAbstractComplex V) (x : Face K → ℝ) (v : V) : ℝ :=
  ∑ s : Face K, x s * ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0)
theorem barycentric_map_range_and_continuous (K : FiniteAbstractComplex V) :
    (∀ x : StandardRealization (barycentricSubdivision K),
      (fun v => barycentricMap K x.val v) ∈ (realization K).space) ∧
    Continuous (fun x : StandardRealization (barycentricSubdivision K) =>
      fun v => barycentricMap K x.val v) :=

by
  classical
  let bary : Face K → V → ℝ :=
    fun s v => ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0)
  have map_eq (x : Face K → ℝ) (v : V) :
      barycentricMap K x v = ∑ s : Face K, x s * bary s v := by
    simp [barycentricMap, bary]
  have hsum_bary (s : Face K) : (∑ v : V, bary s v) = 1 := by
    have hsne : s.val.Nonempty := (K.isRelLowerSet_faces s.property).1
    simp [bary, Finset.sum_ite, hsne, Finset.card_ne_zero.mpr hsne,
      mul_comm, mul_left_comm, mul_assoc]
  have hmap_range (x : StandardRealization (barycentricSubdivision K)) :
      (fun v => barycentricMap K x.val v) ∈ (realization K).space := by
    rcases Geometry.SimplicialComplex.mem_space_iff.mp x.property with ⟨t, ht, hxconv⟩
    rcases realized_face_originates (barycentricSubdivision K) ht with ⟨c, hc, rfl⟩
    change x.val ∈ convexHull ℝ (↑(c.image (barycentricVertex (V := Face K))) :
      Set (Face K → ℝ)) at hxconv
    rw [mem_convexHull_iff_exists_fintype] at hxconv
    rcases hxconv with ⟨ι, _, w, p, hw0, hw1, hp, hsum⟩
    have hp' : ∀ i, p i ∈ c.image (barycentricVertex (V := Face K)) := fun i =>
      Finset.mem_coe.mp (hp i)
    choose f hf using fun i => Finset.mem_image.mp (hp' i)
    have hcoord (s : Face K) : x.val s = ∑ i, w i *
        (barycentricVertex (V := Face K) (f i)) s := by
      have heq := congrArg (fun y : Face K → ℝ => y s) hsum
      simpa [hf, smul_eq_mul] using heq.symm
    have hxnonneg : ∀ s : Face K, 0 ≤ x.val s := by
      intro s
      rw [hcoord]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hw0 i) (by
        simp only [barycentricVertex, Pi.single_apply]
        split_ifs <;> norm_num)
    have hxtotal : (∑ s : Face K, x.val s) = 1 := by
      simp_rw [hcoord]
      rw [Finset.sum_comm]
      simp [barycentricVertex, Pi.single_apply, mul_ite, hw1]
    let C := Finset.univ.filter fun s : Face K => 0 < x.val s
    have hCne : C.Nonempty := by
      have hpos : 0 < x.val := (Fintype.sum_pos_iff_of_nonneg hxnonneg).mp
        (by rw [hxtotal]; norm_num)
      obtain ⟨s, hs⟩ := (Pi.lt_def.mp hpos).2
      exact ⟨s, by simpa [C, Pi.zero_apply] using hs⟩
    have hCsub : C ⊆ c := by
      intro s hs
      have hspos : 0 < x.val s := (Finset.mem_filter.mp hs).2
      rw [hcoord] at hspos
      have hpos : 0 < fun i => w i * (barycentricVertex (V := Face K) (f i)) s :=
        (Fintype.sum_pos_iff_of_nonneg (fun i => mul_nonneg (hw0 i) (by
          simp only [barycentricVertex, Pi.single_apply]
          split_ifs <;> norm_num))).mp hspos
      obtain ⟨i, hi⟩ := (Pi.lt_def.mp hpos).2
      have hfi : f i = s := by
        by_contra hne
        simp [barycentricVertex, hne] at hi
      exact hfi ▸ (hf i).1
    have hxchain : C ∈ (barycentricSubdivision K).faces :=
      ((barycentricSubdivision K).isRelLowerSet_faces hc).2 hCsub hCne
    have hnonneg : ∀ v, 0 ≤ barycentricMap K x.val v := by
      intro v
      rw [map_eq]
      apply Finset.sum_nonneg
      intro s hs
      exact mul_nonneg (hxnonneg s) (by
        dsimp [bary]
        split_ifs <;> positivity)
    have htotal : (∑ v, barycentricMap K x.val v) = 1 := by
      simp_rw [map_eq]
      calc
        (∑ v : V, ∑ s : Face K, x.val s * bary s v) =
            ∑ s : Face K, ∑ v : V, x.val s * bary s v := Finset.sum_comm
        _ = ∑ s : Face K, x.val s * ∑ v : V, bary s v := by
          simp_rw [Finset.mul_sum]
        _ = 1 := by simp [hsum_bary, hxtotal]
    have hmax : ∃ s₀ ∈ C, ∀ s ∈ C, s.val ⊆ s₀.val := by
      let n := C.sup' hCne fun s => s.val.card
      obtain ⟨s₀, hs₀C, hs₀n⟩ := Finset.exists_mem_eq_sup' hCne
        (fun s : Face K => s.val.card)
      change n = s₀.val.card at hs₀n
      refine ⟨s₀, hs₀C, ?_⟩
      intro s hsC
      have hchain : ∀ a ∈ C, ∀ b ∈ C, a.val ⊆ b.val ∨ b.val ⊆ a.val := hxchain.2
      rcases hchain s hsC s₀ hs₀C with hss₀ | hs₀s
      · exact hss₀
      · have hcardle : s.val.card ≤ s₀.val.card := by
          calc
            s.val.card ≤ C.sup' hCne (fun s : Face K => s.val.card) :=
              Finset.le_sup' (fun s : Face K => s.val.card) hsC
            _ = s₀.val.card := hs₀n
        have hcard : s.val.card = s₀.val.card :=
          le_antisymm hcardle (Finset.card_le_card hs₀s)
        have heq : s₀.val = s.val :=
          Finset.eq_of_subset_of_card_le hs₀s (by rw [hcard])
        exact heq.symm ▸ Finset.Subset.rfl
    obtain ⟨s₀, hs₀C, hle⟩ := hmax
    have hsub : (Finset.univ.filter fun v : V => 0 < barycentricMap K x.val v) ⊆ s₀.val := by
      intro v hv
      have hvpos : 0 < barycentricMap K x.val v := (Finset.mem_filter.mp hv).2
      rw [map_eq] at hvpos
      have hpos : 0 < fun s : Face K => x.val s * bary s v :=
        (Fintype.sum_pos_iff_of_nonneg (fun s =>
          mul_nonneg (hxnonneg s) (by
            dsimp [bary]
            split_ifs <;> positivity))).mp hvpos
      obtain ⟨s, hs⟩ := (Pi.lt_def.mp hpos).2
      have hsx : 0 < x.val s := by
        by_contra! hn
        have hz : x.val s = 0 := le_antisymm hn (hxnonneg s)
        simp [hz] at hs
      have hsC : s ∈ C := by simpa [C, Pi.zero_apply] using hsx
      have hle' := hle s hsC
      have hvis : v ∈ s.val := by
        by_contra hnot
        simp [bary, hnot] at hs
      exact hle' hvis
    have hs₀face : s₀.val ∈ K.faces := s₀.property
    have hsuppface :
        (Finset.univ.filter fun v : V => 0 < barycentricMap K x.val v) ∈ K.faces :=
      (K.isRelLowerSet_faces hs₀face).2 hsub
        (by
          have hpos : 0 < barycentricMap K x.val := (Fintype.sum_pos_iff_of_nonneg hnonneg).mp
            (by rw [htotal]; norm_num)
          obtain ⟨v, hv⟩ := (Pi.lt_def.mp hpos).2
          exact ⟨v, by simpa [Pi.zero_apply] using hv⟩)
    have hs₀ne : s₀.val.Nonempty := (K.isRelLowerSet_faces s₀.property).1
    obtain ⟨v₀, hv₀⟩ := hs₀ne
    let w : Face K × V → ℝ := fun p => x.val p.1 * bary p.1 p.2
    let z : Face K × V → V → ℝ := fun p =>
      if hp : p.1 ∈ C ∧ p.2 ∈ p.1.val then barycentricVertex p.2
      else barycentricVertex v₀
    have hw0 : ∀ p, 0 ≤ w p := by
      intro p
      dsimp [w, bary]
      exact mul_nonneg (hxnonneg p.1) (by split_ifs <;> positivity)
    have hw1 : (∑ p : Face K × V, w p) = 1 := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ s : Face K, ∑ v : V, x.val s * bary s v) =
            ∑ s : Face K, x.val s * ∑ v : V, bary s v := by
          congr 1
          funext s
          rw [Finset.mul_sum]
        _ = 1 := by simp [hsum_bary, hxtotal]
    have hz : ∀ p, z p ∈ (↑(s₀.val.image barycentricVertex) : Set (V → ℝ)) := by
      intro p
      apply Finset.mem_coe.mpr
      rw [Finset.mem_image]
      by_cases hp : p.1 ∈ C ∧ p.2 ∈ p.1.val
      · exact ⟨p.2, hle p.1 hp.1 hp.2, by simp [z, hp]⟩
      · exact ⟨v₀, hv₀, by simp [z, hp]⟩
    have hterm (p : Face K × V) : w p • z p = w p • barycentricVertex p.2 := by
      by_cases hp : p.1 ∈ C ∧ p.2 ∈ p.1.val
      · simp [z, hp]
      · have hwzero : w p = 0 := by
          by_cases hs : p.1 ∈ C
          · have hvnot : p.2 ∉ p.1.val := fun hv => hp ⟨hs, hv⟩
            simp [w, bary, hvnot]
          · have hn : ¬ 0 < x.val p.1 := by simpa [C] using hs
            have hxzero : x.val p.1 = 0 := le_antisymm (le_of_not_gt hn) (hxnonneg p.1)
            simp [w, hxzero]
        simp [hwzero]
    have hsum_vertex (s : Face K) (u : V) :
        (∑ v : V, bary s v * barycentricVertex v u) = bary s u := by
      simp [bary, barycentricVertex, Pi.single_apply]
    have hcomb : (∑ p : Face K × V, w p • z p) =
        (fun v => barycentricMap K x.val v) := by
      ext u
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ p : Face K × V, w p * z p u) =
            ∑ p : Face K × V, w p * barycentricVertex p.2 u := by
          apply Finset.sum_congr rfl
          intro p hp
          simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (hterm p) u
        _ = ∑ s : Face K, x.val s * bary s u := by
          rw [Fintype.sum_prod_type]
          calc
            (∑ s : Face K, ∑ v : V, x.val s * bary s v *
                barycentricVertex v u) =
                ∑ s : Face K, x.val s * ∑ v : V, bary s v * barycentricVertex v u := by
              congr 1
              funext s
              rw [Finset.mul_sum]
              congr 1
              funext v
              ring
            _ = ∑ s : Face K, x.val s * bary s u := by simp_rw [hsum_vertex]
        _ = barycentricMap K x.val u := (map_eq x.val u).symm
    have hconv : (fun v => barycentricMap K x.val v) ∈
        convexHull ℝ (↑(s₀.val.image barycentricVertex) : Set (V → ℝ)) := by
      apply mem_convexHull_of_exists_fintype (w := w) (z := z)
      · exact hw0
      · exact hw1
      · exact hz
      · exact hcomb
    exact (realization K).convexHull_subset_space (abstract_face_realizes K s₀.property) hconv
  let f : StandardRealization (barycentricSubdivision K) → StandardRealization K :=
    fun x => ⟨fun v => barycentricMap K x.val v, hmap_range x⟩
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    · apply continuous_pi
      intro v
      change Continuous (fun x : StandardRealization (barycentricSubdivision K) =>
        ∑ s : Face K, x.val s *
          ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0))
      apply continuous_finset_sum
      intro s hs
      exact ((continuous_apply s).comp continuous_subtype_val).mul continuous_const
  exact ⟨hmap_range, continuous_subtype_val.comp hfcont⟩
theorem barycentric_subdivision_realization_homeomorph
    (K : FiniteAbstractComplex V) :
    ∃ e : StandardRealization (barycentricSubdivision K) ≃ₜ StandardRealization K,
      ∀ x : StandardRealization (barycentricSubdivision K), ∀ v : V,
        (e x).val v = barycentricMap K x.val v :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases barycentric_map_range_and_continuous K with ⟨hmap, hcont⟩
  let f : StandardRealization (barycentricSubdivision K) → StandardRealization K :=
    fun x => ⟨fun v => barycentricMap K x.val v, hmap x⟩
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    exact hcont

  let lift : (Face K → ℝ) → Finset V → ℝ := fun a s =>
    if hs : s ∈ K.faces then a ⟨s, hs⟩ else 0
  have subtype_face_sum (q : Face K → ℝ) :
      (∑ s : {s : Finset V // s ∈ K.faces}, q ⟨s.val, s.property⟩) =
        ∑ s : Face K, q s := by
    exact Fintype.sum_equiv (Equiv.refl (Face K)) _ _ (fun _ => rfl)
  have sum_lift (a : Face K → ℝ) (v : V) :
      (∑ s : Finset V, lift a s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)) =
        ∑ s : Face K, a s * ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0) := by
    let p : Finset V → Prop := fun s => s ∈ K.faces
    let term : Finset V → ℝ := fun s => lift a s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)
    have hcompl :
        (∑ s : {s : Finset V // ¬ p s}, term s.val) = 0 := by
      apply Fintype.sum_eq_zero
      intro s
      simp [term, lift, p, s.property]
    have hdecomp := (Fintype.sum_subtype_add_sum_subtype p term).symm
    have hinst : Subtype.fintype p = faceFintype K := Subsingleton.elim _ _
    rw [hinst] at hdecomp
    calc
      (∑ s : Finset V, term s) =
          (∑ s : {s : Finset V // p s}, term s.val) +
            (∑ s : {s : Finset V // ¬ p s}, term s.val) :=
        hdecomp
      _ = ∑ s : Face K, a s * ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0) := by
        rw [hcompl, add_zero]
        simpa [term, lift, p] using
          subtype_face_sum (fun s => a s * ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0))

  have hempty : (∅ : Finset V) ∉ K.faces := by
    intro h
    exact (Finset.not_nonempty_iff_eq_empty.mpr rfl) (K.isRelLowerSet_faces h).1

  have hinj : Function.Injective f := by
    intro x y hxy
    let w : Finset V → ℝ := lift x.val
    let z : Finset V → ℝ := lift y.val
    have hxcoord :=
      (PoincareConjecture.ParallelImplementation.FiniteRealizationCoordinates.mem_realization_iff_coordinates
        (barycentricSubdivision K) x.val).mp x.property
    have hycoord :=
      (PoincareConjecture.ParallelImplementation.FiniteRealizationCoordinates.mem_realization_iff_coordinates
        (barycentricSubdivision K) y.val).mp y.property
    have hw0 : w ∅ = 0 := by simp [w, lift, hempty]
    have hz0 : z ∅ = 0 := by simp [z, lift, hempty]
    have hw : ∀ s, 0 ≤ w s := by
      intro s
      by_cases hs : s ∈ K.faces
      · simpa [w, lift, hs] using hxcoord.1 ⟨s, hs⟩
      · simp [w, lift, hs]
    have hz : ∀ s, 0 ≤ z s := by
      intro s
      by_cases hs : s ∈ K.faces
      · simpa [z, lift, hs] using hycoord.1 ⟨s, hs⟩
      · simp [z, lift, hs]
    have hwchain : ∀ a b, 0 < w a → 0 < w b → a ⊆ b ∨ b ⊆ a := by
      intro a b ha hb
      have haFace : a ∈ K.faces := by
        by_contra h
        simp [w, lift, h] at ha
      have hbFace : b ∈ K.faces := by
        by_contra h
        simp [w, lift, h] at hb
      have haPos : 0 < x.val ⟨a, haFace⟩ := by simpa [w, lift, haFace] using ha
      have hbPos : 0 < x.val ⟨b, hbFace⟩ := by simpa [w, lift, hbFace] using hb
      have hchain := hxcoord.2.2
      change (Finset.univ.filter fun s : Face K => 0 < x.val s) ∈
        (barycentricSubdivision K).faces at hchain
      exact hchain.2 ⟨a, haFace⟩ (by simp [haPos]) ⟨b, hbFace⟩ (by simp [hbPos])
    have hzchain : ∀ a b, 0 < z a → 0 < z b → a ⊆ b ∨ b ⊆ a := by
      intro a b ha hb
      have haFace : a ∈ K.faces := by
        by_contra h
        simp [z, lift, h] at ha
      have hbFace : b ∈ K.faces := by
        by_contra h
        simp [z, lift, h] at hb
      have haPos : 0 < y.val ⟨a, haFace⟩ := by simpa [z, lift, haFace] using ha
      have hbPos : 0 < y.val ⟨b, hbFace⟩ := by simpa [z, lift, hbFace] using hb
      have hchain := hycoord.2.2
      change (Finset.univ.filter fun s : Face K => 0 < y.val s) ∈
        (barycentricSubdivision K).faces at hchain
      exact hchain.2 ⟨a, haFace⟩ (by simp [haPos]) ⟨b, hbFace⟩ (by simp [hbPos])
    have hpoint : ∀ v : V, barycentricMap K x.val v = barycentricMap K y.val v := by
      have hval := congrArg Subtype.val hxy
      intro v
      exact congrFun hval v
    have hcoords : ∀ v : V,
        (∑ s : Finset V, w s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)) =
        (∑ s : Finset V, z s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)) := by
      intro v
      rw [sum_lift, sum_lift]
      exact hpoint v
    have hweights :=
      PoincareConjecture.ParallelImplementation.BarycentricChainInjectivity.chain_weights_eq_of_barycenter_eq
        w z hw0 hz0 hw hz hwchain hzchain hcoords
    apply Subtype.ext
    funext s
    have hs := congrFun hweights s.val
    simpa [w, z, lift] using hs

  have hsurj : Function.Surjective f := by
    intro y
    have hycoord :=
      (PoincareConjecture.ParallelImplementation.FiniteRealizationCoordinates.mem_realization_iff_coordinates
        K y.val).mp y.property
    let g : Finset V → ℝ :=
      PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse.recoveredWeight y.val
    have hlayer :=
      PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse.finite_layer_cake
        y.val hycoord.1
    have hzeroOut : ∀ s : Finset V, s ∉ K.faces → g s = 0 := by
      intro s hs
      by_contra hne
      have hne' : (0 : ℝ) ≠ g s := by
        intro h
        exact hne h.symm
      have hspos : 0 < g s := lt_of_le_of_ne (hlayer.1 s) hne'
      have hsne : s.Nonempty := by
        by_contra h
        have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        subst s
        simp [g, PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse.recoveredWeight] at hspos
      have hsub : s ⊆ Finset.univ.filter fun v : V => 0 < y.val v := by
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlayer.2.2.1 s hspos v hv
      have hsface : s ∈ K.faces := (K.isRelLowerSet_faces hycoord.2.2).2 hsub hsne
      exact hs hsface
    let a : Face K → ℝ := fun s => g s.val
    have hmass : (∑ s : Face K, a s) = 1 := by
      have hcompl :
          (∑ s : {s : Finset V // ¬ s ∈ K.faces}, g s.val) = 0 := by
        apply Fintype.sum_eq_zero
        intro s
        simp [hzeroOut s s.property]
      let p : Finset V → Prop := fun s => s ∈ K.faces
      have hdecomp := (Fintype.sum_subtype_add_sum_subtype p (fun s => g s)).symm
      have hinst : Subtype.fintype p = faceFintype K := Subsingleton.elim _ _
      rw [hinst] at hdecomp
      calc
        (∑ s : Face K, a s) = ∑ s : {s : Finset V // s ∈ K.faces}, g s.val := by
          symm
          exact subtype_face_sum (fun s => g s.val)
        _ = ∑ s : Finset V, g s := by
          symm
          calc
            (∑ s : Finset V, g s) =
                (∑ s : {s : Finset V // p s}, g s.val) +
                  (∑ s : {s : Finset V // ¬ p s}, g s.val) := hdecomp
            _ = ∑ s : {s : Finset V // p s}, g s.val := by rw [hcompl, add_zero]
        _ = 1 := by rw [hlayer.2.2.2.2, hycoord.2.1]
    have haNonneg : ∀ s : Face K, 0 ≤ a s := fun s => hlayer.1 s.val
    let S : Finset (Face K) := Finset.univ.filter fun s => 0 < a s
    have hS_nonempty : S.Nonempty := by
      have hpos : 0 < ∑ s : Face K, a s := by rw [hmass]; norm_num
      have hpos' := (Fintype.sum_pos_iff_of_nonneg haNonneg).mp hpos
      obtain ⟨s, hs⟩ := (Pi.lt_def.mp hpos').2
      have hs' : 0 < a s := by simpa using hs
      exact ⟨s, by simp [S, hs']⟩
    have hS_chain : ∀ u ∈ S, ∀ v ∈ S, u.val ⊆ v.val ∨ v.val ⊆ u.val := by
      intro u hu v hv
      exact hlayer.2.1 u.val v.val (by simpa [S, a] using (Finset.mem_filter.mp hu).2)
        (by simpa [S, a] using (Finset.mem_filter.mp hv).2)
    have haCoords : (∑ s : Face K, a s) = 1 := hmass
    have hface : S ∈ (barycentricSubdivision K).faces := by
      change S.Nonempty ∧ _
      exact ⟨hS_nonempty, hS_chain⟩
    have hamem : a ∈ (realization (barycentricSubdivision K)).space :=
      (PoincareConjecture.ParallelImplementation.FiniteRealizationCoordinates.mem_realization_iff_coordinates
        (barycentricSubdivision K) a).2
        ⟨haNonneg, haCoords, hface⟩
    let x : StandardRealization (barycentricSubdivision K) := ⟨a, hamem⟩
    have hlift : lift a = g := by
      funext s
      by_cases hs : s ∈ K.faces
      · simp [lift, a, g, hs]
      · simp [lift, hs, hzeroOut s hs]
    have hsumcoord (v : V) :
        barycentricMap K a v =
          PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse.barycenterCoordinates
            g v := by
      calc
        barycentricMap K a v =
            ∑ s : Face K, a s * ((s.val.card : ℝ)⁻¹ * if v ∈ s.val then 1 else 0) := rfl
        _ = ∑ s : Finset V, lift a s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0) :=
          (sum_lift a v).symm
        _ = ∑ s : Finset V, g s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0) := by
          rw [hlift]
        _ = PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse.barycenterCoordinates
            g v := rfl
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext v
    change barycentricMap K a v = y.val v
    rw [hsumcoord]
    exact hlayer.2.2.2.1 v

  letI : CompactSpace (StandardRealization (barycentricSubdivision K)) :=
    isCompact_iff_compactSpace.mp
      (PoincareConjecture.ParallelImplementation.FinitePLRealization.realization_isCompact
        (barycentricSubdivision K))
  letI : T2Space (StandardRealization K) := inferInstance
  let e : StandardRealization (barycentricSubdivision K) ≃ StandardRealization K :=
    Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hecont : Continuous (⇑e) := by simpa [e] using hfcont
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hecont, ?_⟩
  intro x v
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricSubdivisionRealization
