import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FinitePolytopeHalfspaceClip
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
def crossingPoint (f : E →ₗ[ℝ] ℝ) (a : ℝ) (u v : E) : E :=
  ((f v - a) / (f v - f u)) • u + ((a - f u) / (f v - f u)) • v
def clippedVertices (s : Finset E) (f : E →ₗ[ℝ] ℝ) (a : ℝ) : Finset E := by
  classical
  exact (s.filter fun v => f v ≤ a) ∪
    (((s.product s).filter fun p => f p.1 < a ∧ a < f p.2).image
      fun p => crossingPoint f a p.1 p.2)
/-- Explicit finite vertices for clipping a finite convex hull by one closed
halfspace. This is actual polytope geometry needed by common PL refinement,
not an assumed finite-intersection certificate. -/
theorem convexHull_inter_halfspace_eq_clipped
    (s : Finset E) (f : E →ₗ[ℝ] ℝ) (a : ℝ) :
    convexHull ℝ (s : Set E) ∩ {x : E | f x ≤ a} =
      convexHull ℝ (clippedVertices s f a : Set E) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨hx, hxa⟩
    rcases (Finset.mem_convexHull' (R := ℝ) (s := s) (x := x)).mp hx with
      ⟨w, hw0, hw1, hwx⟩
    let R : Finset E := s.filter fun v => f v ≤ a
    let I : Finset E := s.filter fun v => f v < a
    let O : Finset E := s.filter fun v => a < f v
    let D : E → ℝ := fun v => a - f v
    let H : E → ℝ := fun v => f v - a
    let α : E → ℝ := fun v => w v * D v
    let β : E → ℝ := fun v => w v * H v
    let A : ℝ := ∑ i ∈ I, α i
    let B : ℝ := ∑ j ∈ O, β j
    have hfx : (∑ v ∈ s, w v * f v) = f x := by
      calc
        (∑ v ∈ s, w v * f v) = f (∑ v ∈ s, w v • v) := by
          simp only [map_sum, map_smul, smul_eq_mul]
        _ = f x := congrArg f hwx
    have hwhole : (∑ v ∈ s, w v * (a - f v)) = a - f x := by
      calc
        (∑ v ∈ s, w v * (a - f v)) =
            (∑ v ∈ s, (w v * a - w v * f v)) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
        _ = (∑ v ∈ s, w v * a) - ∑ v ∈ s, w v * f v := by
              rw [← Finset.sum_sub_distrib]
        _ = a - f x := by rw [← Finset.sum_mul, hw1, hfx]; ring
    have hRI : I = R.filter fun v => f v < a := by
      ext v
      simp only [I, R, Finset.mem_filter]
      constructor
      · rintro ⟨hv, hlt⟩
        exact ⟨⟨hv, le_of_lt hlt⟩, hlt⟩
      · rintro ⟨⟨hv, hle⟩, hlt⟩
        exact ⟨hv, hlt⟩
    have hA_as_R : A = ∑ v ∈ R, w v * (a - f v) := by
      dsimp [A, α, D]
      apply Finset.sum_subset
      · intro v hv
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hv).1, le_of_lt (Finset.mem_filter.mp hv).2⟩
      · intro v hvR hvI
        have hvS : v ∈ s := (Finset.mem_filter.mp hvR).1
        have hle : f v ≤ a := (Finset.mem_filter.mp hvR).2
        have hnlt : ¬ f v < a := by
          intro hlt
          exact hvI (by simp [I, hvS, hlt])
        have heq : f v = a := le_antisymm hle (le_of_not_gt hnlt)
        simp [heq]
    have hO_as_neg : (∑ v ∈ O, w v * (a - f v)) = -B := by
      calc
        (∑ v ∈ O, w v * (a - f v)) =
            ∑ v ∈ O, -(w v * (f v - a)) := by
              apply Finset.sum_congr rfl
              intro v hv
              ring
        _ = -(∑ v ∈ O, w v * (f v - a)) := by rw [Finset.sum_neg_distrib]
        _ = -B := by rfl
    have hsplit (g : E → ℝ) :
        (∑ v ∈ R, g v) + ∑ v ∈ O, g v = ∑ v ∈ s, g v := by
      rw [← Finset.sum_filter_add_sum_filter_not s (fun v => f v ≤ a) g]
      simp [R, O, not_le]
    have hdiff : A - B = a - f x := by
      calc
        A - B = (∑ v ∈ R, w v * (a - f v)) +
            ∑ v ∈ O, w v * (a - f v) := by rw [hA_as_R, hO_as_neg]; ring
        _ = ∑ v ∈ s, w v * (a - f v) := hsplit _
        _ = a - f x := hwhole
    have hA_nonneg : 0 ≤ A := by
      dsimp [A, α, D]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hw0 i (Finset.mem_filter.mp hi).1)
        (sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp hi).2))
    have hB_nonneg : 0 ≤ B := by
      dsimp [B, β, H]
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (hw0 j (Finset.mem_filter.mp hj).1)
        (sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp hj).2))
    have hBA : B ≤ A := by
      have hfxa : f x ≤ a := hxa
      linarith [hdiff, hfxa]
    have hratio_nonneg : 0 ≤ B / A := div_nonneg hB_nonneg hA_nonneg
    have hratio_le : B / A ≤ 1 := div_le_one_of_le₀ hBA hA_nonneg
    have hB_zero_of_A_zero : A = 0 → B = 0 := by
      intro hA0
      apply le_antisymm
      · simpa [hA0] using hBA
      · exact hB_nonneg
    have hO_weight_zero_of_A_zero : A = 0 → ∀ j ∈ O, w j = 0 := by
      intro hA0 j hj
      have hB0 := hB_zero_of_A_zero hA0
      have hterm : w j * (f j - a) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k hk =>
          mul_nonneg (hw0 k (Finset.mem_filter.mp hk).1)
            (sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp hk).2)))).mp hB0 j hj
      nlinarith [Finset.mem_filter.mp hj |>.2]
    have houtside_scale (j : {v : E // v ∈ O}) :
        w j.val * (A / A) = w j.val := by
      by_cases hA0 : A = 0
      · have hwj := hO_weight_zero_of_A_zero hA0 j.val j.property
        simp [hA0, hwj]
      · rw [div_self hA0, mul_one]
    let p : E → E → ℝ := fun i j => α i * β j / A
    let q : E → E → ℝ := fun i j =>
      p i j * (1 / D i + 1 / H j)
    let RT := {v : E // v ∈ R}
    let IT := {v : E // v ∈ I}
    let OT := {v : E // v ∈ O}
    letI : Fintype RT := Fintype.ofFinset R (by intro v; rfl)
    letI : Fintype IT := Fintype.ofFinset I (by intro v; rfl)
    letI : Fintype OT := Fintype.ofFinset O (by intro v; rfl)
    let c : RT ⊕ (IT × OT) → ℝ := fun k =>
      match k with
      | Sum.inl v => if f v.val < a then w v.val * (1 - B / A) else w v.val
      | Sum.inr ij => q ij.1.val ij.2.val
    let z : RT ⊕ (IT × OT) → E := fun k =>
      match k with
      | Sum.inl v => v.val
      | Sum.inr ij => crossingPoint f a ij.1.val ij.2.val
    have hcoeff_nonneg : ∀ k, 0 ≤ c k := by
      intro k
      cases k with
      | inl v =>
          dsimp [c]
          split_ifs with hv
          · exact mul_nonneg (hw0 v.val (Finset.mem_filter.mp v.property).1)
              (sub_nonneg.mpr hratio_le)
          · exact hw0 v.val (Finset.mem_filter.mp v.property).1
      | inr ij =>
          dsimp [c, q, p, α, β, D, H]
          apply mul_nonneg
          · exact div_nonneg
              (mul_nonneg
                (mul_nonneg (hw0 ij.1.val (Finset.mem_filter.mp ij.1.property).1)
                  (sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp ij.1.property).2)))
                (mul_nonneg (hw0 ij.2.val (Finset.mem_filter.mp ij.2.property).1)
                  (sub_nonneg.mpr (le_of_lt (Finset.mem_filter.mp ij.2.property).2))))
              hA_nonneg
          · exact add_nonneg (div_nonneg zero_le_one (sub_nonneg.mpr
                (le_of_lt (Finset.mem_filter.mp ij.1.property).2)))
              (div_nonneg zero_le_one (sub_nonneg.mpr
                (le_of_lt (Finset.mem_filter.mp ij.2.property).2)))
    have hz : ∀ k, z k ∈ clippedVertices s f a := by
      intro k
      cases k with
      | inl v =>
          simp only [z, clippedVertices, Finset.mem_union]
          left
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp v.property).1, (Finset.mem_filter.mp v.property).2⟩
      | inr ij =>
          simp only [z, clippedVertices, Finset.mem_union]
          right
          apply Finset.mem_image.mpr
          refine ⟨(ij.1.val, ij.2.val), Finset.mem_filter.mpr ?_, rfl⟩
          constructor
          · exact Finset.mem_product.mpr
              ⟨(Finset.mem_filter.mp ij.1.property).1,
                (Finset.mem_filter.mp ij.2.property).1⟩
          · exact ⟨(Finset.mem_filter.mp ij.1.property).2,
              (Finset.mem_filter.mp ij.2.property).2⟩
    have hsumRreal (g : E → ℝ) :
        (∑ v : RT, g v.val) = ∑ v ∈ R, g v := by
      simpa only [Finset.attach_eq_univ] using (Finset.sum_attach R g)
    have hsumIreal (g : E → ℝ) :
        (∑ v : IT, g v.val) = ∑ v ∈ I, g v := by
      simpa only [Finset.attach_eq_univ] using (Finset.sum_attach I g)
    have hsumOreal (g : E → ℝ) :
        (∑ v : OT, g v.val) = ∑ v ∈ O, g v := by
      simpa only [Finset.attach_eq_univ] using (Finset.sum_attach O g)
    have hres_sum_fin :
        (∑ v ∈ R, if f v < a then w v * (1 - B / A) else w v) =
          (∑ v ∈ R, w v) - (B / A) * (∑ v ∈ I, w v) := by
      calc
        (∑ v ∈ R, if f v < a then w v * (1 - B / A) else w v) =
            ∑ v ∈ R, (w v - if f v < a then w v * (B / A) else 0) := by
              apply Finset.sum_congr rfl
              intro v hv
              by_cases hlt : f v < a <;> simp [hlt] <;> ring
        _ = (∑ v ∈ R, w v) -
              ∑ v ∈ R, if f v < a then w v * (B / A) else 0 := by
                rw [← Finset.sum_sub_distrib]
        _ = (∑ v ∈ R, w v) - ∑ v ∈ I, w v * (B / A) := by
              congr 1
              rw [← Finset.sum_filter, hRI]
        _ = (∑ v ∈ R, w v) - (B / A) * (∑ v ∈ I, w v) := by
              rw [← Finset.sum_mul]
              ring
    have hres_sum :
        (∑ v : RT, if f v.val < a then w v.val * (1 - B / A) else w v.val) =
          (∑ v ∈ R, w v) - (B / A) * (∑ v ∈ I, w v) := by
      calc
        _ = ∑ v ∈ R, if f v < a then w v * (1 - B / A) else w v :=
          hsumRreal _
        _ = _ := hres_sum_fin
    have hsumAlpha : (∑ i : IT, α i.val) = A := by
      calc
        (∑ i : IT, α i.val) = ∑ i ∈ I, α i := hsumIreal α
        _ = A := rfl
    have hsumBeta : (∑ j : OT, β j.val) = B := by
      calc
        (∑ j : OT, β j.val) = ∑ j ∈ O, β j := hsumOreal β
        _ = B := rfl
    have hDpos (i : IT) : 0 < D i.val :=
      sub_pos.mpr (Finset.mem_filter.mp i.property).2
    have hHpos (j : OT) : 0 < H j.val :=
      sub_pos.mpr (Finset.mem_filter.mp j.property).2
    have hpFactorI (i : IT) (j : OT) :
        p i.val j.val = (w i.val * (β j.val / A)) * D i.val := by
      dsimp [p, α, D]
      rw [mul_div_assoc]
      ring
    have hpFactorO (i : IT) (j : OT) :
        p i.val j.val = (α i.val * (w j.val / A)) * H j.val := by
      dsimp [p, β, H]
      rw [mul_div_assoc]
      ring
    have hpInside (i : IT) (j : OT) :
        p i.val j.val / D i.val = w i.val * (β j.val / A) := by
      rw [hpFactorI i j, mul_div_cancel_right₀ _ (ne_of_gt (hDpos i))]
    have hpOutside (i : IT) (j : OT) :
        p i.val j.val / H j.val = α i.val * (w j.val / A) := by
      rw [hpFactorO i j, mul_div_cancel_right₀ _ (ne_of_gt (hHpos j))]
    have hqDecomp (i : IT) (j : OT) :
        q i.val j.val = p i.val j.val / D i.val + p i.val j.val / H j.val := by
      dsimp [q]
      simp only [div_eq_mul_inv]
      ring
    have hqInside (i : IT) (j : OT) :
        q i.val j.val * (H j.val / (D i.val + H j.val)) = p i.val j.val / D i.val := by
      have hd := ne_of_gt (hDpos i)
      have he := ne_of_gt (hHpos j)
      have hde := ne_of_gt (add_pos (hDpos i) (hHpos j))
      dsimp [q]
      field_simp [hd, he, hde]
      <;> ring
    have hqOutside (i : IT) (j : OT) :
        q i.val j.val * (D i.val / (D i.val + H j.val)) = p i.val j.val / H j.val := by
      have hd := ne_of_gt (hDpos i)
      have he := ne_of_gt (hHpos j)
      have hde := ne_of_gt (add_pos (hDpos i) (hHpos j))
      dsimp [q]
      field_simp [hd, he, hde]
      <;> ring
    have hcrossPoint (i : IT) (j : OT) :
        crossingPoint f a i.val j.val =
          (H j.val / (D i.val + H j.val)) • i.val +
            (D i.val / (D i.val + H j.val)) • j.val := by
      unfold crossingPoint
      have hden : f j.val - f i.val = D i.val + H j.val := by
        dsimp [D, H]
        ring
      rw [hden]
    have hpairVector (i : IT) (j : OT) :
        q i.val j.val • crossingPoint f a i.val j.val =
          (w i.val * (β j.val / A)) • i.val +
            (α i.val * (w j.val / A)) • j.val := by
      rw [hcrossPoint]
      simp only [smul_add, smul_smul]
      rw [hqInside, hqOutside, hpInside, hpOutside]
    have hinnerBeta (i : IT) :
        (∑ j : OT, w i.val * (β j.val / A)) = w i.val * (B / A) := by
      calc
        (∑ j : OT, w i.val * (β j.val / A)) =
            w i.val * (∑ j : OT, β j.val / A) := by rw [← Finset.mul_sum]
        _ = w i.val * ((∑ j : OT, β j.val) / A) := by rw [← Finset.sum_div]
        _ = w i.val * (B / A) := by rw [hsumBeta]
    have hinnerAlpha (j : OT) :
        (∑ i : IT, α i.val * (w j.val / A)) = (A / A) * w j.val := by
      calc
        (∑ i : IT, α i.val * (w j.val / A)) =
            (∑ i : IT, α i.val) * (w j.val / A) := by rw [← Finset.sum_mul]
        _ = A * (w j.val / A) := by rw [hsumAlpha]
        _ = (A / A) * w j.val := by ring
    have hcrossWeightSum :
        (∑ ij : IT × OT, q ij.1.val ij.2.val) =
          (B / A) * (∑ i : IT, w i.val) + (A / A) * (∑ j : OT, w j.val) := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ i : IT, ∑ j : OT, q i.val j.val) =
            ∑ i : IT, ∑ j : OT,
              (w i.val * (β j.val / A) + α i.val * (w j.val / A)) := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                rw [hqDecomp, hpInside, hpOutside]
        _ = (∑ i : IT, w i.val * (B / A)) +
              (∑ j : OT, (A / A) * w j.val) := by
                simp_rw [Finset.sum_add_distrib]
                congr 1
                · apply Finset.sum_congr rfl
                  intro i hi
                  exact hinnerBeta i
                · rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact hinnerAlpha j
        _ = (B / A) * (∑ i : IT, w i.val) +
              (A / A) * (∑ j : OT, w j.val) := by
                rw [← Finset.sum_mul, ← Finset.mul_sum]
                ring
    have hinnerBetaVec (i : IT) :
        (∑ j : OT, (w i.val * (β j.val / A)) • i.val) =
          (w i.val * (B / A)) • i.val := by
      calc
        (∑ j : OT, (w i.val * (β j.val / A)) • i.val) =
            (∑ j : OT, w i.val * (β j.val / A)) • i.val := by rw [Finset.sum_smul]
        _ = (w i.val * (B / A)) • i.val := by rw [hinnerBeta i]
    have hinnerAlphaVec (j : OT) :
        (∑ i : IT, (α i.val * (w j.val / A)) • j.val) = w j.val • j.val := by
      calc
        (∑ i : IT, (α i.val * (w j.val / A)) • j.val) =
            (∑ i : IT, α i.val * (w j.val / A)) • j.val := by rw [Finset.sum_smul]
        _ = ((A / A) * w j.val) • j.val := by rw [hinnerAlpha j]
        _ = w j.val • j.val := by
          have hscale : (A / A) * w j.val = w j.val := by
            rw [mul_comm]
            exact houtside_scale j
          rw [hscale]
    have hcrossVectorSum :
        (∑ ij : IT × OT, q ij.1.val ij.2.val •
          crossingPoint f a ij.1.val ij.2.val) =
          (∑ i : IT, (w i.val * (B / A)) • i.val) +
            (∑ j : OT, w j.val • j.val) := by
      rw [Fintype.sum_prod_type]
      calc
        (∑ i : IT, ∑ j : OT,
            q i.val j.val • crossingPoint f a i.val j.val) =
          ∑ i : IT, ∑ j : OT,
            ((w i.val * (β j.val / A)) • i.val +
              (α i.val * (w j.val / A)) • j.val) := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                exact hpairVector i j
        _ = (∑ i : IT, (w i.val * (B / A)) • i.val) +
              (∑ j : OT, w j.val • j.val) := by
                simp_rw [Finset.sum_add_distrib]
                congr 1
                · apply Finset.sum_congr rfl
                  intro i hi
                  exact hinnerBetaVec i
                · rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact hinnerAlphaVec j
    have hresVectorFin :
        (∑ v ∈ R, if f v < a then (w v * (1 - B / A)) • v else w v • v) =
          (∑ v ∈ R, w v • v) - (B / A) • (∑ v ∈ I, w v • v) := by
      calc
        (∑ v ∈ R, if f v < a then (w v * (1 - B / A)) • v else w v • v) =
            ∑ v ∈ R, (w v • v - if f v < a then (w v * (B / A)) • v else 0) := by
              apply Finset.sum_congr rfl
              intro v hv
              by_cases hlt : f v < a
              · simp only [if_pos hlt]
                rw [show w v * (1 - B / A) = w v - w v * (B / A) by ring,
                  sub_smul]
              · simp [hlt]
        _ = (∑ v ∈ R, w v • v) -
              ∑ v ∈ R, if f v < a then (w v * (B / A)) • v else 0 := by
                rw [← Finset.sum_sub_distrib]
        _ = (∑ v ∈ R, w v • v) - ∑ v ∈ I, (w v * (B / A)) • v := by
              congr 1
              rw [← Finset.sum_filter, hRI]
        _ = (∑ v ∈ R, w v • v) - (B / A) • (∑ v ∈ I, w v • v) := by
              congr 1
              calc
                (∑ v ∈ I, (w v * (B / A)) • v) =
                    ∑ v ∈ I, (B / A) • (w v • v) := by
                      apply Finset.sum_congr rfl
                      intro v hv
                      rw [mul_comm, smul_smul]
                _ = (B / A) • (∑ v ∈ I, w v • v) := by
                      rw [← Finset.smul_sum]
    have hsumRvec (g : E → E) :
        (∑ v : RT, g v.val) = ∑ v ∈ R, g v := by
      simpa only [Finset.attach_eq_univ] using (Finset.sum_attach R g)
    have hsumIvec (g : E → E) :
        (∑ v : IT, g v.val) = ∑ v ∈ I, g v := by
      simpa only [Finset.attach_eq_univ] using (Finset.sum_attach I g)
    have hsumOvec (g : E → E) :
        (∑ v : OT, g v.val) = ∑ v ∈ O, g v := by
      simpa only [Finset.attach_eq_univ] using (Finset.sum_attach O g)
    have hresVector :
        (∑ v : RT, if f v.val < a then (w v.val * (1 - B / A)) • v.val
          else w v.val • v.val) =
          (∑ v ∈ R, w v • v) - (B / A) • (∑ v ∈ I, w v • v) := by
      calc
        _ = ∑ v ∈ R,
            if f v < a then (w v * (1 - B / A)) • v else w v • v := hsumRvec _
        _ = _ := hresVectorFin
    have hcrossWeightSum' :
        (∑ ij : IT × OT, q ij.1.val ij.2.val) =
          (B / A) * (∑ i : IT, w i.val) + (∑ j : OT, w j.val) := by
      rw [hcrossWeightSum]
      have houtsideFactor : (A / A) * (∑ j : OT, w j.val) =
          ∑ j : OT, w j.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (A / A) * w j.val = w j.val * (A / A) := by ring
          _ = w j.val := houtside_scale j
      rw [houtsideFactor]
    have hretainedWeight :
        (∑ v ∈ R, w v) + (∑ j : OT, w j.val) = 1 := by
      calc
        (∑ v ∈ R, w v) + (∑ j : OT, w j.val) =
            (∑ v ∈ R, w v) + (∑ v ∈ O, w v) := by rw [hsumOreal]
        _ = ∑ v ∈ s, w v := hsplit _
        _ = 1 := hw1
    have hweight_sum : (∑ k, c k) = 1 := by
      simp only [Fintype.sum_sum_type, c]
      calc
        (∑ v : RT, if f v.val < a then w v.val * (1 - B / A) else w v.val) +
            ∑ ij : IT × OT, q ij.1.val ij.2.val =
          (∑ v ∈ R, w v) - (B / A) * (∑ v ∈ I, w v) +
            ((B / A) * (∑ i : IT, w i.val) + (∑ j : OT, w j.val)) := by
              rw [hres_sum, hcrossWeightSum']
        _ = (∑ v ∈ R, w v) + (∑ j : OT, w j.val) := by
              rw [hsumIreal (fun v => w v)]
              ring
        _ = 1 := hretainedWeight
    have hscaledInsideVector :
        (∑ i : IT, (w i.val * (B / A)) • i.val) =
          (B / A) • (∑ v ∈ I, w v • v) := by
      calc
        (∑ i : IT, (w i.val * (B / A)) • i.val) =
            ∑ v ∈ I, (w v * (B / A)) • v :=
              hsumIvec (fun v : E => (w v * (B / A)) • v)
        _ = (B / A) • (∑ v ∈ I, w v • v) := by
              conv_rhs => rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro v hv
              rw [mul_comm, smul_smul]
    have hcrossVectorSum' :
        (∑ ij : IT × OT, q ij.1.val ij.2.val •
          crossingPoint f a ij.1.val ij.2.val) =
          (B / A) • (∑ v ∈ I, w v • v) + (∑ j : OT, w j.val • j.val) := by
      rw [hcrossVectorSum, hscaledInsideVector]
    have hsplitVector :
        (∑ v ∈ R, w v • v) + (∑ j : OT, w j.val • j.val) = x := by
      calc
        (∑ v ∈ R, w v • v) + (∑ j : OT, w j.val • j.val) =
            (∑ v ∈ R, w v • v) + (∑ v ∈ O, w v • v) := by
              congr 1
              exact hsumOvec (fun v => w v • v)
        _ = ∑ v ∈ s, w v • v := by
          rw [← Finset.sum_filter_add_sum_filter_not s (fun v => f v ≤ a)
            (fun v => w v • v)]
          simp [R, O, not_le]
        _ = x := hwx
    have hvector_sum : (∑ k, c k • z k) = x := by
      simp only [Fintype.sum_sum_type, c, z, ite_smul]
      calc
        (∑ v : RT, if f v.val < a then
            (w v.val * (1 - B / A)) • v.val else w v.val • v.val) +
          ∑ ij : IT × OT,
            q ij.1.val ij.2.val • crossingPoint f a ij.1.val ij.2.val =
          (∑ v ∈ R, w v • v) - (B / A) • (∑ v ∈ I, w v • v) +
            ((B / A) • (∑ v ∈ I, w v • v) +
              (∑ j : OT, w j.val • j.val)) := by
                rw [hresVector, hcrossVectorSum']
        _ = (∑ v ∈ R, w v • v) + (∑ j : OT, w j.val • j.val) := by abel
        _ = x := hsplitVector
    exact mem_convexHull_of_exists_fintype (s := (clippedVertices s f a : Set E))
      c z hcoeff_nonneg hweight_sum hz hvector_sum
  · intro x hx
    have hclip : (clippedVertices s f a : Set E) ⊆ convexHull ℝ (s : Set E) := by
        intro y hy
        have hy' : y ∈ clippedVertices s f a := by simpa only [Finset.mem_coe] using hy
        simp only [clippedVertices, Finset.mem_union] at hy'
        rcases hy' with hy | hy
        · exact subset_convexHull ℝ (s : Set E) (Finset.mem_filter.mp hy).1
        · rcases Finset.mem_image.mp hy with ⟨uv, huv, rfl⟩
          have huv' := Finset.mem_filter.mp huv
          have huvS := Finset.mem_product.mp huv'.1
          have huvLt := huv'.2
          have hd : 0 < a - f uv.1 := sub_pos.mpr huvLt.1
          have he : 0 < f uv.2 - a := sub_pos.mpr huvLt.2
          have hden : f uv.2 - f uv.1 = (a - f uv.1) + (f uv.2 - a) := by ring
          have hpoint : crossingPoint f a uv.1 uv.2 =
              ((f uv.2 - a) / ((a - f uv.1) + (f uv.2 - a))) • uv.1 +
                ((a - f uv.1) / ((a - f uv.1) + (f uv.2 - a))) • uv.2 := by
            unfold crossingPoint
            rw [hden]
          have hsum : (f uv.2 - a) / ((a - f uv.1) + (f uv.2 - a)) +
              (a - f uv.1) / ((a - f uv.1) + (f uv.2 - a)) = 1 := by
            have hden0 : (a - f uv.1) + (f uv.2 - a) ≠ 0 := ne_of_gt (add_pos hd he)
            field_simp [hden0]
            <;> ring
          have hmemseg : crossingPoint f a uv.1 uv.2 ∈ segment ℝ uv.1 uv.2 := by
            rw [hpoint]
            exact ⟨(f uv.2 - a) / ((a - f uv.1) + (f uv.2 - a)),
              (a - f uv.1) / ((a - f uv.1) + (f uv.2 - a)),
              div_nonneg (le_of_lt he) (le_of_lt (add_pos hd he)),
              div_nonneg (le_of_lt hd) (le_of_lt (add_pos hd he)), hsum, rfl⟩
          exact segment_subset_convexHull huvS.1 huvS.2 hmemseg
    have hclip_le : (clippedVertices s f a : Set E) ⊆ {y : E | f y ≤ a} := by
        intro y hy
        have hy' : y ∈ clippedVertices s f a := by simpa only [Finset.mem_coe] using hy
        simp only [clippedVertices, Finset.mem_union] at hy'
        rcases hy' with hy | hy
        · exact (Finset.mem_filter.mp hy).2
        · rcases Finset.mem_image.mp hy with ⟨uv, huv, rfl⟩
          have huv' := Finset.mem_filter.mp huv
          have huvLt := huv'.2
          have hd : 0 < a - f uv.1 := sub_pos.mpr huvLt.1
          have he : 0 < f uv.2 - a := sub_pos.mpr huvLt.2
          have hden : f uv.2 - f uv.1 = (a - f uv.1) + (f uv.2 - a) := by ring
          have hpoint : crossingPoint f a uv.1 uv.2 =
              ((f uv.2 - a) / ((a - f uv.1) + (f uv.2 - a))) • uv.1 +
                ((a - f uv.1) / ((a - f uv.1) + (f uv.2 - a))) • uv.2 := by
            unfold crossingPoint
            rw [hden]
          have hdenpos : 0 < (a - f uv.1) + (f uv.2 - a) := add_pos hd he
          have hfcross : f (crossingPoint f a uv.1 uv.2) = a := by
            rw [hpoint, map_add, map_smul, map_smul]
            simp only [smul_eq_mul]
            field_simp [ne_of_gt hdenpos]
            <;> ring
          change f (crossingPoint f a uv.1 uv.2) ≤ a
          rw [hfcross]
    exact ⟨convexHull_min hclip (convex_convexHull ℝ (s : Set E)) hx,
      (convexHull_min hclip_le (convex_halfSpace_le f.isLinear a)) hx⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FinitePolytopeHalfspaceClip
