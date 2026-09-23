import Mathlib
import MorganTianLib.Ch01.CurvatureOperator
import PoincareConjecture.ParallelImplementation.MatrixComponentBound
set_option autoImplicit false
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace PoincareConjecture.ParallelImplementation.ExteriorCurvatureBound
/-- Component bounds control the actual curvature bilinear form on the exterior square. -/
theorem curvatureOperator_bound_of_components
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (d : ℕ) (b : OrthonormalBasis (Fin d) ℝ V)
    {B : V → V → V → V → ℝ} (hB : Riemannian.IsAlgCurvatureForm B)
    (C : ℝ) (hC : 0 ≤ C)
    (hcomp : ∀ i j k l, |B (b i) (b j) (b k) (b l)| ≤ C) :
    MorganTianLib.HasCurvatureOperatorNormLe hB ((d : ℝ)^2 * C) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let I := Set.powersetCard (Fin d) 2
  let e : Module.Basis I ℝ (⋀[ℝ]^2 V) := b.toBasis.exteriorPower 2
  let u (s : I) : Fin 2 ↪o Fin d := Set.powersetCard.ofFinEmbEquiv.symm s
  let v (s : I) : Fin 2 → V := fun k => b (u s k)
  have hv (s : I) : v s = ![b (u s 0), b (u s 1)] := by
    funext k
    fin_cases k <;> rfl
  have he (s : I) : e s = exteriorPower.ιMulti ℝ 2 (v s) := by
    change (b.toBasis.exteriorPower 2) s = _
    rw [exteriorPower.basis_apply]
    rfl
  have hpair (s t : I) (h0 : u s 0 = u t 0) (h1 : u s 1 = u t 1) : s = t := by
    apply Set.powersetCard.ofFinEmbEquiv.symm.injective
    ext k
    fin_cases k
    · simpa [u] using congrArg Fin.val h0
    · simpa [u] using congrArg Fin.val h1
  have hstrict (s : I) : u s 0 < u s 1 := by
    exact (u s).strictMono (by decide)
  have hdiag (s t : I) :
      (if u s 0 = u t 0 then (1 : ℝ) else 0) *
          (if u s 1 = u t 1 then 1 else 0) =
        if s = t then 1 else 0 := by
    by_cases hst : s = t
    · subst t
      simp
    · by_cases h00 : u s 0 = u t 0
      · by_cases h11 : u s 1 = u t 1
        · exact False.elim (hst (hpair s t h00 h11))
        · simp [h00, h11, hst]
      · simp [h00, hst]
  have hcross (s t : I) :
      ¬ (u s 0 = u t 1 ∧ u s 1 = u t 0) := by
    rintro ⟨h01, h10⟩
    have hs := hstrict s
    have ht := hstrict t
    rw [h01, h10] at hs
    exact (not_lt_of_ge (le_of_lt ht)) hs
  have hcrossZero (s t : I) :
      (if u s 1 = u t 0 then (1 : ℝ) else 0) *
          (if u s 0 = u t 1 then 1 else 0) = 0 := by
    by_cases h10 : u s 1 = u t 0
    · by_cases h01 : u s 0 = u t 1
      · exact False.elim (hcross s t ⟨h01, h10⟩)
      · simp [h10, h01]
    · simp [h10]
  have hwi (s t : I) :
      (MorganTianLib.wedgeInner (e s)) (e t) = if s = t then 1 else 0 := by
    rw [he s, he t, hv s, hv t, MorganTianLib.wedgeInner_ιMulti]
    simp only [Riemannian.stdCurvForm, b.inner_eq_ite]
    calc
      _ = (if s = t then 1 else 0) -
          ((if u s 1 = u t 0 then 1 else 0) *
            (if u s 0 = u t 1 then 1 else 0)) :=
        congrArg (fun z : ℝ => z -
          ((if u s 1 = u t 0 then 1 else 0) *
            (if u s 0 = u t 1 then 1 else 0))) (hdiag s t)
      _ = if s = t then 1 else 0 := by
        simpa using congrArg
          (fun z : ℝ => (if s = t then 1 else 0) - z) (hcrossZero s t)
  let Q := MorganTianLib.curvatureOperator hB
  let A : Matrix I I ℝ := fun s t => (Q (e s)) (e t)
  have hA : ∀ s t, |A s t| ≤ C := by
    intro s t
    simpa [A, Q, he s, he t, hv s, hv t,
      MorganTianLib.curvatureOperator_iMulti] using
      hcomp (u s 0) (u s 1) (u t 0) (u t 1)
  have hcard : Fintype.card I ≤ d ^ 2 := by
    calc
      Fintype.card I = Nat.card I := by simp
      _ = (Nat.card (Fin d)).choose 2 := Set.powersetCard.card (Fin d) 2
      _ = d.choose 2 := by simp
      _ ≤ d ^ 2 := Nat.choose_le_pow d 2
  intro φ
  let x : I → ℝ := fun s => e.repr φ s
  have hquad (D : (⋀[ℝ]^2 V) →ₗ[ℝ] (⋀[ℝ]^2 V) →ₗ[ℝ] ℝ) :
      (D φ) φ = ∑ s, ∑ t, x s * (D (e s)) (e t) * x t := by
    rw [← LinearMap.sum_repr_mul_repr_mul e e (B := D) φ φ]
    rw [Finsupp.sum_fintype (e.repr φ)
      (fun s a => (e.repr φ).sum (fun t c => a • c • ((D (e s)) (e t))))
      (by intro s; simp)]
    refine Finset.sum_congr rfl ?_
    intro s hs
    rw [Finsupp.sum_fintype (e.repr φ)
      (fun t c => (e.repr φ s) • c • ((D (e s)) (e t)))
      (by intro t; simp)]
    refine Finset.sum_congr rfl ?_
    intro t ht
    simp only [smul_eq_mul]
    dsimp [x]
    ring
  have hnorm :
      (MorganTianLib.wedgeInner φ) φ = ∑ s, (x s) ^ 2 := by
    calc
      (MorganTianLib.wedgeInner φ) φ =
          ∑ s, ∑ t, x s * (MorganTianLib.wedgeInner (e s)) (e t) * x t :=
        hquad MorganTianLib.wedgeInner
      _ = ∑ s, (x s) ^ 2 := by
        simp_rw [hwi]
        refine Finset.sum_congr rfl ?_
        intro s hs
        rw [Finset.sum_eq_single s]
        · simp only [if_true]
          ring
        · intro t ht hts
          simp [hts.symm]
        · simp
  have hcurv : (Q φ) φ = ∑ s, ∑ t, x s * A s t * x t := by
    simpa [A] using hquad Q
  rw [hcurv, hnorm]
  have hq :=
    PoincareConjecture.ParallelImplementation.IndependentAlgebra.quadratic_bound_of_entry_bound
      A C hC hA x
  have hsquares : 0 ≤ ∑ s, (x s) ^ 2 :=
    Finset.sum_nonneg fun s _ => sq_nonneg (x s)
  have hcoeff : (Fintype.card I : ℝ) * C ≤ (d : ℝ) ^ 2 * C := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC
  calc
    |∑ s, ∑ t, x s * A s t * x t|
        ≤ (Fintype.card I : ℝ) * C * (∑ s, (x s) ^ 2) := hq
    _ ≤ (d : ℝ) ^ 2 * C * (∑ s, (x s) ^ 2) :=
      mul_le_mul_of_nonneg_right hcoeff hsquares
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ExteriorCurvatureBound
