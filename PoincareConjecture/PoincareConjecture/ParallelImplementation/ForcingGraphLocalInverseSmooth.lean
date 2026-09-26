import PoincareConjecture.ParallelImplementation.BilinearResolventSmooth
import PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphLocalInverseSmooth
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped ContDiff Topology BoundedContinuousFunction
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
local instance (T : ℝ) : NormedAddCommGroup (ForcingJet A T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (ForcingJet A T) := inferInstance
local instance (T : ℝ) (X : Submodule ℝ (ForcingJet A T)) : NormedAddCommGroup X := inferInstance
local instance (T : ℝ) (X : Submodule ℝ (ForcingJet A T)) : NormedSpace ℝ X := inferInstance
/-- Actual local inversion on the SAME forcing graph near any existing
pointwise two-sided inverse. No smallness of the base input, smooth inverse,
or false submultiplicative graph norm is assumed. -/
theorem exists_smooth_local_forcing_inverse
    (T alpha : ℝ) (X : Submodule ℝ (ForcingJet A T))
    (hX : (X : Set (ForcingJet A T)) = forcingGraph A T alpha)
    [CompleteSpace X] (a b : X)
    (hb : ∀ p : Slab T,
      (1 - a.1.1 p) * b.1.1 p = 1 ∧ b.1.1 p * (1 - a.1.1 p) = 1) :
    ∃ I : X → X, I a = b ∧ ContDiffAt ℝ ∞ I a ∧
      ∀ᶠ x : X in 𝓝 a, ∀ p : Slab T,
        (1 - x.1.1 p) * (I x).1.1 p = 1 ∧
        (I x).1.1 p * (1 - x.1.1 p) = 1 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let B : A →L[ℝ] A →L[ℝ] A := ContinuousLinearMap.mul ℝ A
  have hBnorm : ‖B‖ ≤ 1 := by
    exact ContinuousLinearMap.opNorm_mul_le ℝ A
  have memGraph (u : X) : (u : ForcingJet A T) ∈ forcingGraph A T alpha := by
    rw [← hX]
    exact u.property
  let M (u : X) : ForcingJet A T →L[ℝ] ForcingJet A T :=
    Classical.choose
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha (u : ForcingJet A T) (memGraph u))
  have hM (u : X) :=
    Classical.choose_spec
      (PoincareConjecture.ParallelImplementation.ForcingGraphBilinearProduct.exists_forcing_bilinear_product
        B T alpha (u : ForcingJet A T) (memGraph u))
  let L (u : X) : X →L[ℝ] X :=
    ((M u).comp X.subtypeL).codRestrict X (by
      intro v
      have hv := (hM u).2.2.2 (v : ForcingJet A T) (memGraph v)
      change (M u (v : ForcingJet A T)) ∈ (X : Set (ForcingJet A T))
      rw [hX]
      exact hv)
  have hL_apply (u v : X) :
      ((L u) v : ForcingJet A T) = M u (v : ForcingJet A T) := by
    rfl
  let Llin : X →ₗ[ℝ] X →L[ℝ] X := {
    toFun := L
    map_add' := by
      intro u v
      apply ContinuousLinearMap.ext
      intro z
      apply Subtype.ext
      apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
        T alpha ((L (u + v)) z : ForcingJet A T)
        (((L u) z + (L v) z : X) : ForcingJet A T)
        (memGraph ((L (u + v)) z)) (memGraph ((L u) z + (L v) z))
      intro p
      change ((M (u + v)) (z : ForcingJet A T)).1 p =
        ((L u) z : ForcingJet A T).1 p + ((L v) z : ForcingJet A T).1 p
      rw [hL_apply, hL_apply,
        (hM (u + v)).2.1 (z : ForcingJet A T) p,
        (hM u).2.1 (z : ForcingJet A T) p,
        (hM v).2.1 (z : ForcingJet A T) p]
      simp [BoundedContinuousFunction.add_apply]
    map_smul' := by
      intro c u
      apply ContinuousLinearMap.ext
      intro z
      apply Subtype.ext
      apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
        T alpha ((L (c • u)) z : ForcingJet A T)
        (((c • L u) z : X) : ForcingJet A T)
        (memGraph ((L (c • u)) z)) (memGraph ((c • L u) z))
      intro p
      change ((M (c • u)) (z : ForcingJet A T)).1 p =
        c • ((L u) z : ForcingJet A T).1 p
      rw [hL_apply,
        (hM (c • u)).2.1 (z : ForcingJet A T) p,
        (hM u).2.1 (z : ForcingJet A T) p]
      simp [BoundedContinuousFunction.smul_apply]
  }
  have hLbound (u : X) : ‖L u‖ ≤ (2 * ‖B‖) * ‖u‖ := by
    apply ContinuousLinearMap.opNorm_le_bound (L u) (by positivity)
    intro v
    calc
      ‖(L u) v‖ = ‖((L u) v : ForcingJet A T)‖ := rfl
      _ = ‖(M u) (v : ForcingJet A T)‖ := by rw [hL_apply]
      _ ≤ ‖M u‖ * ‖(v : ForcingJet A T)‖ := (M u).le_opNorm _
      _ ≤ ((2 * ‖B‖) * ‖u‖) * ‖v‖ := by
        have hmu : ‖M u‖ ≤ 2 * ‖B‖ * ‖u‖ := by simpa [M] using (hM u).1
        have h := mul_le_mul_of_nonneg_right hmu
          (norm_nonneg (v : ForcingJet A T))
        simpa [mul_assoc] using h
  let Lclm : X →L[ℝ] X →L[ℝ] X :=
    Llin.mkContinuous (2 * ‖B‖) (by
      intro u
      change ‖L u‖ ≤ (2 * ‖B‖) * ‖u‖
      exact hLbound u)
  have Lclm_apply (u : X) : Lclm u = L u := by
    rfl
  let prodX (u v : X) : X := L u v
  have hprod_val (u v : X) (p : Slab T) :
      ((prodX u v : X) : ForcingJet A T).1 p =
        ((u : ForcingJet A T).1 p) * ((v : ForcingJet A T).1 p) := by
    change ((M u) (v : ForcingJet A T)).1 p = _
    exact (hM u).2.1 (v : ForcingJet A T) p
  have prod_add_left (u v z : X) :
      prodX (u + v) z = prodX u z + prodX v z := by
    change (Llin (u + v)) z = (Llin u) z + (Llin v) z
    rw [map_add]
    simp only [add_apply]
  have prod_sub_left (u v z : X) :
      prodX (u - v) z = prodX u z - prodX v z := by
    change (Llin (u - v)) z = (Llin u) z - (Llin v) z
    rw [map_sub]
    simp only [sub_apply]
  have prod_add_right (u v z : X) :
      prodX u (v + z) = prodX u v + prodX u z := by
    change (L u) (v + z) = (L u) v + (L u) z
    exact (L u).map_add v z
  have prod_sub_right (u v z : X) :
      prodX u (v - z) = prodX u v - prodX u z := by
    change (L u) (v - z) = (L u) v - (L u) z
    exact (L u).map_sub v z
  have prod_assoc (u v z : X) :
      prodX (prodX u v) z = prodX u (prodX v z) := by
    apply Subtype.ext
    apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha ((prodX (prodX u v) z : X) : ForcingJet A T)
      ((prodX u (prodX v z) : X) : ForcingJet A T)
      (memGraph (prodX (prodX u v) z)) (memGraph (prodX u (prodX v z)))
    intro p
    simpa only [hprod_val] using
      (mul_assoc ((u : ForcingJet A T).1 p) ((v : ForcingJet A T).1 p)
        ((z : ForcingJet A T).1 p))
  let oneJet : ForcingJet A T := (1, 0)
  have honeGraph : oneJet ∈ forcingGraph A T alpha := by
    intro p
    simp [oneJet]
  let oneX : X := ⟨oneJet, by
    change oneJet ∈ (X : Set (ForcingJet A T))
    rw [hX]
    exact honeGraph⟩
  have prod_one_left (u : X) : prodX oneX u = u := by
    apply Subtype.ext
    apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha ((prodX oneX u : X) : ForcingJet A T) (u : ForcingJet A T)
      (memGraph (prodX oneX u)) (memGraph u)
    intro p
    simp [hprod_val, oneX, oneJet]
  have prod_one_right (u : X) : prodX u oneX = u := by
    apply Subtype.ext
    apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha ((prodX u oneX : X) : ForcingJet A T) (u : ForcingJet A T)
      (memGraph (prodX u oneX)) (memGraph u)
    intro p
    simp [hprod_val, oneX, oneJet]
  have hbaseL : prodX (oneX - a) b = oneX := by
    apply Subtype.ext
    apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha ((prodX (oneX - a) b : X) : ForcingJet A T) (oneX : ForcingJet A T)
      (memGraph (prodX (oneX - a) b)) (memGraph oneX)
    intro p
    simpa [hprod_val, oneX, oneJet] using (hb p).1
  have hbaseR : prodX b (oneX - a) = oneX := by
    apply Subtype.ext
    apply PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
      T alpha ((prodX b (oneX - a) : X) : ForcingJet A T) (oneX : ForcingJet A T)
      (memGraph (prodX b (oneX - a))) (memGraph oneX)
    intro p
    simpa [hprod_val, oneX, oneJet] using (hb p).2
  let m : X →L[ℝ] X →L[ℝ] X :=
    (ContinuousLinearMap.compL ℝ X X X (L b)).comp Lclm
  have hm_apply (d z : X) : m d z = prodX b (prodX d z) := by
    change (L b) ((Lclm d) z) = _
    rw [Lclm_apply]
  let good : Set X := {d | ‖m d‖ < 1}
  have hgoodOpen : IsOpen good := by
    dsimp [good]
    exact isOpen_lt (by fun_prop) continuous_const
  have hzeroGood : (0 : X) ∈ good := by
    simp [good, m]
  obtain ⟨w, hwSmooth, hwSpec⟩ :=
    PoincareConjecture.ParallelImplementation.BilinearResolventSmooth.exists_smooth_bilinear_resolvent
      m b
  have hwzero : w 0 = b := by
    have h := (hwSpec 0 hzeroGood).1
    simpa [m] using h
  let I : X → X := fun x => w (x - a)
  have hIbase : I a = b := by
    simp [I, hwzero]
  have hWsmooth : ContDiffAt ℝ ∞ w 0 :=
    hwSmooth.contDiffAt (hgoodOpen.mem_nhds hzeroGood)
  have hshift : ContDiffAt ℝ ∞ (fun x : X => x - a) a := by
    fun_prop
  have hIsmooth : ContDiffAt ℝ ∞ I a := by
    change ContDiffAt ℝ ∞ (fun x : X => w (x - a)) a
    have hWsmooth' : ContDiffAt ℝ ∞ w (a - a) := by simpa using hWsmooth
    exact ContDiffAt.comp (f := fun x : X => x - a) (g := w)
      a hWsmooth' hshift
  have hgoodNear : IsOpen {x : X | ‖m (x - a)‖ < 1} := by
    exact isOpen_lt (by fun_prop) continuous_const
  have hgoodAt (x : X) (hx : ‖m (x - a)‖ < 1) : (x - a) ∈ good := hx
  have hleftAt (x : X) (hx : ‖m (x - a)‖ < 1) :
      prodX (oneX - x) (I x) = oneX := by
    let d : X := x - a
    have hxa : x = a + d := by
      dsimp [d]
      abel
    have hsub : oneX - x = (oneX - a) - d := by
      rw [hxa]
      abel
    have hfix : I x = b + prodX b (prodX d (I x)) := by
      have h := (hwSpec d (hgoodAt x (by simpa [d, I] using hx))).1
      simpa [I, hm_apply] using h
    calc
      prodX (oneX - x) (I x) = prodX ((oneX - a) - d) (I x) := by rw [hsub]
      _ = prodX (oneX - a) (I x) - prodX d (I x) := prod_sub_left _ _ _
      _ = prodX (oneX - a) (b + prodX b (prodX d (I x))) - prodX d (I x) := by
        rw [show prodX (oneX - a) (I x) =
          prodX (oneX - a) (b + prodX b (prodX d (I x))) from
            congrArg (fun q : X => prodX (oneX - a) q) hfix]
      _ = prodX (oneX - a) b + prodX (oneX - a) (prodX b (prodX d (I x))) -
          prodX d (I x) := by rw [prod_add_right]
      _ = oneX + prodX d (I x) - prodX d (I x) := by
        rw [← prod_assoc, hbaseL, prod_one_left]
      _ = oneX := by abel
  have hinjective (x : X) (hx : ‖m (x - a)‖ < 1) :
      Function.Injective (fun z : X => prodX (oneX - x) z) := by
    let d : X := x - a
    have hsub : oneX - x = (oneX - a) - d := by
      have hxa : x = a + d := by dsimp [d]; abel
      rw [hxa]
      abel
    intro y z hyz
    let t : X := y - z
    have hker : prodX (oneX - x) t = 0 := by
      have hyz' : prodX (oneX - x) y = prodX (oneX - x) z := by
        simpa using hyz
      dsimp [t]
      rw [prod_sub_right (oneX - x) y z, hyz']
      abel
    have hbt : prodX b (prodX (oneX - x) t) = 0 := by
      rw [hker]
      change (L b) (0 : X) = 0
      exact (L b).map_zero
    have hcontract : t = m d t := by
      have hcalc : prodX b (prodX (oneX - x) t) = t - m d t := by
        calc
          prodX b (prodX (oneX - x) t) = prodX (prodX b (oneX - x)) t := by
            rw [← prod_assoc b (oneX - x) t]
          _ = prodX (prodX b ((oneX - a) - d)) t := by rw [hsub]
          _ = prodX (prodX b (oneX - a) - prodX b d) t := by
            rw [prod_sub_right b (oneX - a) d]
          _ = prodX (prodX b (oneX - a)) t - prodX (prodX b d) t := by
            rw [prod_sub_left (prodX b (oneX - a)) (prodX b d) t]
          _ = prodX oneX t - prodX (prodX b d) t := by rw [hbaseR]
          _ = t - prodX b (prodX d t) := by rw [prod_one_left, prod_assoc]
          _ = t - m d t := by rw [hm_apply]
      have hzero : t - m d t = 0 := by
        calc
          t - m d t = prodX b (prodX (oneX - x) t) := hcalc.symm
          _ = 0 := hbt
      exact sub_eq_zero.mp hzero
    have hnorm : ‖t‖ = 0 := by
      have hle : ‖t‖ ≤ ‖m d‖ * ‖t‖ := by
        calc
          ‖t‖ = ‖m d t‖ := congrArg norm hcontract
          _ ≤ ‖m d‖ * ‖t‖ := (m d).le_opNorm t
      have hx' : ‖m d‖ < 1 := by simpa [d] using hx
      nlinarith [norm_nonneg t, norm_nonneg (m d)]
    have ht : t = 0 := norm_eq_zero.mp hnorm
    have hyz' : y - z = 0 := by simpa [t] using ht
    exact sub_eq_zero.mp hyz'
  have hrightAt (x : X) (hx : ‖m (x - a)‖ < 1) :
      prodX (I x) (oneX - x) = oneX := by
    apply hinjective x hx
    calc
      prodX (oneX - x) (prodX (I x) (oneX - x)) =
          prodX (prodX (oneX - x) (I x)) (oneX - x) := by
            rw [← prod_assoc (oneX - x) (I x) (oneX - x)]
      _ = prodX oneX (oneX - x) := by rw [hleftAt x hx]
      _ = prodX (oneX - x) oneX := by rw [prod_one_left, prod_one_right]
  refine ⟨I, hIbase, hIsmooth, ?_⟩
  have hIeventually : ∀ᶠ x : X in 𝓝 a, ‖m (x - a)‖ < 1 := by
    filter_upwards [hgoodNear.mem_nhds (by simp)] with x hx
    exact hx
  filter_upwards [hIeventually] with x hx
  intro p
  constructor
  · have h := congrArg (fun z : X => (z : ForcingJet A T).1 p) (hleftAt x hx)
    simpa [prodX, hprod_val, oneX, oneJet, mul_sub] using h
  · have h := congrArg (fun z : X => (z : ForcingJet A T).1 p) (hrightAt x hx)
    simpa [prodX, hprod_val, oneX, oneJet, mul_sub] using h
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphLocalInverseSmooth
