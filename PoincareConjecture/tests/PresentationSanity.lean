import PoincareConjecture
import Mathlib.Topology.Instances.AddCircle.Real

open Set Function PoincareConjecture.Topology.FiberSaturation
open PoincareConjecture.Topology.FiberSaturation.MappingTorus
noncomputable section

/-- Independent presentation of the untwisted bundle as a product with the circle. -/
def productCirclePresentation (p : Sphere2 × ℝ) : Sphere2 × AddCircle (4 : ℝ) :=
  (p.1, p.2)

example : ∃ e : (Sphere2 × AddCircle (4 : ℝ)) ≃ₜ Space (Homeomorph.refl Sphere2).symm 4,
    ∀ p, e (productCirclePresentation p) = proj (Homeomorph.refl Sphere2).symm 4 p := by
  apply sphere_presentation_coordinates (Homeomorph.refl Sphere2) (by norm_num)
    productCirclePresentation Prod.snd
  · exact continuous_fst.prodMk ((AddCircle.continuous_mk' 4).comp continuous_snd)
  · exact continuous_snd
  · rintro ⟨x, z⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact ⟨(x, t), rfl⟩
  · intro p; rfl
  · intro t x y h
    exact congrArg Prod.fst h
  · intro x t
    change (x, ((t + 4 : ℝ) : AddCircle (4 : ℝ))) = (x, (t : AddCircle (4 : ℝ)))
    exact Prod.ext rfl (AddCircle.coe_add_period 4 t)

/-- A nonidentity sphere twist for the canonical-presentation regression. -/
def presentationAntipodal : Sphere2 ≃ₜ Sphere2 where
  toFun x := ⟨-x.1, by simp⟩
  invFun x := ⟨-x.1, by simp⟩
  left_inv x := by apply Subtype.ext; exact neg_neg x.1
  right_inv x := by apply Subtype.ext; exact neg_neg x.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

example : presentationHomeomorph presentationAntipodal 4
    (proj presentationAntipodal 4) (circleProjection presentationAntipodal 4)
    (circleProjection_proj presentationAntipodal 4)
    (proj_fiber_injective presentationAntipodal (by norm_num))
    (fun x t => period_endpoint_identification presentationAntipodal 4 t x)
    (proj_isOpenQuotientMap presentationAntipodal 4) =
      Homeomorph.refl (Space presentationAntipodal 4) :=
  canonical_presentationHomeomorph presentationAntipodal (by norm_num)

example (p : Sphere2 × ℝ) :
    proj presentationAntipodal 4 (deck presentationAntipodal 4 (-7) p) =
      proj presentationAntipodal 4 p :=
  presentation_deck_invariant presentationAntipodal 4 (proj presentationAntipodal 4)
    (fun x t => period_endpoint_identification presentationAntipodal 4 t x) (-7) p

-- Dropping fiber injectivity allows genuine extra identifications despite gluing.
example : ∀ (_ : Bool) (t : ℝ), ((t + 4 : ℝ) : AddCircle (4 : ℝ)) = t := by
  intro _ t
  exact AddCircle.coe_add_period 4 t

example : ¬ Injective (fun _ : Bool => ((0 : ℝ) : AddCircle (4 : ℝ))) := by
  intro h
  have hbad : false = true := h rfl
  cases hbad

-- The circle base detects extra wraps: half a period is not a whole period.
example : ¬ ((0 : ℝ) : AddCircle (4 : ℝ)) = ((2 : ℝ) : AddCircle (4 : ℝ)) := by
  rw [circle_eq_iff_integer_shift]
  rintro ⟨n, hn⟩
  have hn' : (n : ℝ) = 1/2 := by linarith
  have hlow : 0 < n := by exact_mod_cast (by linarith : (0 : ℝ) < n)
  have hhigh : n < 1 := by exact_mod_cast (by linarith : (n : ℝ) < 1)
  omega
