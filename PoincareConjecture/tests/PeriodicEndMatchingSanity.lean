import PoincareConjecture

open Set Bundle Manifold
open PoincareConjecture.Topology.FiberSaturation SmoothBundle
open scoped Manifold ContDiff
noncomputable section

/-- A concrete ordinary product chart. -/
def periodicTestChart (F : Type*) [TopologicalSpace F] :
    Trivialization F (Prod.fst : ℝ × F → ℝ) where
  toOpenPartialHomeomorph := (Homeomorph.refl (ℝ × F)).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := by simp
  proj_toFun _ _ := rfl

theorem periodicTestChart_smooth {W G F : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace G]
    [TopologicalSpace F] [ChartedSpace G F] (J : ModelWithCorners ℝ W G) :
    IsSmoothTrivialization ((𝓘(ℝ,ℝ)).prod J) J (periodicTestChart F) :=
  ⟨contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩

/-- This deck transformation has a genuinely time-dependent fiber shear. -/
def periodicShearDeck : (ℝ × ℝ) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ),
    (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)⟯ (ℝ × ℝ) where
  toFun z := (z.1+4,z.2+z.1)
  invFun z := (z.1-4,z.2-(z.1-4))
  left_inv z := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  contMDiff_toFun := (contMDiff_fst.add contMDiff_const).prodMk
    (contMDiff_snd.add contMDiff_fst)
  contMDiff_invFun := (contMDiff_fst.sub contMDiff_const).prodMk
    (contMDiff_snd.sub (contMDiff_fst.sub contMDiff_const))

-- The original product coordinates have no constant fiber transition
-- on ANY positive collar; the theorem must genuinely correct the chart.
example (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ δ : ℝ → ℝ, ∀ t ∈ Ioo (-ε) ε, ∀ x : ℝ,
      (periodicShearDeck (t,x)).2 = δ x := by
  rintro ⟨δ,h⟩
  have h0 := h 0 (by constructor <;> linarith) 0
  have h1 := h (ε/2) (by constructor <;> linarith) 0
  change 0+0 = δ 0 at h0
  change 0+ε/2 = δ 0 at h1
  linarith

-- Neither member of this local atlas covers the whole period [0,4].
theorem periodicTestLocalAtlas : ∀ t : ℝ,
    ∃ e : Trivialization ℝ (Prod.fst : ℝ × ℝ → ℝ), t ∈ e.baseSet ∧
      IsSmoothTrivialization ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) e := by
  intro t
  by_cases ht : t < 3
  · refine ⟨(periodicTestChart ℝ).restrOpen (Iio (3 : ℝ)) isOpen_Iio, ⟨mem_univ _,ht⟩,?_⟩
    exact isSmooth_restrOpen (periodicTestChart_smooth 𝓘(ℝ,ℝ)) _ _
  · refine ⟨(periodicTestChart ℝ).restrOpen (Ioi (1 : ℝ)) isOpen_Ioi, ⟨mem_univ _,?_⟩,?_⟩
    · change (1 : ℝ) < t
      linarith
    · exact isSmooth_restrOpen (periodicTestChart_smooth 𝓘(ℝ,ℝ)) _ _

-- Construct matching collars from genuine smooth local charts.
example : ∃ k : Trivialization ℝ (Prod.fst : ℝ × ℝ → ℝ),
    ∃ φ : ℝ ≃ₘ[ℝ] ℝ, ∃ ε : ℝ, 0 < ε ∧
      IsSmoothTrivialization ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) k ∧
      Icc (0 : ℝ) 4 ⊆ k.baseSet ∧
      ∀ x t, t ∈ Ioo (-ε) ε → k.toOpenPartialHomeomorph.symm (t+4,x) =
        periodicShearDeck (k.toOpenPartialHomeomorph.symm (t,φ x)) := by
  obtain ⟨k,φ,ε,hε,_,hk,hseg,_,_,hseam,_⟩ :=
    exists_smooth_endmatched_period_chart continuous_fst
      periodicTestLocalAtlas
      periodicShearDeck (by norm_num : (0 : ℝ) < 4) (fun _ => rfl)
  exact ⟨k,φ,ε,hε,hk,hseg,hseam⟩

-- Real sphere fibers retain their standard smooth structure.
example : ∃ k : Trivialization Sphere2 (Prod.fst : ℝ × Sphere2 → ℝ),
    ∃ φ : Sphere2 ≃ₘ⟮𝓡 2,𝓡 2⟯ Sphere2, ∃ ε : ℝ, 0 < ε ∧
      IsSmoothTrivialization ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) k ∧
      Icc (0 : ℝ) 4 ⊆ k.baseSet ∧
      ∀ x t, t ∈ Ioo (-ε) ε → k.toOpenPartialHomeomorph.symm (t+4,x) =
        ((realTranslation 4).prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞))
          (k.toOpenPartialHomeomorph.symm (t,φ x)) := by
  obtain ⟨k,φ,ε,hε,_,hk,hseg,_,_,hseam,_⟩ :=
    exists_smooth_endmatched_period_chart continuous_fst
      (fun t => ⟨periodicTestChart Sphere2,mem_univ _,periodicTestChart_smooth (𝓡 2)⟩)
      ((realTranslation 4).prodCongr (Diffeomorph.refl (𝓡 2) Sphere2 ∞))
      (by norm_num : (0 : ℝ) < 4) (fun _ => rfl)
  exact ⟨k,φ,ε,hε,hk,hseg,hseam⟩

-- A non-involutive fiber translation checks the inverse-twist convention.
example (x t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (periodicTestChart ℝ).toOpenPartialHomeomorph.symm (t+4,x) =
      ((realTranslation 4).prodCongr (realTranslation 3))
        ((periodicTestChart ℝ).toOpenPartialHomeomorph.symm
          (t,(realTranslation 3).symm x)) := by
  apply periodic_inverse_seam ((realTranslation 4).prodCongr (realTranslation 3))
    (realTranslation 3) (fun _ => rfl)
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) (fun _ _ => rfl) x ht

-- Replacing the inverse twist by the forward one is provably wrong.
example (x t : ℝ) : (t+4,x) ≠
    ((realTranslation 4).prodCongr (realTranslation 3)) (t,(realTranslation 3) x) := by
  intro h
  have hs := congrArg Prod.snd h
  change x = (x+3)+3 at hs
  linarith

-- Inverse-chart local smooth invertibility is a theorem, even at period endpoints.
example : IsLocalDiffeomorphAt ((𝓘(ℝ,ℝ)).prod (𝓡 2))
    ((𝓘(ℝ,ℝ)).prod (𝓡 2)) ∞ (periodicTestChart Sphere2).toOpenPartialHomeomorph.symm
      (4,Classical.choice (inferInstance : Nonempty Sphere2)) :=
  smooth_chart_inverse_localDiffeomorphAt (periodicTestChart_smooth (𝓡 2)) (mem_univ _) _
