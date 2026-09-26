import PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FinitePolytopeConeCover
open scoped BigOperators
/-- Cover an actual finite polytope by cones from its exact centroid over
proper exposed faces. No boundary-cover or radial-exit certificate is assumed. -/
theorem convexHull_covered_by_centroid_face_cones
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (s : Finset E) (hs : s.Nonempty) :
    let b : E := ((s.card : ℝ)⁻¹) • ∑ v ∈ s, v
    ∀ x ∈ convexHull ℝ (s : Set E),
      ∃ t : Finset E, t ⊆ s ∧
        IsExposed ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set E)) ∧
        convexHull ℝ (t : Set E) ≠ convexHull ℝ (s : Set E) ∧
        x ∈ convexHull ℝ (↑(insert b t) : Set E) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp only
  intro x hx
  let K : Set E := convexHull ℝ (s : Set E)
  let b : E := ((s.card : ℝ)⁻¹) • ∑ v ∈ s, v
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_pos.ne'
  obtain ⟨p, hpS⟩ := hs.exists_mem
  have hbK : b ∈ K := by
    rw [Finset.mem_convexHull']
    refine ⟨fun _ => (s.card : ℝ)⁻¹, ?_, ?_, ?_⟩
    · intro v hv
      positivity
    · simp [Finset.sum_const, hcard]
    · simp [b, Finset.smul_sum]
  by_cases hxb : x = b
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_, ?_⟩
    · simpa using (isExposed_empty (A := K))
    · intro hEq
      have hpK : p ∈ K := subset_convexHull ℝ _ hpS
      have hKempty : K = (∅ : Set E) := by
        have : (∅ : Set E) = K := by simpa [K] using hEq
        exact this.symm
      rw [hKempty] at hpK
      simpa using hpK
    · rw [hxb]
      exact subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
  · let A : AffineSubspace ℝ E := affineSpan ℝ (s : Set E)
    have hpA : p ∈ A := subset_affineSpan ℝ _ hpS
    let pA : A := ⟨p, hpA⟩
    letI : Nonempty A := ⟨pA⟩
    letI : Nonempty (s : Set E) := ⟨p, hpS⟩
    let inc : A →ᵃ[ℝ] E := A.subtype
    let SA : Set A := inc ⁻¹' (s : Set E)
    have hSAimg : inc '' SA = (s : Set E) := by
      ext v
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hv
        exact ⟨⟨v, subset_affineSpan ℝ _ hv⟩, hv, rfl⟩
    let ψ : A ≃ᵃⁱ[ℝ] A.direction := AffineIsometryEquiv.constVSub ℝ pA
    have hSAspan : affineSpan ℝ SA = ⊤ := by
      simpa [SA, A, inc] using
        (affineSpan_coe_preimage_eq_top (k := ℝ) (A := (s : Set E)))
    let SD : Set A.direction := ψ '' SA
    have hspanImage : affineSpan ℝ SD = ⊤ := by
      calc
        affineSpan ℝ SD = (affineSpan ℝ SA).map ψ.toAffineEquiv.toAffineMap :=
          (AffineSubspace.map_span ψ.toAffineEquiv.toAffineMap SA).symm
        _ = ⊤ := by
          rw [hSAspan, AffineMap.map_top_of_surjective _ ψ.surjective]
    have hSAfinite : SA.Finite :=
      Set.Finite.preimage (Set.injOn_of_injective A.subtype_injective) s.finite_toSet
    have hSDfinite : SD.Finite := hSAfinite.image ψ
    let qE : A.direction →ᵃ[ℝ] E := inc.comp ψ.symm.toAffineEquiv.toAffineMap
    have hqψ (z : A) : qE (ψ z) = inc z := by simp [qE]
    have hqEinj : Function.Injective qE := by
      intro z z' hzz'
      apply ψ.symm.injective
      exact A.subtype_injective hzz'
    have hSDimg : qE '' SD = (s : Set E) := by
      ext v
      constructor
      · rintro ⟨z, ⟨a, ha, rfl⟩, hz⟩
        rw [hqψ] at hz
        change inc a ∈ (s : Set E) at ha
        exact hz ▸ ha
      · intro hv
        let a : A := ⟨v, subset_affineSpan ℝ _ hv⟩
        refine ⟨ψ a, ⟨a, ?_, rfl⟩, ?_⟩
        · change inc a ∈ (s : Set E)
          exact hv
        · rw [hqψ]
          rfl
    let C : Set A.direction := convexHull ℝ SD
    have hCeq : C = convexHull ℝ (ψ '' SA) := rfl
    have hCcompact : IsCompact C := hSDfinite.isCompact_convexHull ℝ
    have hCconv : Convex ℝ C := convex_convexHull ℝ SD
    have hCimg : qE '' C = K := by
      change qE '' convexHull ℝ SD = K
      rw [qE.image_convexHull, hSDimg]
    have hCpre (z : A.direction) : z ∈ C ↔ qE z ∈ K := by
      constructor
      · intro hz
        have : qE z ∈ qE '' C := ⟨z, hz, rfl⟩
        rw [hCimg] at this
        exact this
      · intro hz
        have : qE z ∈ qE '' C := by rw [hCimg]; exact hz
        rcases this with ⟨z', hz', hzz'⟩
        have : z' = z := hqEinj hzz'
        simpa [this] using hz'
    have hCspan : affineSpan ℝ C = ⊤ := by
      change affineSpan ℝ (convexHull ℝ SD) = ⊤
      rw [affineSpan_convexHull]
      exact hspanImage
    have hCint : (interior C).Nonempty :=
      hCconv.interior_nonempty_iff_affineSpan_eq_top.mpr hCspan
    have hKspan : K ⊆ (A : Set E) := by
      simpa [K, A] using (convexHull_subset_affineSpan (s : Set E))
    let xA : A := ⟨x, hKspan hx⟩
    let bA : A := ⟨b, hKspan hbK⟩
    let xC : A.direction := ψ xA
    let bC : A.direction := ψ bA
    have hqx : qE xC = x := by
      change qE (ψ xA) = x
      rw [hqψ]
      rfl
    have hqb : qE bC = b := by
      change qE (ψ bA) = b
      rw [hqψ]
      rfl
    have hxC : xC ∈ C := (hCpre xC).2 (hqx ▸ hx)
    have hbC : bC ∈ C := (hCpre bC).2 (hqb ▸ hbK)
    have hxbC : xC ≠ bC := by
      intro he
      apply hxb
      have hA : xA = bA := ψ.injective he
      calc
        x = (xA : E) := rfl
        _ = (bA : E) := congrArg (fun z : A => (z : E)) hA
        _ = b := rfl
    have hbCint : bC ∈ interior C := by
      by_contra hbnot
      obtain ⟨f, hfne, hfmax⟩ :=
        geometric_hahn_banach_of_nonempty_interior_point hCconv hbnot hCint
      let vA : {v : E // v ∈ (s : Set E)} → A := fun v =>
        ⟨v.1, subset_affineSpan ℝ _ v.2⟩
      have hsumAttach (g : E → E) :
          (∑ v : {v : E // v ∈ s}, g v.1) = ∑ v ∈ s, g v := by
        simpa only [Finset.attach_eq_univ] using (Finset.sum_attach s g)
      have hsumAttachR (g : E → ℝ) :
          (∑ v : {v : E // v ∈ s}, g v.1) = ∑ v ∈ s, g v := by
        simpa only [Finset.attach_eq_univ] using (Finset.sum_attach s g)
      have hsumc : ∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ = 1 := by
        rw [hsumAttachR (fun _ : E => (s.card : ℝ)⁻¹)]
        simp [Finset.sum_const, hcard]
      have hsumcoeff : ∑ v ∈ s, (s.card : ℝ)⁻¹ = 1 := by
        calc
          _ = ∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ :=
            (hsumAttachR (fun _ : E => (s.card : ℝ)⁻¹)).symm
          _ = 1 := hsumc
      have hψb : bC = ∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ • ψ (vA v) := by
        apply Subtype.ext
        have hvec :
            p - b = ∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ • (p - v.1) := by
          rw [hsumAttach (fun v : E => (s.card : ℝ)⁻¹ • (p - v))]
          dsimp [b]
          simp_rw [smul_sub]
          rw [Finset.sum_sub_distrib]
          rw [← Finset.sum_smul, ← Finset.smul_sum, hsumcoeff, one_smul]
        simpa [bC, bA, pA, vA, ψ, AffineIsometryEquiv.coe_constVSub,
          vsub_eq_sub] using hvec
      have havg :
          (∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ * f (ψ (vA v))) = f bC := by
        calc
          _ = f (∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ • ψ (vA v)) := by simp
          _ = f bC := congrArg f hψb.symm
      have hterm : ∀ v : {v : E // v ∈ s},
          0 ≤ (s.card : ℝ)⁻¹ * (f bC - f (ψ (vA v))) := by
        intro v
        apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        apply sub_nonneg.mpr
        apply hfmax
        have hvA : vA v ∈ SA := by
          change (v.1 : E) ∈ s
          exact v.2
        exact subset_convexHull ℝ SD ⟨vA v, hvA, rfl⟩
      have hzero :
          ∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ * (f bC - f (ψ (vA v))) = 0 := by
        calc
          _ = ∑ v : {v : E // v ∈ s},
              ((s.card : ℝ)⁻¹ * f bC - (s.card : ℝ)⁻¹ * f (ψ (vA v))) := by
                apply Finset.sum_congr rfl
                intro v hv
                ring
          _ = (∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ * f bC) -
              ∑ v : {v : E // v ∈ s}, (s.card : ℝ)⁻¹ * f (ψ (vA v)) := by
                simpa using (Finset.sum_sub_distrib
                  (s := (Finset.univ : Finset {v : E // v ∈ s}))
                  (fun v : {v : E // v ∈ s} => (s.card : ℝ)⁻¹ * f bC)
                  (fun v => (s.card : ℝ)⁻¹ * f (ψ (vA v))))
          _ = 0 := by
            rw [← Finset.sum_mul, hsumc, havg]
            ring
      have htermzero := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hterm v)).1 hzero
      have hval (v : {v : E // v ∈ s}) : f (ψ (vA v)) = f bC := by
        have hm := htermzero v (Finset.mem_univ v)
        rcases mul_eq_zero.mp hm with hc | hv
        · exact (inv_ne_zero hcard hc).elim
        · linarith
      have hfb : f bC = 0 := by
        have hpval := hval ⟨p, hpS⟩
        have hψp : ψ (vA ⟨p, hpS⟩) = 0 := by
          apply Subtype.ext
          simp [vA, ψ, AffineIsometryEquiv.coe_constVSub, pA, vsub_eq_sub]
        rw [hψp] at hpval
        simpa using hpval.symm
      have hvertices : ∀ v : {v : E // v ∈ s}, f (ψ (vA v)) = 0 := by
        intro v
        rw [hval v, hfb]
      have hCker : C ⊆ {z : A.direction | f z = 0} := by
        rw [hCeq]
        apply convexHull_min
        · rintro z ⟨v, hv, rfl⟩
          have hvS : (v : E) ∈ s := by simpa [SA, inc] using hv
          have hvA : vA ⟨v, hvS⟩ = v := by apply Subtype.ext; rfl
          rw [← hvA]
          exact hvertices ⟨v, hvS⟩
        · exact convex_hyperplane
            ⟨fun z w => map_add f.toLinearMap z w,
              fun c z => map_smul f.toLinearMap c z⟩ 0
      have hkerSpan :
          affineSpan ℝ C ≤ f.toLinearMap.ker.toAffineSubspace := by
        apply affineSpan_le.2
        intro z hz
        change f z = 0
        exact hCker hz
      have htop : (⊤ : AffineSubspace ℝ A.direction) ≤
          f.toLinearMap.ker.toAffineSubspace := by
        rw [← hCspan]
        exact hkerSpan
      have hfzero : f = 0 := by
        ext z
        have hz : z ∈ f.toLinearMap.ker := by
          have hz' : z ∈ (f.toLinearMap.ker.toAffineSubspace : Set A.direction) :=
            htop (Set.mem_univ z)
          simpa using hz'
        exact LinearMap.mem_ker.mp hz
      exact hfne hfzero
    have hd : (xC - bC : A.direction) ≠ 0 := sub_ne_zero.mpr hxbC
    obtain ⟨q₀, hq₀norm, hq₀d⟩ :=
      exists_dual_vector ℝ (xC - bC) (norm_ne_zero_iff.mpr hd)
    let q : StrongDual ℝ A.direction := ‖xC - bC‖⁻¹ • q₀
    have hqd : q (xC - bC) = 1 := by
      change ‖xC - bC‖⁻¹ * q₀ (xC - bC) = 1
      rw [hq₀d]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd)
    let Lline : AffineSubspace ℝ A.direction :=
      affineSpan ℝ ({bC, xC} : Set A.direction)
    have hLclosed : IsClosed (Lline : Set A.direction) := Lline.closed_of_finiteDimensional
    let Sline : Set A.direction := C ∩ (Lline : Set A.direction)
    have hSlinecompact : IsCompact Sline := hCcompact.inter_right hLclosed
    have hSlinene : Sline.Nonempty :=
      ⟨xC, hxC, right_mem_affineSpan_pair ℝ bC xC⟩
    obtain ⟨yC, hySline, hymax⟩ :=
      hSlinecompact.exists_isMaxOn hSlinene q.continuous.continuousOn
    have hqline (t : ℝ) : q (AffineMap.lineMap bC xC t) = q bC + t := by
      simp only [AffineMap.lineMap_apply_module', map_add, map_smul, smul_eq_mul, hqd]
      ring
    rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (p := yC) (p₁ := bC) (p₂ := xC)).1
        hySline.2 with ⟨u, huy⟩
    have hu : u = q yC - q bC := by
      have hqeq := congrArg q huy
      rw [hqline] at hqeq
      linarith
    let lam : ℝ := q yC - q bC
    have hyRay : AffineMap.lineMap bC xC lam = yC := by
      have hLamU : lam = u := by
        dsimp [lam]
        exact hu.symm
      rw [hLamU]
      exact huy
    have hlam : 1 ≤ lam := by
      have hmx := (isMaxOn_iff.mp hymax) xC
        ⟨hxC, right_mem_affineSpan_pair ℝ bC xC⟩
      have hqxdiff : q xC - q bC = 1 := by
        have h := hqd
        rw [map_sub] at h
        linarith
      dsimp [lam]
      linarith
    have hyNotInt : yC ∉ interior C := by
      intro hyint
      let ray : ℝ → A.direction := fun t => AffineMap.lineMap bC xC t
      have hUopen : IsOpen (ray ⁻¹' interior C) :=
        isOpen_interior.preimage (by fun_prop)
      have hlamU : lam ∈ ray ⁻¹' interior C := by
        change ray lam ∈ interior C
        dsimp [ray]
        rw [hyRay]
        exact hyint
      obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hUopen lam hlamU
      let t' : ℝ := lam + min 1 (ε / 2)
      have htBall' : dist t' lam < ε := by
        dsimp [t']
        have hmin0 : 0 ≤ min (1 : ℝ) (ε / 2) :=
          le_min (by norm_num) (by positivity)
        rw [Real.dist_eq]
        have hdiff : lam + min (1 : ℝ) (ε / 2) - lam = min 1 (ε / 2) := by abel
        rw [hdiff, abs_of_nonneg hmin0]
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have htC : AffineMap.lineMap bC xC t' ∈ interior C := hεball htBall'
      have hlt : lam < t' := by
        dsimp [t']
        have hmin : 0 < min 1 (ε / 2) :=
          lt_min (by norm_num) (by linarith)
        linarith
      have htLine : AffineMap.lineMap bC xC t' ∈ Sline := by
        refine ⟨interior_subset htC, ?_⟩
        exact AffineMap.lineMap_mem_affineSpan_pair t' bC xC
      have htmax := (isMaxOn_iff.mp hymax) _ htLine
      have hqY : q yC = q bC + lam := by
        calc
          q yC = q (AffineMap.lineMap bC xC lam) := congrArg q hyRay.symm
          _ = q bC + lam := hqline lam
      rw [hqline t', hqY] at htmax
      linarith
    obtain ⟨f, hfne, hfmax⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hCconv hyNotInt hCint
    let gD : StrongDual ℝ A.direction := -f
    obtain ⟨ell, hell⟩ := StrongDual.exists_extension A.direction gD
    let yA : A := ψ.symm yC
    have hyA : yA = AffineMap.lineMap bA xA lam := by
      calc
        yA = ψ.symm (AffineMap.lineMap bC xC lam) := by rw [hyRay]
        _ = AffineMap.lineMap (ψ.symm bC) (ψ.symm xC) lam :=
          ψ.symm.toAffineEquiv.apply_lineMap bC xC lam
        _ = AffineMap.lineMap bA xA lam := by simp [bC, xC]
    have hyE : (yA : E) = AffineMap.lineMap b x lam := by
      calc
        (yA : E) = inc yA := rfl
        _ = inc (AffineMap.lineMap bA xA lam) := congrArg inc hyA
        _ = AffineMap.lineMap b x lam := by
          simpa [inc, bA, xA] using inc.apply_lineMap bA xA lam
    have hyK : (yA : E) ∈ K := by
      have hyCmem : yC ∈ C := hySline.1
      have hqEy : qE yC = (yA : E) := by
        rw [← (show ψ yA = yC by simp [yA])]
        exact hqψ yA
      rw [← hqEy]
      exact (hCpre yC).1 hyCmem
    have hspanD (k : K) : (k : E) - p ∈ A.direction := by
      simpa [vsub_eq_sub] using A.vsub_mem_direction (hKspan k.2) hpA
    have hellPoint (k : E) (hk : k ∈ K) :
        ell k = f (ψ ⟨k, hKspan hk⟩) + ell p := by
      have hmem := hspanD ⟨k, hk⟩
      have hψ : ψ ⟨k, hKspan hk⟩ = -⟨k - p, hmem⟩ := by
        apply Subtype.ext
        simp [ψ, pA, vsub_eq_sub]
      have hdiff : ell (k - p) = f (ψ ⟨k, hKspan hk⟩) := by
        calc
          ell (k - p) = (-f) ⟨k - p, hmem⟩ := hell ⟨k - p, hmem⟩
          _ = f (-⟨k - p, hmem⟩) := by simp
          _ = f (ψ ⟨k, hKspan hk⟩) := by rw [← hψ]
      calc
        ell k = ell ((k - p) + p) := congrArg ell (sub_add_cancel k p).symm
        _ = ell (k - p) + ell p := map_add ell (k - p) p
        _ = f (ψ ⟨k, hKspan hk⟩) + ell p := by rw [hdiff]
    have hyEll : ell (yA : E) = f yC + ell p := by
      have hψy : ψ yA = yC := by simp [yA]
      rw [hellPoint (yA : E) hyK, hψy]
    have hellmax : ∀ k ∈ K, ell k ≤ ell (yA : E) := by
      intro k hk
      rw [hellPoint k hk, hyEll]
      have hkC : ψ ⟨k, hKspan hk⟩ ∈ C := by
        apply (hCpre _).2
        rw [hqψ]
        exact hk
      have h := hfmax _ hkC
      linarith
    let F : Set E := ell.toExposed K
    have hFexposed : IsExposed ℝ K F :=
      ContinuousLinearMap.toExposed.isExposed (l := ell) (A := K)
    have hyF : (yA : E) ∈ F := ⟨hyK, fun z hz => hellmax z hz⟩
    obtain ⟨hgen, _⟩ :=
      PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces.exposed_faces_are_finitely_generated s
    obtain ⟨t, ht, hFt⟩ := hgen F hFexposed
    have hFproper : convexHull ℝ (t : Set E) ≠ K := by
      intro hEq
      have hFK : F = K := hFt.trans hEq
      have hpEll : ell p = ell (yA : E) := by
        have hpF : p ∈ F := hFK.symm ▸ subset_convexHull ℝ _ hpS
        have hmaxp := hpF.2 (yA : E) hyK
        have hmaxy := hellmax p (subset_convexHull ℝ _ hpS)
        linarith
      let vA : {v : E // v ∈ (s : Set E)} → A := fun v =>
        ⟨v.1, subset_affineSpan ℝ _ v.2⟩
      have hvertices : ∀ v : {v : E // v ∈ s}, f (ψ (vA v)) = 0 := by
        intro v
        have hvK : (v : E) ∈ K := subset_convexHull ℝ _ v.2
        have hvF : (v : E) ∈ F := by rw [hFK]; exact hvK
        have hmaxv := hvF.2 (yA : E) hyK
        have hmaxy := hellmax (v : E) hvK
        have heq : ell (v : E) = ell (yA : E) := le_antisymm hmaxy hmaxv
        have hval := hellPoint (v : E) hvK
        rw [hpEll] at hval
        linarith
      have hCker : C ⊆ {z : A.direction | f z = 0} := by
        rw [hCeq]
        apply convexHull_min
        · rintro z ⟨a, ha, rfl⟩
          have haS : (a : E) ∈ s := by simpa [SA, inc] using ha
          have hvA : vA ⟨a, haS⟩ = a := by apply Subtype.ext; rfl
          rw [← hvA]
          exact hvertices ⟨a, haS⟩
        · exact convex_hyperplane
            ⟨fun z w => map_add f.toLinearMap z w,
              fun c z => map_smul f.toLinearMap c z⟩ 0
      have hkerSpan :
          affineSpan ℝ C ≤ f.toLinearMap.ker.toAffineSubspace := by
        apply affineSpan_le.2
        intro z hz
        change f z = 0
        exact hCker hz
      have htop : (⊤ : AffineSubspace ℝ A.direction) ≤
          f.toLinearMap.ker.toAffineSubspace := by
        rw [← hCspan]
        exact hkerSpan
      have hfzero : f = 0 := by
        ext z
        have hz : z ∈ f.toLinearMap.ker := by
          have hz' : z ∈ (f.toLinearMap.ker.toAffineSubspace : Set A.direction) :=
            htop (Set.mem_univ z)
          simpa using hz'
        exact LinearMap.mem_ker.mp hz
      exact hfne hfzero
    have hFhull : IsExposed ℝ K (convexHull ℝ (t : Set E)) := by
      simpa [F, hFt] using hFexposed
    have hyHull : (yA : E) ∈ convexHull ℝ (insert b (t : Set E)) := by
      have hyT : (yA : E) ∈ convexHull ℝ (t : Set E) := by
        rw [← hFt]
        exact hyF
      exact (convexHull_mono (by
        intro z hz
        exact Set.mem_insert_of_mem b hz)) hyT
    have hbHull : b ∈ convexHull ℝ (insert b (t : Set E)) :=
      subset_convexHull ℝ _ (Set.mem_insert_iff.mpr (Or.inl rfl))
    have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
    have hrho : lam⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact inv_nonneg.mpr hlampos.le
      · exact inv_le_one_of_one_le₀ hlam
    have hxLine : AffineMap.lineMap b (yA : E) lam⁻¹ = x := by
      rw [AffineMap.lineMap_apply_module', hyE, AffineMap.lineMap_apply_module']
      have hl : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hlampos.ne'
      have hl' : lam⁻¹ * lam = 1 := by rw [mul_comm]; exact hl
      rw [add_sub_cancel_right]
      rw [smul_smul, hl', one_smul, sub_add_cancel]
    have hxHull : x ∈ convexHull ℝ (insert b (t : Set E)) := by
      rw [← hxLine]
      exact (convex_convexHull ℝ (insert b (t : Set E))).lineMap_mem hbHull hyHull hrho
    exact ⟨t, ht, hFhull, hFproper, by simpa [b] using hxHull⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FinitePolytopeConeCover
