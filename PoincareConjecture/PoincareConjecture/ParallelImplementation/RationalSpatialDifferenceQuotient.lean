import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
def spatialUnit (i : Fin 3) : E3 := EuclideanSpace.single i 1
def shiftPoint {T : ℝ} (p : Slab T) (i : Fin 3) (h : ℝ) : Slab T :=
  (p.1, p.2 + h • spatialUnit i)
def dqValue {T : ℝ} (z : FullJet T) (i : Fin 3) (h : ℝ) (p : Slab T) : E6 :=
  h⁻¹ • (z.1.1.1.1 (shiftPoint p i h) - z.1.1.1.1 p)
def dqGradient {T : ℝ} (z : FullJet T) (i : Fin 3) (h : ℝ)
    (p : Slab T) : E3 →L[ℝ] E6 :=
  h⁻¹ • (z.1.1.1.2.1 (shiftPoint p i h) - z.1.1.1.2.1 p)
def dqHessian {T : ℝ} (z : FullJet T) (i : Fin 3) (h : ℝ)
    (p : Slab T) : E3 →L[ℝ] E3 →L[ℝ] E6 :=
  h⁻¹ • (z.1.1.1.2.2 (shiftPoint p i h) - z.1.1.1.2.2 p)
def dqTime {T : ℝ} (z : FullJet T) (i : Fin 3) (h : ℝ) (p : Slab T) : E6 :=
  h⁻¹ • (z.1.2 (shiftPoint p i h) - z.1.2 p)
def dqTimeExtension {T : ℝ} (z : FullJet T) (i : Fin 3) (h : ℝ)
    (x : E3) (s : ℝ) : E6 := by
  classical
  exact if hs : s ∈ Set.Icc (0 : ℝ) T then dqValue z i h (⟨s, hs⟩, x) else 0
def spatialTrace (H : E3 →L[ℝ] E3 →L[ℝ] E6) : E6 :=
  ∑ a : Fin 3, H (spatialUnit a) (spatialUnit a)
def principalPart (A : E3 →L[ℝ] E3) (H : E3 →L[ℝ] E3 →L[ℝ] E6) : E6 :=
  ∑ a : Fin 3, ∑ c : Fin 3, (A (spatialUnit c)) a • H (spatialUnit a) (spatialUnit c)
theorem rational_spatial_difference_quotient_equation
    (T alpha : ℝ)
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (B : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ]
      (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6)
    (z : FullJet T)
    (hz : z.1.1 ∈ parabolicC2HolderSet T alpha)
    (hzt : (z.1.1.1.1, z.1.2) ∈ slabTimeDerivativeGraph T)
    (b : Slab T → E3 →L[ℝ] E3)
    (hinv : ∀ p : Slab T, (1 + E (z.1.1.1.1 p)) * b p = 1 ∧
      b p * (1 + E (z.1.1.1.1 p)) = 1)
    (heq : ∀ p : Slab T, z.1.2 p - spatialTrace (z.1.1.1.2.2 p) =
      principalPart (b p - 1) (z.1.1.1.2.2 p) +
        B (b p) (b p) (z.1.1.1.2.1 p) (z.1.1.1.2.1 p))
    (i : Fin 3) (h : ℝ) (hh : h ≠ 0) :
    (∀ t : Set.Icc (0 : ℝ) T, ∀ x : E3,
      HasFDerivAt (fun y : E3 => dqValue z i h (t, y))
        (dqGradient z i h (t, x)) x) ∧
    (∀ t : Set.Icc (0 : ℝ) T, ∀ x : E3,
      HasFDerivAt (fun y : E3 => dqGradient z i h (t, y))
        (dqHessian z i h (t, x)) x) ∧
    (∀ t : Set.Icc (0 : ℝ) T, 0 < (t : ℝ) → (t : ℝ) < T → ∀ x : E3,
      HasDerivAt (dqTimeExtension z i h x) (dqTime z i h (t, x)) (t : ℝ)) ∧
    (∀ p : Slab T,
      let ps := shiftPoint p i h
      let R := -(b ps * E (dqValue z i h p) * b p)
      h⁻¹ • (b ps - b p) = R ∧
      dqTime z i h p - spatialTrace (dqHessian z i h p) =
        principalPart (b ps - 1) (dqHessian z i h p) +
        principalPart R (z.1.1.1.2.2 p) +
        B R (b ps) (z.1.1.1.2.1 ps) (z.1.1.1.2.1 ps) +
        B (b p) R (z.1.1.1.2.1 ps) (z.1.1.1.2.1 ps) +
        B (b p) (b p) (dqGradient z i h p) (z.1.1.1.2.1 ps) +
        B (b p) (b p) (z.1.1.1.2.1 p) (dqGradient z i h p)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hspace : z.1.1.1 ∈ spaceTimeC2JetSet T := hz.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    let c : E3 := h • spatialUnit i
    have hjet := hspace t
    have htrans₁ : HasFDerivAt (fun y : E3 => z.1.1.1.1 (t, y + c))
        (z.1.1.1.2.1 (t, x + c)) x := by
      have hinner : HasFDerivAt (fun y : E3 => c + y)
          (ContinuousLinearMap.id ℝ E3) x := by
        simpa using (hasFDerivAt_id x).const_add c
      have h := HasFDerivAt.comp (f := fun y : E3 => c + y) (x := x)
        (hjet.1 (c + x)) hinner
      simpa [Function.comp_def, add_comm, ContinuousLinearMap.comp_id] using h
    have hbase : HasFDerivAt (fun y : E3 => z.1.1.1.1 (t, y))
        (z.1.1.1.2.1 (t, x)) x := hjet.1 x
    change HasFDerivAt
      (fun y : E3 => h⁻¹ • (z.1.1.1.1 (t, y + h • spatialUnit i) -
        z.1.1.1.1 (t, y)))
      (h⁻¹ • (z.1.1.1.2.1 (t, x + h • spatialUnit i) -
        z.1.1.1.2.1 (t, x))) x
    exact (htrans₁.sub hbase).const_smul h⁻¹
  · intro t x
    let c : E3 := h • spatialUnit i
    have hjet := hspace t
    have htrans₂ : HasFDerivAt (fun y : E3 => z.1.1.1.2.1 (t, y + c))
        (z.1.1.1.2.2 (t, x + c)) x := by
      have hinner : HasFDerivAt (fun y : E3 => c + y)
          (ContinuousLinearMap.id ℝ E3) x := by
        simpa using (hasFDerivAt_id x).const_add c
      have h := HasFDerivAt.comp (f := fun y : E3 => c + y) (x := x)
        (hjet.2 (c + x)) hinner
      simpa [Function.comp_def, add_comm, ContinuousLinearMap.comp_id] using h
    have hbase : HasFDerivAt (fun y : E3 => z.1.1.1.2.1 (t, y))
        (z.1.1.1.2.2 (t, x)) x := hjet.2 x
    change HasFDerivAt
      (fun y : E3 => h⁻¹ • (z.1.1.1.2.1 (t, y + h • spatialUnit i) -
        z.1.1.1.2.1 (t, y)))
      (h⁻¹ • (z.1.1.1.2.2 (t, x + h • spatialUnit i) -
        z.1.1.1.2.2 (t, x))) x
    exact (htrans₂.sub hbase).const_smul h⁻¹
  · intro t ht0 htT x
    let c : E3 := h • spatialUnit i
    have hshift := hzt t ht0 htT (x + c)
    have hbase := hzt t ht0 htT x
    have htimeEq : (fun s : ℝ => dqTimeExtension z i h x s) =
        fun s => h⁻¹ • (timeExtension z.1.1.1.1 (x + c) s -
          timeExtension z.1.1.1.1 x s) := by
      funext s
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · simp [dqTimeExtension, dqValue, shiftPoint, timeExtension, c, hs]
      · simp [dqTimeExtension, timeExtension, hs]
    have hdiff := (hshift.sub hbase).const_smul h⁻¹
    change HasDerivAt (fun s : ℝ => h⁻¹ •
      (timeExtension z.1.1.1.1 (x + c) s - timeExtension z.1.1.1.1 x s))
      (h⁻¹ • (z.1.2 (t, x + c) - z.1.2 (t, x))) (t : ℝ) at hdiff
    simpa only [htimeEq, dqTime, shiftPoint, c] using hdiff
  · intro p
    dsimp only
    let ps : Slab T := shiftPoint p i h
    let u : Slab T → E6 := fun q => z.1.1.1.1 q
    let G : Slab T → (E3 →L[ℝ] E6) := fun q => z.1.1.1.2.1 q
    let H : Slab T → (E3 →L[ℝ] E3 →L[ℝ] E6) := fun q => z.1.1.1.2.2 q
    let bp := b p
    let bs := b ps
    let R : E3 →L[ℝ] E3 := -(bs * E (dqValue z i h p) * bp)
    have hbdiff : bs - bp = -(bs * E (u ps - u p) * bp) := by
      have hp := hinv p
      have hs := hinv ps
      have hbaseA : (1 + E (u p)) * bp = 1 := by simpa [u, bp] using hp.1
      have hshiftA : bs * (1 + E (u ps)) = 1 := by simpa [u, bs] using hs.2
      calc
        bs - bp = bs * ((1 + E (u p)) * bp) -
            (bs * (1 + E (u ps))) * bp := by
              rw [hbaseA, hshiftA]
              simp
        _ = bs * (((1 + E (u p)) * bp) - ((1 + E (u ps)) * bp)) := by
              simp only [mul_assoc]
              rw [← mul_sub]
        _ = bs * (((1 + E (u p)) - (1 + E (u ps))) * bp) := by
              rw [← sub_mul]
        _ = -(bs * E (u ps - u p) * bp) := by
              rw [map_sub]
              noncomm_ring
    have hinverseDiff : h⁻¹ • (bs - bp) = R := by
      have hdelta : dqValue z i h p = h⁻¹ • (u ps - u p) := by
        simp [dqValue, shiftPoint, u, ps]
      have hEdelta : E (dqValue z i h p) = h⁻¹ • E (u ps - u p) := by
        rw [hdelta, map_smul]
      dsimp [R]
      rw [hbdiff, hEdelta]
      simp [smul_neg, mul_assoc, smul_mul_assoc]
    refine ⟨hinverseDiff, ?_⟩
    have hprincipal (A A' : E3 →L[ℝ] E3)
        (K K' : E3 →L[ℝ] E3 →L[ℝ] E6) :
        principalPart A K - principalPart A' K' =
          principalPart A (K - K') + principalPart (A - A') K' := by
      unfold principalPart
      simp [ContinuousLinearMap.sub_apply, sub_smul, smul_sub,
        Finset.sum_sub_distrib]
    have hB (a a' : E3 →L[ℝ] E3) (g g' : E3 →L[ℝ] E6) :
        B a a g g - B a' a' g' g' =
          B (a - a') a g g + B a' (a - a') g g +
            B a' a' (g - g') g + B a' a' g' (g - g') := by
      simp only [map_sub, sub_apply, add_apply, smul_apply]
      abel
    have hHquot : dqHessian z i h p = h⁻¹ • (H ps - H p) := by
      simp [dqHessian, shiftPoint, ps, H]
    have hGquot : dqGradient z i h p = h⁻¹ • (G ps - G p) := by
      simp [dqGradient, shiftPoint, ps, G]
    have hPsmulR (r : ℝ) (A : E3 →L[ℝ] E3)
        (K : E3 →L[ℝ] E3 →L[ℝ] E6) :
        principalPart A (r • K) = r • principalPart A K := by
      simp [principalPart, Finset.smul_sum, smul_apply, smul_smul,
        mul_comm, mul_left_comm, mul_assoc]
    have hPsmulL (r : ℝ) (A : E3 →L[ℝ] E3)
        (K : E3 →L[ℝ] E3 →L[ℝ] E6) :
        principalPart (r • A) K = r • principalPart A K := by
      simp [principalPart, Finset.smul_sum, smul_apply, smul_smul,
        mul_comm, mul_left_comm, mul_assoc]
    have hBsmul1 (r : ℝ) (a a' : E3 →L[ℝ] E3)
        (g g' : E3 →L[ℝ] E6) :
        B (r • a) a' g g' = r • B a a' g g' := by
      simp only [map_smul, smul_apply]
    have hBsmul2 (r : ℝ) (a a' : E3 →L[ℝ] E3)
        (g g' : E3 →L[ℝ] E6) :
        B a (r • a') g g' = r • B a a' g g' := by
      simp only [map_smul, smul_apply]
    have hBsmul3 (r : ℝ) (a a' : E3 →L[ℝ] E3)
        (g g' : E3 →L[ℝ] E6) :
        B a a' (r • g) g' = r • B a a' g g' := by
      simp only [map_smul, smul_apply]
    have hBsmul4 (r : ℝ) (a a' : E3 →L[ℝ] E3)
        (g g' : E3 →L[ℝ] E6) :
        B a a' g (r • g') = r • B a a' g g' := by
      simp only [map_smul, smul_apply]
    have hPscaled :
        h⁻¹ • (principalPart (bs - 1) (H ps) -
          principalPart (bp - 1) (H p)) =
          principalPart (bs - 1) (dqHessian z i h p) +
            principalPart R (H p) := by
      rw [hprincipal, smul_add, ← hPsmulR, ← hPsmulL]
      have hcoeff : (bs - 1) - (bp - 1) = bs - bp := by abel
      rw [hHquot, hcoeff, hinverseDiff]
    have hBscaled :
        h⁻¹ • (B bs bs (G ps) (G ps) - B bp bp (G p) (G p)) =
          B R bs (G ps) (G ps) + B bp R (G ps) (G ps) +
            B bp bp (dqGradient z i h p) (G ps) +
            B bp bp (G p) (dqGradient z i h p) := by
      rw [hB, smul_add, smul_add, smul_add]
      rw [← hBsmul1, ← hBsmul2, ← hBsmul3, ← hBsmul4]
      rw [hinverseDiff, hGquot]
    have htime := heq ps
    have htime0 := heq p
    have hEqdiff :
        (z.1.2 ps - spatialTrace (H ps)) - (z.1.2 p - spatialTrace (H p)) =
          (principalPart (bs - 1) (H ps) - principalPart (bp - 1) (H p)) +
          (B bs bs (G ps) (G ps) - B bp bp (G p) (G p)) := by
      rw [htime, htime0]
      abel
    have hmain :
        h⁻¹ • ((z.1.2 ps - spatialTrace (H ps)) -
          (z.1.2 p - spatialTrace (H p))) =
          principalPart (bs - 1) (dqHessian z i h p) +
          principalPart R (H p) +
          B R bs (G ps) (G ps) + B bp R (G ps) (G ps) +
          B bp bp (dqGradient z i h p) (G ps) +
          B bp bp (G p) (dqGradient z i h p) := by
      rw [hEqdiff, smul_add, hPscaled, hBscaled]
      abel
    have htrace : spatialTrace (dqHessian z i h p) =
        h⁻¹ • (spatialTrace (H ps) - spatialTrace (H p)) := by
      rw [hHquot]
      simp [spatialTrace, Finset.smul_sum, Finset.sum_sub_distrib,
        smul_sub, smul_apply]
    have hleft : dqTime z i h p - spatialTrace (dqHessian z i h p) =
        h⁻¹ • ((z.1.2 ps - spatialTrace (H ps)) -
          (z.1.2 p - spatialTrace (H p))) := by
      rw [htrace]
      simp only [dqTime, shiftPoint, ps, smul_sub]
      abel
    simpa [R, bp, bs, G, H, ps] using hleft.trans hmain
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
