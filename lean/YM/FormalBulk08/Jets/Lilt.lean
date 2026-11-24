import YM.PertExtension.Uniform
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Position invariance for the Frechet ranks needed by gauge Jacobians, no
limits of representations involved. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Jets
open Function Filter Set Metric
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem smooth_top (f : E→F) (x a b : E) (n : ℕ) (m : Fin n→E) (h : ContDiffAt ℝ ((n+2:ℕ) : WithTop ℕ∞) f x) :
     iteratedFDeriv ℝ (n+2) f x (Fin.cons a (Fin.cons b m))= iteratedFDeriv ℝ (n+2) f x (Fin.cons b (Fin.cons a m)) := by
  let P:= iteratedFDeriv ℝ n f
  have hp : ContDiffAt ℝ 2 P x := h.iteratedFDeriv_right (by rw [add_comm]; norm_cast)
  have ht := hp.isSymmSndFDerivAt (by simp)
  let L:= (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1)=>E) F).symm
  have h' : DifferentiableAt ℝ (fderiv ℝ P) x := (hp.fderiv_right (m:=1) (by norm_num)).differentiableAt_one
  have he : fderiv ℝ (iteratedFDeriv ℝ (n+1) f) x=L.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ P) x) := by
     let Z : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) →L[ℝ] _ := L.toContinuousLinearEquiv.toContinuousLinearMap
     have he : HasFDerivAt Z Z (fderiv ℝ P x) := Z.hasFDerivAt
     have he' : HasFDerivAt (Z ∘ fderiv ℝ P) (Z.comp (fderiv ℝ (fderiv ℝ P) x)) x := by
       refine HasFDerivAt.comp (𝕜:=ℝ) (f:=fderiv ℝ P) (f':=fderiv ℝ (fderiv ℝ P) x) (g:= Z) (g':=Z) x ?_ ?_
       · exact he
       exact h'.hasFDerivAt
     rw [iteratedFDeriv_succ_eq_comp_left]; exact he'.fderiv
  simp only [iteratedFDeriv_succ_apply_left (n:=n+1), Fin.cons_zero,Fin.tail_cons, he,ContinuousLinearMap.comp_apply]
  change L (fderiv ℝ (fderiv ℝ P) x a) _ = L (fderiv ℝ (fderiv ℝ P) x b) _
  simp [L]; rw [ht a b]

private def cheek (n : ℕ) (i : Fin n) (a b : E) := Function.update (fun _ => a) i b
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma cheek_zero (n) (a b:E) : cheek (n+1) 0 a b = Fin.cons b (fun _=>a) := by
   ext1 j; refine Fin.cases ?_ ?_ j <;> simp [cheek]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma cheek_succ (n) (a b:E) (j : Fin n) : cheek (n+1) j.succ a b = Fin.cons a (cheek n j a b) := by
   ext1 i; refine Fin.cases ?_ (fun p=>?_) i
   · simp [cheek,Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
   by_cases h : p=j
   · rw [h];simp [cheek]
   simp [cheek,h]

private theorem cheek_head (f : E→F) (x : E) (n : ℕ) (h : ContDiffAt ℝ ((n+1:ℕ):WithTop ℕ∞) f x) (a b:E) (i : Fin (n+1)) :
    iteratedFDeriv ℝ (n+1) f x (cheek _ i a b)=iteratedFDeriv ℝ (n+1) f x (cheek _ 0 a b) := by
   induction n generalizing x with
   | zero=> congr 1; fin_cases i; rfl
   | succ n ih=>
     refine Fin.cases rfl (fun j=> ?_) i
     rw [cheek_succ]
     -- first walk up to second via IH on tail
     calc _ = iteratedFDeriv ℝ (n+1+1) f x (Fin.cons a (cheek (n+1) 0 a b)) := by
            have H : ∀ᶠ z in 𝓝 x, iteratedFDeriv ℝ (n+1) f z (cheek _ j a b)=iteratedFDeriv ℝ (n+1) f z (cheek _ 0 a b) := (h.eventually (by simp)).mono fun z hz => ih z (hz.of_le (by norm_cast; omega)) j
            have hh := h.differentiableAt_iteratedFDeriv (m:=n+1) (by norm_cast; omega)
            simp_rw [hh.iteratedFDeriv_succ_apply_left',Fin.tail_cons, Fin.cons_zero]; rw [Filter.EventuallyEq.fderiv_eq H]
          _ = _ := by
            have he : (fun _ : Fin (n+1)=> a) = Fin.cons a (fun _=>a) := funext fun i=> Fin.cases rfl (fun j=>by simp) i
            rw [cheek_zero,cheek_zero,smooth_top f x a b n _ h,he]

theorem cheek_pin (f : E→F) (n) (x a b:E) (i : Fin (n+1)) (h : ContDiffAt ℝ ((n+1 : ℕ):WithTop ℕ∞) f x) :
    iteratedFDeriv ℝ (n+1) f x (Function.update (fun _=>a) i b)= iteratedFDeriv ℝ n (fun y=> fderiv ℝ f y b) x (fun _=>a) := by
   change iteratedFDeriv ℝ (n+1) f x (cheek _ i a b)=_
   rw [cheek_head f x n h a b i, ←cheek_head f x n h a b (Fin.last _), iteratedFDeriv_succ_apply_right, show Fin.init _ = (fun _=>a) by ext i; simp [Fin.init,cheek],cheek, Function.update_self]
   have hf : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ f) x := h.fderiv_right (by norm_cast)
   obtain ⟨s,hs,hz,he⟩ := hf.contDiffOn' (m:=n) le_rfl (by simp)
   simp only [insert_eq_of_mem (mem_univ ..), univ_inter] at he
   rw [←iteratedFDerivWithin_of_isOpen n hs hz,←iteratedFDerivWithin_of_isOpen n hs hz]
   exact (iteratedFDerivWithin_clm_apply_const_apply (hs.uniqueDiffOn) he le_rfl hz).symm
end YM.FormalBulk08.Jets
