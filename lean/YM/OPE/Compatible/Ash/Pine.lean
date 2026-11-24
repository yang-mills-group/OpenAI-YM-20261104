import YM.OPE.Compatible.Ash.Spare
/-!
# Compact bounded oscillatory test under Richardson
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric
open Pert.Band
open scoped BigOperators Classical ContDiff
variable {E M:Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup M][NormedSpace ℝ M]{s t:ℝ}{i k:ℕ}
abbrev vet (s:ℝ)(k:ℕ)(g:ℝ→E→M) (x:ℝ)(z:E):= chill s k (fun u=>g u z) x
lemma vet_silk (hs:1 ≤ s){t x:ℝ}{g:ℝ→E→M}{z:E}(H:∀ u∈Icc 0 t,ContDiffAt ℝ ∞ (Function.uncurry g) (u,z)) (hx:x∈ Icc 0 t):ContDiffAt ℝ ∞ (vet s k g x) z:=by
    induction k generalizing x with
    | zero=> exact (H x hx).comp z (f:=fun y=>(x,y)) (contDiffAt_const.prodMk contDiffAt_id)
    | succ k ih=> exact (ih hx).sub ((ih (starMem hs hx)).const_smul (s^k))
lemma vet_conv (hs:1 ≤ s){t x:ℝ}{g:ℝ→E→M}{z:E}(H:∀ u∈ Icc 0 t,ContDiffAt ℝ ∞ (Function.uncurry g) (u,z)) (hx:x∈ Icc 0 t): fderiv ℝ (vet s k g x) z= vet s k (fun u y=> fderiv ℝ (g u) y) x z:=by
   induction k generalizing x with
   | zero=> rfl
   | succ k ih=>
      change fderiv ℝ (vet s k g x - s^k • vet s k g (x/s)) z=_ -- maybe Pi.sub etc
      erw [fderiv_sub ((vet_silk (k:=k) hs H hx).differentiableAt (by simp)) (((vet_silk (k:=k) hs H (starMem hs hx)).const_smul (s^k)).differentiableAt (by simp)), fderiv_const_smul ((vet_silk hs H (starMem hs hx)).differentiableAt (by simp)), ih (starMem hs hx), ih hx]; rfl
lemma vet_price {s t:ℝ}(hs:1 ≤ s){X:Set E4}(hp:IsCompact X)(i k:ℕ){M:Type}[NormedAddCommGroup M][NormedSpace ℝ M]{g:ℝ→E4→M} (H:∀ x∈Icc 0 t,∀ z, ContDiffAt ℝ ∞ (Function.uncurry g) (x,z)):∃ C≥0,∀ z∈ X,∀ x∈Icc 0 t, ‖iteratedFDeriv ℝ i (vet s k g x) z‖ ≤ x^k*C:=by
    induction i generalizing M with
    | zero=> simpa only [norm_iteratedFDeriv_zero] using! (snow (k:=k) hs hp (fun p hh=> H p.1 hh.1 _))
    | succ i ih=>
      let f(u:ℝ):=fderiv ℝ (g u)
      have hh : ∀ x∈Icc 0 t, ∀ z, ContDiffAt ℝ ∞ (Function.uncurry f) (x,z):=by
        intro u hu z; let F : (ℝ×E4)→ E4→M:=fun v x=> g v.1 x; have hp:= (H u hu z).comp (f:=fun p:(ℝ×E4)×E4=>(p.1.1,p.2)) ((u,z),z) (contDiffAt_fst.fst.prodMk contDiffAt_snd); exact ContDiffAt.fderiv (f:=F) (g:=Prod.snd) hp (contDiffAt_snd (𝕜:=ℝ)) (by simp)
      obtain ⟨C,hC,A⟩:= ih hh
      refine ⟨C,hC,fun z hz x hx=>?_⟩
      rw [←norm_iteratedFDeriv_fderiv, show fderiv ℝ (vet s k g x)=vet s k f x from funext fun y=> vet_conv hs (fun u hu=> H u hu y) hx]; exact A z hz x hx
end YM.OPE.Balsam
