import YM.OPE.Compatible.Tune.Lw
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {i j m:ℕ}{μ:ℝ}{U:Jewel E→ₗ[ℝ] Jewel E}{V:ℕ→ ΦB E}{k:E≃ₗ[ℝ] F}
lemma honestTrans (p:E≃ₗ[ℝ] F)(Q:Jewel E≃ₗ[ℝ] Jewel F)(X:Jewel E≃ₗ[ℝ] Jewel E) (h:Honest Q p)(hx:Honest X (LinearEquiv.refl ℝ E)): Honest (X.trans Q) p:=by
      constructor<;>intro u<;> simp only[LinearEquiv.trans_apply,h.comm,hx.comm,h.earns,hx.earns]; rfl
-- gauge θ ≔ Id+τ M.
noncomputable abbrev vary (M:E→ₗ[ℝ] E):Jewel E→ₗ[ℝ] Jewel E:=(τΓ E).comp (jewelMap M)
noncomputable def LoopΘ (M:E→ₗ[ℝ] E) : Jewel E ≃ₗ[ℝ] Jewel E := by
     let T:= vary M; have ht(x:Jewel E):T (T (T x))=0:=by
         funext i; fin_cases i; · rfl
         · exact map_zero M
         change M (M 0)=_; rw [map_zero,map_zero]; rfl
     exact { LinearMap.id+T with invFun:=fun x=>x-T x+T (T x),
                                  left_inv:=fun x=>by change x+T x-T (x+T x)+T (T (x+T x))=x; rw [T.map_add,map_add,ht]; abel,
                                  right_inv:=fun x=>by change x-T x+T (T x)+ T (x-T x+T (T x))=x; rw [map_add,T.map_sub,ht]; abel }
lemma loopApply (M:E→ₗ[ℝ] E)(x:Jewel E): LoopΘ M x=x+vary M x:=rfl
lemma honestLoop (M:E→ₗ[ℝ] E) : Honest (LoopΘ M) (LinearEquiv.refl ℝ E):=by
     refine ⟨fun x=>?_,fun x=>?_⟩
     · rw [loopApply,loopApply,map_add]; unfold vary; simp_rw [LinearMap.comp_apply,JMic]
     rw [loopApply,Pi.add_apply]; exact add_zero _
-- `T1sym` correcting diag metric
lemma lEt (P:Artπ E)(h: ∀ x:E,x≠0→0<P x x) [FiniteDimensional ℝ E]: Function.Bijective P:=by
     have hi: Injective P:=fun x y hp=>by
         by_contra hv; have ht: P (x-y)=0:=by rw [map_sub,hp,sub_self]
         exact (ne_of_gt (h _ (sub_ne_zero.mpr hv))) (LinearMap.congr_fun ht (x-y))
     exact ⟨hi,LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hi).trans (Subspace.dual_finrank_eq ..).symm))⟩
-- compression.G Harg
lemma Job.top (p:ΦB E)(h:Job p)(x y:Jewel E):p 0 x y=p 0 (τ₀ E (x 0)) (τ₀ E (y 0)):=Metricζ (p 0) h.nil x y
abbrev originω (p:Artπ (Jewel E)):Artπ E:= LinearMap.compl₂ (p.comp (τ₀ E)) (τ₀ E)
-- choose linear correction
lemma curvature (p:ΦB E)(h:Job p)(hz:∀ x:E,x≠0→0<p 0 (τ₀ E x) (τ₀ E x))(hp:∀ i x y,p i x y=p i y x) [FiniteDimensional ℝ E]:∃ M:E→ₗ[ℝ] E,∀ x y:E,p 1 (LoopΘ M (τ₀ E x)) (LoopΘ M (τ₀ E y))=0:=by
      let B:=LinearEquiv.ofBijective (originω (p 0)) (lEt (originω (p 0)) hz); let M:=B.symm.toLinearMap.comp (((-1/2:ℝ)) • originω (p 1)); have hx(x y:E): p 0 (τ₀ E (M x)) (τ₀ E y)=(-1/2)*p 1 (τ₀ E x) (τ₀ E y):=by
         have ht:B (M x)= ((-1/2:ℝ)) • (originω (p 1)) x:=B.apply_symm_apply _; exact LinearMap.congr_fun ht _
      refine ⟨M,fun x y=>?_⟩; have hh(x y:E): p 1 (vary M (τ₀ E x)) (τ₀ E y)=(-1/2)*p 1 (τ₀ E x) (τ₀ E y):=by unfold vary; rw [LinearMap.comp_apply, (h.one ..).1,h.top,τat y,show (jewelMap M) _ 0=M x from (by change M (τ₀ E x 0)=M x;rw[τat]),hx]; -- perhaps simp mismatch
      have he: p 1 (vary M (τ₀ E x)) (vary M (τ₀ E y))=0 := ((h.one ..).1).trans ((h.nil ..).2)
      simp only [loopApply,map_add,LinearMap.add_apply]; rw [he,hp 1 (τ₀ E x) (vary M (τ₀ E y)),hh,hh,hp 1 (τ₀ E y)]; ring
end YM.OPE.Hark
