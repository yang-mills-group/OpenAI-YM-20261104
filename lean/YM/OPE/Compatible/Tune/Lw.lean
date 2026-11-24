import YM.OPE.Compatible.Tune.Shine
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
-- sym no /2
noncomputable abbrev Tot (f:Artπ E):Artπ E:=f+f.flip
lemma symEq (B:Artπ E)(x y:E):Tot B x y=B x y+B y x:=rfl
lemma symmTran (B:Artπ E)(x y:E):Tot B x y=Tot B y x:=by simp_rw[symEq];ring
lemma ampW (h:Svet V U μ): Svet (fun x i=>Tot (V x i)) U μ:=by
      refine ⟨⟨?_,?_,?_⟩, ?_, h.capT,h.slip,?_,?_⟩
      · intro x y; simp only [symEq,(h.drum.nil ..).1,(h.drum.nil ..).2,add_zero,and_self]
      · intro x y; simp only [symEq,(h.drum.one ..).1,(h.drum.one ..).2,and_self]
      · intro x y; simp only [symEq,(h.drum.two ..).1,(h.drum.two ..).2,and_self]
      · intro i t x y; simp only[symEq,h.fuel]
      · intro x y; rw[symEq,symEq,h.winds,h.winds,mul_add]
      intro x hx; rw[symEq]; exact add_pos (h.earn x hx) (h.earn x hx)
noncomputable def τequi (P:E≃ₗ[ℝ] F):Jewel E≃ₗ[ℝ] Jewel F:={ jewelMap P.toLinearMap with invFun := jewelMap P.symm.toLinearMap,right_inv :=fun _=> funext fun _=> P.apply_symm_apply _,left_inv:=fun _=> funext fun _=> P.symm_apply_apply _ }
structure Honest (f:Jewel E≃ₗ[ℝ] Jewel F)(k:E≃ₗ[ℝ] F):Prop where
      comm (x:Jewel E): f (τΓ E x)=τΓ F (f x)
      earns(x:Jewel E):f x 0=k (x 0)
variable {f:Jewel E≃ₗ[ℝ] Jewel F}
lemma Honest.inv (H:Honest f k): Honest f.symm k.symm:=by
      refine ⟨fun x=> f.injective (by rw [f.apply_symm_apply,H.comm,f.apply_symm_apply]),fun x=> k.injective (by rw [← H.earns,k.apply_symm_apply,f.apply_symm_apply])⟩
lemma Honest.track (H:Honest f k){W:Jewel F≃ₗ[ℝ] Jewel E}{p:F≃ₗ[ℝ] E}(H':Honest W p): Honest (f.trans W) (k.trans p):=by
      refine ⟨fun x=>?_,fun x=>?_⟩ <;> simp only [LinearEquiv.trans_apply,H.comm,H'.comm,H.earns,H'.earns]
lemma Honest.τ (P:E≃ₗ[ℝ] F): Honest (τequi P) P:=⟨fun x=>(JMic _ x).symm,fun _=>rfl⟩
noncomputable def Jug (f:Jewel E≃ₗ[ℝ] Jewel F)(U:ΦB E):ΦB F:= fun i=> ((U i).comp f.symm.toLinearMap).compl₂ f.symm.toLinearMap
noncomputable def Kw (f:Jewel E≃ₗ[ℝ] Jewel F)(X:Jewel E→ₗ[ℝ] Jewel E): Jewel F→ₗ[ℝ] Jewel F:= f.toLinearMap.comp (X.comp f.symm.toLinearMap)
lemma JugEq (X:ΦB E)(i:Fin 3)(x y:Jewel F): Jug f X i x y=X i (f.symm x) (f.symm y):=rfl
lemma KwRun (X:Jewel E→ₗ[ℝ] Jewel E)(x:Jewel F):Kw f X x=f (X (f.symm x)):=rfl
lemma Honest.live (H:Honest f k)(Z:Svet V U μ):Svet (fun i=> Jug f (V i)) (Kw f U) μ:=by
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · constructor <;> intro x y <;> simp_rw [JugEq, H.inv.comm] <;> first| exact Z.drum.nil ..| exact Z.drum.one .. | exact Z.drum.two ..
      · intro j t x y; simp_rw [JugEq,KwRun,f.symm_apply_apply]; exact Z.fuel ..
      · intro x; rw[KwRun,H.earns,Z.capT,k.map_smul,H.inv.earns,k.apply_symm_apply]
      · intro x; rw [KwRun,KwRun,H.inv.comm,Z.slip,H.comm]
      · intro p q; simp_rw [JugEq,KwRun,f.symm_apply_apply]; exact Z.winds ..
      intro x hx
      have ht: (Pi.single 0 x : Jewel F)=τ₀ _ x:= rfl; rw [ht,JugEq,Metricζ (V 0 0) Z.drum.nil,H.inv.earns,τat]; exact Z.earn _ ((k.symm.map_ne_zero_iff).2 hx)
end YM.OPE.Hark
