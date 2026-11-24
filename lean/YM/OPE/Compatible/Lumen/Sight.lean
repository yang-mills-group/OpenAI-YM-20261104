import YM.OPE.Compatible.Chain.Cove
/-!
# Dime from all lids in any Score chart. Allows degree-one ambient comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics
attribute [local instance] Gauge.frobInner
namespace Score.Stand
variable {K V D:Type}{B:Set V}{S:Score D V} [Group K]
variable (T:S.Stand B)
abbrev splitSet (u:D→K): T.Stable→K:=fun i=>u i.val
def setMove (p:T.Stable→K) : V→K:= T.sweep (T.cite p 1)
def crust (p:T.Stable→K)(x:T.Free→K):D→K:= S.dress (T.setMove p)⁻¹ (T.cite 1 x)
lemma crust_split (p:T.Stable→K)(s:T.Free→K): T.splitSet (T.crust p s)=p:=by
     funext i; unfold crust; let b:=T.cite p 1; let g:=T.setMove p; have hb: (T.sweep b)=g:=rfl
     have he:S.dress g⁻¹ (S.dress g b)=b:= by rw [S.dandy,inv_mul_cancel,S.dance]
     change S.dress g⁻¹ _ _= _; rw [← T.keptZ p (1 :T.Free→K) i]; change S.dress g⁻¹ _ _= b _; nth_rw 1 [← he] -- likely
     change g⁻¹ _ * _ * _ =g⁻¹ _ * _ * _; rw [show T.cite 1 s i.val =1 from T.keptZ _ _ i, show S.dress g b i.val= _ from T.bare_sweep b i]
lemma crust_pure (p:T.Stable→K)(s:T.Free→K): T.dell (T.crust p s)=s:=by rw [crust,T.dell_reg _ _ _ ,T.stays]; intro v hv; rw [Pi.inv_apply,setMove,T.swept _ hv,inv_one]
lemma order_set (x:D→K) : T.sweep x=T.setMove (T.splitSet x):= T.sweepZ _ _ (fun i=> (T.keptZ (T.splitSet x) (1:T.Free→K) i).symm) -- inference
lemma crust_at (x:D→K) : T.crust (T.splitSet x) (T.dell x)=x :=by
      unfold crust; rw [← T.emits, ← T.order_set,S.dandy, inv_mul_cancel,S.dance]
variable [TopologicalSpace K] [IsTopologicalGroup K]
@[fun_prop] lemma crust_cont : Continuous (fun u:(T.Stable→K) × (T.Free→K)=>T.crust u.1 u.2):=by
     let f:= fun u:(T.Stable→K) × (T.Free→K)=> T.setMove u.1; have hf:Continuous f:= T.sweepC.comp (T.citeC.comp (continuous_fst.prodMk continuous_const)); let g:= fun u:(T.Stable→K) × (T.Free→K)=>T.cite 1 u.2; have hh:Continuous g:= T.citeC.comp (continuous_const.prodMk continuous_snd); apply continuous_pi; intro i; unfold crust; change Continuous (fun x=> _); apply (show Continuous (fun u=>(f u (S.inn i))⁻¹ * g u i) from (continuous_apply (S.inn i)|>.comp hf).inv.mul (continuous_apply i|>.comp hh)).mul ((continuous_apply (S.out i)|>.comp hf).inv.inv)
def crustX : ((T.Stable→K) × (T.Free→K))≃ₜ (D→K):= {
    toFun:=fun u=>T.crust u.1 u.2
    invFun:=fun x=>(T.splitSet x,T.dell x)
    left_inv:= fun _=> Prod.ext (T.crust_split ..) (T.crust_pure ..)
    right_inv:=T.crust_at
    continuous_toFun:=T.crust_cont
    continuous_invFun:= (continuous_pi fun _=>continuous_apply _).prodMk T.dellC }
variable [Fintype D]
lemma prod_stamp (G:Gauge): MeasurePreserving T.crustX ((Gem G T.Stable).prod (Gem G T.Free)) (Gem G D):=by
     let X:= T.crustX (K:=G.El); let v:= Gem G D; let μ:= (Gem G T.Stable).prod (Gem G T.Free); have ht:Measurable X.symm:= X.symm.measurable
     have ha: MeasurePreserving X.symm v μ:=by
         refine ⟨ht,?_⟩
         unfold v; rw [← T.citeHaar.map_eq,Measure.map_map ht T.citeHaar.measurable]; ext s hs; rw [Measure.map_apply (ht.comp T.citeHaar.measurable) hs]; unfold μ; rw [Measure.prod_apply, Measure.prod_apply hs]; swap; · exact (ht.comp T.citeHaar.measurable) hs
         apply lintegral_congr_ae <| Eventually.of_forall fun u=>?_; let f:T.Free→G.El :=fun _=>1; let K:=fun v:Tile G T.Free=>T.dell (T.cite u v); rw [← (T.rightHaar u).measure_preimage (show NullMeasurableSet ((Prod.mk u) ⁻¹' s) (Gem G T.Free) from (hs.preimage (measurable_const.prodMk measurable_id)).nullMeasurableSet)]; -- occ
         congr! 1; ext x; simp only [Set.mem_preimage]; change X.symm (T.cite u x) ∈ s ↔ (u,T.dell _)∈s; rw [show X.symm (T.cite u x)= (u,T.dell (T.cite u x)) from Prod.ext (funext fun p=>T.keptZ u x p) (rfl)]
     refine ⟨X.measurable,?_⟩; change μ.map X=v; rw [← ha.map_eq,Measure.map_map X.measurable ht, show _∘ X.symm=id from funext fun i=> X.apply_symm_apply i, Measure.map_id]
end Score.Stand
end YM.OPE.Cascade
