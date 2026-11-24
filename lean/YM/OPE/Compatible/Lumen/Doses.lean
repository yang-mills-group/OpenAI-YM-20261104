import YM.OPE.Compatible.Lumen.Ochre
/-!
# lifting frame decomposition on gradient charges
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer
open PertExtension Series Asymptotics
attribute [local instance] Gauge.frobInner
namespace Score.Stand
variable {V D:Type}{B:Set V} {S:Score D V}[Fintype D]
local notation "XD" => Keys G D
variable (T:S.Stand B)
nonrec def porch (G:Gauge): Keys G D→L[ℝ] Keys G T.Stable := ContinuousLinearMap.pi (fun i=>ContinuousLinearMap.proj i.val)
def palmL (G:Gauge): Keys G T.Stable→ₗ[ℝ] Keys G D where
   toFun p:=T.cite p 0
   map_add' a b:=by funext i; simp only [cite, Pi.add_apply]; split <;>simp
   map_smul' a b:=by funext i; simp only [cite,Pi.smul_apply,RingHom.id_apply]; split<;>simp
-- world coordinates. charge stable all and free
omit [Fintype D] in
@[simp] lemma porchMove (i:Keys G T.Stable): T.porch G (T.palmL G i)=i:=funext fun p=> T.keptZ i (0:Keys G T.Free) p
omit [Fintype D] in
@[simp] lemma porchMoveU (i:Keys G T.Free):T.porch G (T.rollX i)=0:= funext fun p=> T.keptZ 0 i p
omit [Fintype D] in
@[simp] lemma slabMove (x:Keys G T.Free): T.slab G (T.rollX x)=x:= funext fun p=>T.kept 0 x p
omit [Fintype D] in
@[simp] lemma slabMoveU (i:Keys G T.Stable): T.slab G (T.palmL G i)=0:=funext fun p=> T.kept i 0 p
lemma porch_tex (x: XD): T.porch G (T.dtex G x)= T.porch G x:=by
    let L:=T.porch G; let A:= T.skews G; have ht: (L∘A.gradient)=ᶠ[𝓝 0] L:=by
        filter_upwards [A.lead_grad,local_zone (G:=G) (I:=D)] with i hi hv; change L (A.gradient i)=_; rw [hi]; ext p r; change G.plog (G.mat ((T.crust (T.splitSet (put i)) (fun p:T.Free=> put i p.val)) p.val)) r= i p.val r; rw [show T.crust (T.splitSet (put i)) (fun j:T.Free=>put i j.val) p.val=put i p.val from congr_fun (T.crust_split ..) _]; exact congr_arg (fun v:G.Color=> WithLp.ofLp v r) (congr_fun hv _)
    have he: L (T.dtex G x)=fderiv ℝ (L ∘ A.gradient) 0 x:=by
        rw [fderiv_comp _ L.differentiableAt (A.gradC.differentiableAt (by simp)), L.fderiv];rfl
    rw [he,ht.fderiv_eq, L.fderiv]
lemma keep_tex (x:Keys G T.Free):T.dtex G (T.rollX x) = T.rollX x:=by
    let L:= LinearMap.toContinuousLinearMap (T.rollX (G:=G)); let A:= T.skews G
    have ht(i:Keys G T.Free): (A.q (put (L i)))=put (L i):=by
       change T.stepSet (put (T.rollX i))=put (T.rollX i); rw [T.rollPut]; have hu : T.splitSet (T.cite 1 (put i))=1:= funext fun p=>T.keptZ _ _ p
       change T.crust (T.splitSet (T.cite 1 (put i))) (fun v=> T.cite 1 (put i) v.val)=T.cite 1 (put i); rw [hu,show (fun v:T.Free=> T.cite 1 (put i) v.val)=put i from funext fun p=>T.kept 1 (put i) p,crust,setMove,T.dress1,T.sweep1,inv_one,S.dance]
    have he: fderiv ℝ (A.gradient∘ L) 0= L:= (show A.gradient∘ L=ᶠ[𝓝 0] L from by unfold Libra.Dimes.gradient; simp_rw [Function.comp_def,ht]; exact (show Tendsto L (𝓝 0) (𝓝 0) from L.map_zero ▸ L.continuous.continuousAt).eventually local_intro).fderiv_eq.trans L.fderiv
    have hu: (T.dtex G) (T.rollX x)= fderiv ℝ (A.gradient∘ L) 0 x:=by
        rw [fderiv_comp, L.map_zero,L.fderiv]; rfl; · rw [L.map_zero];exact A.gradC.differentiableAt (by simp)
        exact L.differentiableAt
    rw [hu,he]; rfl
omit [Fintype D] in lemma nestPoints (x:XD):T.rollX (T.slab G x)+T.palmL G (T.porch G x)=x:=by
    funext i; change T.cite 0 (T.slab G x) i+ T.cite (T.porch G x) 0 i=_; unfold cite; split<;> simp only [Pi.zero_apply,add_zero,zero_add]<;> rfl
lemma dtexInj : Injective (T.dtex G):= by
    intro x y h; have he(u:XD):T.dtex G u=T.rollX (T.slab G u)+T.dtex G (T.palmL G (T.porch G u)):=by nth_rw 1 [← T.nestPoints u]; rw [map_add,T.keep_tex]
    have hx:T.porch G x=T.porch G y:= ((T.porch_tex x).symm.trans (congr_arg (T.porch G) h)).trans (T.porch_tex y); rw [he x, he y,hx] at h; have hp:=add_right_cancel h; rw [← T.nestPoints x,← T.nestPoints y,hx,hp]
end Score.Stand
end YM.OPE.Cascade
