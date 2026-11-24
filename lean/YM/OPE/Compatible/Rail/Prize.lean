import YM.OPE.Compatible.Rail.Mull
/-! # Determinant parser operational estimates, rank≥2 cotton recipe -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Asymptotics Work.F05 Stationary
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type} {G:Gauge}{c f:Side}
namespace Virgin
open Analysis Module
variable {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y] [NormedSpace ℝ Y][Fintype I][DecidableEq I] {F:X × Y →ℝ}{g:X→Y}
lemma pack_seat {F:X × Y→ℝ}{z:X×Y}(s:ContDiffAt ℝ ω F z)(u v:Y) : iteratedFDeriv ℝ 2 (fun i=> F (z.1,i)) z.2 ![u,v]=iteratedFDeriv ℝ 2 F z ![(0,u),(0,v)]:=by
    let P:=fun i:Y=>(z.1,i); let Q:=ContinuousLinearMap.inr ℝ X Y; have h(i): fderiv ℝ P i=Q:= ((hasFDerivAt_const (𝕜:=ℝ) _ _).prodMk (hasFDerivAt_id i)).fderiv ; rw [show iteratedFDeriv ℝ 2 (fun i=>F (z.1,i)) z.2 ![u,v] =_ from pay_second (F:=F) (x:=z.2) (H:=P) s (contDiffAt_const.prodMk contDiffAt_id) u v]
    rw [iteratedFDeriv_two_apply (f:=P),show fderiv ℝ P=fun _=>Q from funext h]; simp only [show fderiv ℝ (fun _:Y=>Q) z.2=0 from (hasFDerivAt_const ..).fderiv, _root_.zero_apply,map_zero,zero_add]; rfl
abbrev deposit (F:X×Y→ℝ)(g:X→Y)(B:Basis I ℝ Y)(x:X):=damage B (fun i=>F (x,i)) (g x)
abbrev forceP (F:X×Y→ℝ)(u v:Y)(x:X×Y):=iteratedFDeriv ℝ 2 F x ![(0,u),(0,v)]
lemma powerS (F:X×Y→ℝ)(u v:Y) (h:ContDiffAt ℝ ω F 0):ContDiffAt ℝ ω (forceP F u v) 0:=by
    unfold forceP; simp_rw [iteratedFDeriv_two_apply]; exact (((h.fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _=> (0,u)) contDiffAt_const|>.clm_apply (g:=fun _=>(0,v)) contDiffAt_const)
lemma pension (B:Basis I ℝ Y)(s:Stayed F g)(i j:I): (fun x=>deposit F g B x i j)=ᶠ[𝓝 0] forceP F (B i) (B j) ∘ viewS g:=by
    filter_upwards [((s.H0 ▸ s.hl.continuousAt.tendsto : Tendsto (viewS g) _ (𝓝 0))).eventually (s.origin.eventually (by simp))] with x hx; rw [deposit,damage,LinearMap.toMatrix₂_apply,bend_apply]; exact pack_seat hx _ _
lemma memo_pension (B:Basis I ℝ Y)(s:Stayed F g) : Memo (deposit F g B) 0:=fun i j=> ((show ContDiffAt ℝ ω (forceP F (B i) (B j)) (viewS g 0) by rw [s.H0]; exact powerS _ _ _ s.origin).comp 0 s.hl).congr_of_eventuallyEq (pension B s i j)
abbrev HATCH (F:X×Y→ℝ)(B:Basis I ℝ Y)(v:X×Y): Matrix I I ℝ:= Matrix.of fun i j=> iteratedFDeriv ℝ 3 F 0 ![v,(0,B i),(0,B j)]
abbrev ROACH (F:X×Y→ℝ)(B:Basis I ℝ Y)(v w:X×Y): Matrix I I ℝ:=Matrix.of fun i j=> iteratedFDeriv ℝ 4 F 0 ![v,w,(0,B i),(0,B j)]
lemma bendP {f:X×Y→ℝ}(h:ContDiffAt ℝ ω f 0) (a b:X×Y)(u v:Y):iteratedFDeriv ℝ 2 (forceP f u v) 0 ![a,b]=iteratedFDeriv ℝ 4 f 0 ![a,b,(0,u),(0,v)]:=by
    let p:= fun x=> iteratedFDeriv ℝ 3 f x ![b,(0,u),(0,v)]; rw [show iteratedFDeriv ℝ 4 f 0 ![a,b,(0,u),(0,v)] = D a p 0 from cons_jet (h.of_le le_top) a _]; rw [← direction2 _ _ _ _ (powerS _ _ _ h)]; exact GermD a ((h.eventually (by simp)).mono fun x hx=> (cons_jet (hx.of_le le_top) b ![(0,u),(0,v)]).symm)
lemma advert (B:Basis I ℝ Y)(s:Stayed F g)(a b:X):directionM (deposit F g B) 0 a = HATCH F B (fieldT g a) ∧ bendM (deposit F g B) 0 a b=HATCH F B (fieldU g a b)+ ROACH F B (fieldT g a) (fieldT g b):=by
    constructor <;>ext i j
    · change fderiv ℝ _ 0 a=_; have hf:=pension B s i j; rw [hf.fderiv_eq,fderiv_comp 0 (by rw [s.H0]; exact (powerS _ _ _ s.origin).differentiableAt (by simp)) (s.hl.differentiableAt (by simp)),s.H0];exact (cons_jet (s.origin.of_le le_top) (fieldT g a) ![(0,B i),(0,B j)]).symm
    simp only [bendM,Matrix.of_apply,HATCH,ROACH, Matrix.add_apply]; rw [((pension B s i j).iteratedFDeriv ℝ 2).eq_of_nhds,pay_second (by rw [s.H0]; exact powerS _ _ _ s.origin) s.hl,s.H0,bendP s.origin]; exact congr_arg₂ (· + ·) (cons_jet (s.origin.of_le le_top) (fieldU g a b) ![(0,B i),(0,B j)]).symm rfl
lemma YSolve (B:Basis I ℝ Y)(s:Stayed F g)(a b:X):
    (deposit F g B 0)*ᵥ(cash B (fieldU g a b).2) = fun i=>-(iteratedFDeriv ℝ 3 F 0 ![(0,B i),fieldT g a,fieldT g b]):=by
    funext i; let u:=(fieldU g a b).2; let P:=fun y=> F (0,y); let D:=deposit F g B 0; have hx:g 0=0:=s.zero; have hh:D=damage B P 0:=by unfold D deposit; rw [hx]
    rw [s.reserve (B i) a b,s.lower a b,Work.F03.hessian_symmetric (s.origin.of_le le_top),neg_neg];change D.mulVec (cash B u) i=_; rw [← pack_seat s.origin,hh,← detracts B]; change _= dotProduct (cash B (B i)) (damage B P 0 *ᵥ cash B u); rw [show cash B (B i)=Pi.single i 1 by unfold cash; ext j; by_cases i=j<;> rename_i hi <;> first | subst j; simp | simp [hi,Ne.symm hi] ]; simp
end Virgin
end YM.OPE.Flume
