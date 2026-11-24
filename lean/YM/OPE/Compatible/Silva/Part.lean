import YM.OPE.Compatible.Silva.Avon
/-!
# Denominator estimate
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D: Alps K T d u} (U:Boxes G S.patch S.kernel) {L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:ReadyV S he U A D L g)
variable (V:Bor H D b)(Y:Elm A S H t r)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
lemma riseF {n:ℕ}(hn:0<n)(x:LK)(hs:ContDiffAt ℝ ω (pane X! t A.clip A.live) 0): Radial.jet (Y.L W!).f n x=Radial.jet (pane X! t A.clip A.live) n (lamps S he H X G x)/4:=by
       let D:= lamps S he H X G; let f:= pane X! t A.clip A.live ∘ D; have hv: Tendsto ((stroll S he H X).rollX (G:=G)) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! (stroll S he H X).rollX.continuous_of_finiteDimensional.tendsto (0:LK)
       let O:LK→ℝ:= (4:ℝ)⁻¹ • f; have hx: (Y.L W!).f =ᶠ[𝓝 0] O - fun _=> mural μ A 0:=by
            rw [Y.Lf]; exact (Y.ok.comp_tendsto hv).trans (Eventually.of_forall (fun i=> (loves S he H X A t i).trans (by change f i/4- _= (4:ℝ)⁻¹*f i- _;ring))) -- mismatch functions
       have ht: ContDiffAt ℝ (↑n) f 0:= ((show ContDiffAt ℝ ω _ (D 0) from D.map_zero.symm ▸ hs).comp 0 D.contDiff.contDiffAt|>.of_le le_top); unfold Radial.jet; rw [(hx.iteratedFDeriv ℝ _).eq_of_nhds,iteratedFDeriv_sub_apply (f:=O) (ht.const_smul (4:ℝ)⁻¹) (by exact contDiffAt_const), iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hn),Pi.zero_apply,sub_zero, show iteratedFDeriv ℝ n O 0= _ from iteratedFDeriv_const_smul_apply ht (a:=(4:ℝ)⁻¹),_root_.smul_apply, smul_eq_mul]; unfold f; rw [jets_linear D (hs.of_le le_top)]; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; change _*((4:ℝ)⁻¹*iteratedFDeriv ℝ n (pane X! t A.clip A.live) 0 (fun _:Fin n=>D x))= _; unfold D;ring
lemma riseR {n:ℕ}(hn:0<n)(x:P!): Radial.jet (V.L X).f n x=Radial.jet (swornV D.clip D.live) n (rayS H X G x)/4:=by
       let L:=rayS H X G;let Y:=swornV D.clip D.live (n:=c);let f:= Y ∘ L; have hu:Tendsto (X.rollX (G:=G)) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! X.rollX.continuous_of_finiteDimensional.tendsto (0:P!)
       let O:P!→ℝ:=(4:ℝ)⁻¹ • f; have hp:(V.L X).f=ᶠ[𝓝 0] O - fun _=> mural H D 0:=by
             rw [V.acts]; refine (V.u.comp_tendsto hu).trans (Eventually.of_forall fun x=>?_); change f x/4- _= (4:ℝ)⁻¹ * f x- _;ring
       have he:ContDiffAt ℝ ω Y 0:= (chartK D.live D.clip c D.pays).1; have ht:ContDiffAt ℝ (↑n) f 0:= ((show ContDiffAt ℝ ω Y (L 0) from L.map_zero.symm ▸ he).comp 0 L.contDiff.contDiffAt|>.of_le le_top); unfold Radial.jet; rw [(hp.iteratedFDeriv ℝ n).eq_of_nhds,iteratedFDeriv_sub_apply (f:=O) (ht.const_smul (4:ℝ)⁻¹) contDiffAt_const,iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hn),Pi.zero_apply,sub_zero,show iteratedFDeriv ℝ n O 0= _ from iteratedFDeriv_const_smul_apply ht (a:=(4:ℝ)⁻¹),_root_.smul_apply,smul_eq_mul]; unfold f; rw [jets_linear L (he.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]; change _*((4:ℝ)⁻¹*iteratedFDeriv ℝ n Y 0 (fun _:Fin n=> L x))= _; unfold L Y;ring
lemma polesT {C:Law J!}(hh:Roomy S he H U C) (h:ReadyV S he U A D L g) (p:P!)(v:J!):
     let Q:=Tight S he H X g (p,v)
     (penon (Y.L W!)).P Q Q= (penon (V.L X)).P p p+C.P v v:=by
       intro z; let O:= EchoV S he H G v; let x:= rayS H X G p; let P:=fieldT (cabin g) x; let M := pane X! t A.clip A.live; have hs:=viewer t h.1.2.1; let W:=((0:Bid.Dir G c),O); let Z:=iteratedFDeriv ℝ 2 M 0
       have H1:= penon_shape (Y.L W!) z; have H2 := penon_shape (V.L X) p; rw [riseF S he H X t Y (by decide) z hs.origin, show lamps S he H X G z=P+W from tight_ray _ _ _ _ g U h.1 t ..] at H1; rw [riseR H X V (by decide)] at H2
       unfold Radial.jet at H1 H2
       let D' := Z.curryLeft; have hBB: Z ![P+W,P+W]= Z ![P,P]+Z ![W,W]:=by
            have ha:= D'.map_add P W; have hp (a):Z ![a,P+W]=Z ![a,P]+Z ![a,W]:=DFunLike.congr_fun ((D' a).curryLeft.map_add P W) ![]; have ht : Z ![P,W]=0:=hs.hedge O x; rw [show Z ![P+W,P+W]=Z ![P,P+W]+Z ![W,P+W] from DFunLike.congr_fun ha ![P+W],hp,hp,ht, Work.F03.hessian_symmetric (hs.origin.of_le le_top) W P,ht,zero_add,add_zero]
       rw [show (fun _ :Fin 2=> P+W)=![P+W,P+W] from funext fun i=> by fin_cases i<;>rfl,hBB] at H1; rw [show (fun _ :Fin 2=>x)=![x,x] from funext fun i=>by fin_cases i<;>rfl,TipL S he U A D h t x x] at H2; rw [hh,← tollY S he U h.1 t O O]; change _=_+Z ![W,W]/4; change _*Z ![P,P]/4=_ at H2; norm_num at H1 H2; linarith only [H1,H2]
end YM.OPE.Cascade.Rill
