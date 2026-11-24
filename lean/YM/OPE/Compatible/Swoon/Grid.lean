import YM.OPE.Compatible.Swoon.Bleed
/-!
# Color trace of yy-charge exact vanish. Based on full-F Hess positive, all centers bought
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
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
section algebra
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma tri_cost (f:E→ℝ)(x:E): jet f 3 x=iteratedFDeriv ℝ 3 f 0 ![x,x,x]/6:=by rw [jet,show (fun _ : Fin 3=>x)=![x,x,x] from funext fun i=>by fin_cases i<;>rfl]; norm_num [Nat.factorial];ring
lemma ter_cost (f:E→ℝ)(x:E): jet f 4 x=iteratedFDeriv ℝ 4 f 0 ![x,x,x,x]/24:=by rw [jet,show (fun _ : Fin 4=>x)=![x,x,x,x] from funext fun i=>by fin_cases i<;>rfl];norm_num [Nat.factorial];ring
end algebra
include U S he G g A L h t
include ht in
lemma crest (x:P!): (fun p:J!=> (Y.L W!).hat P (Tight S he H X g (x,p)))=
   Dome (πV S he t A 3) (πV S he t A 4) (HaloC S he t r A P) (InV S he H G) (fieldT (cabin g) (rayS H X G x)) (jet (looper P) 2 x):=by
      funext i; rw [SwiftF S he H X t Y ht _ (viewer t h.2.1).origin]; dsimp only;rw [tight_ray S he H X g U h t x i, (tight_p S he H X g x i).1]; let Z:=pane X! t A.clip A.live; let v:=fieldT (cabin g) (rayS H X G x)+ InV S he H G i; unfold Dome; apply congr_arg₂ flareTok
      · rw [tri_cost]; change -(iteratedFDeriv ℝ 3 Z 0 ![v,v,v]/6)/4= -(((4:ℝ)⁻¹*iteratedFDeriv ℝ 3 Z 0 ![v,v,v])/6);ring
      rw [ter_cost]; change -(iteratedFDeriv ℝ 4 Z 0 ![v,v,v,v]/24)/4+jet _ 2 v+ jet (looper P) 2 x= -(((4:ℝ)⁻¹*iteratedFDeriv ℝ 4 Z 0 ![v,v,v,v])/24)+jet _ 2 v+_; ring
lemma polarπ (n:ℕ):Tensor.Sym (πV S he t A n):= fun v e=>congr_arg ((4:ℝ)⁻¹ * · ) (Analysis.sym_Jet ((viewer t h.2.1).origin.of_le le_top) v e)
include H C hc
lemma rankparse (α:ℝ)(p:ChartRatio G)(hd:TEX U A.clip D.clip A.live D.live α p)(x: Keys G (Limb H)):
    let y:=cloak H x
    let f:=swornV D.clip D.live (n:=c)
    let z:=fieldT (cabin g) y
    let q:= FetchS S he H G (fieldU (cabin g) y y).2
    jet f 3 y/4=τ0 (πV S he t A 3) z ∧ jet f 4 y/4 = τ4 (πV S he t A 4) z-C.P q q/8:=by
          intro y f z q; rw [tri_cost,ter_cost]; let M:=pane X! t A.clip A.live; let W:=iteratedFDeriv ℝ 3 M 0; let d:= iteratedFDeriv ℝ 4 M 0; let v:=fieldU (cabin g) y y; have h3:iteratedFDeriv ℝ 3 f 0 ![y,y,y] = W ![z,z,z]:= Teach3 S he U h A.pays D.pays hd t _; have h4:iteratedFDeriv ℝ 4 f 0 ![y,y,y,y]=d ![z,z,z,z]+3*W ![v,z,z]:=Teach4 S he U h A.pays D.pays hd t _; rw [h3,h4];constructor
          · change W _/6/4=((4:ℝ)⁻¹ * W ![z,z,z])/6;ring
          obtain ⟨hu,hV⟩:= τSolve S he H U t h hc x; have hh:=DFunLike.congr_fun hV q; change (2:ℝ)⁻¹*((4:ℝ)⁻¹ * W ![InV S he H G q,z,z])=(-2:ℝ)⁻¹ * C.P q q at hh; rw [show InV S he H G q=v from hu] at hh; change (d _+ 3*W _)/24/4=((4:ℝ)⁻¹ * d ![z,z,z,z])/24-_; linarith only [hh]
end YM.OPE.Cascade.Rill
