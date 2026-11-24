import YM.OPE.Compatible.Gables.Satisfy
/-!
# All trace accounts, ordinary torque identities.
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
variable (t:S.Choices) (h:ReadyV S he U A D L g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- accounting index and oriented trans
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
open Flume.Script Shell
local notation "T!"=> Flume.Script.Tile G S.ratio.count
open Planned.PrimaryIntegral295.Carrier
local notation "U!"=> FUND S he U
local notation "CAX" => actLight S he H G
open JetS ScriptJ Shell Char Libra.Shift
local notation "PL"=> Shift.crossT Wμ C
local notation "PY"=> (Y.L W!)
local notation "H!"=> Chart.tangent G X.Free
local notation "ZY"=> penon (V.L X)
-- ephemeral Down and Stored markers.
def foldsP (U: Elm A S H t r)(g: Bid.Dir G c→AxisChart G X!)(P:ChartRatio G):ScriptJ (P!×J!) := (U.L W!).hat P ∘ Tight S he H X g -- overshadow
abbrev gatedB (U: Elm A S H t r)(g: Bid.Dir G c→AxisChart G X!)(P:ChartRatio G)(C:Law J!)(u: ScriptJ LK)(x:P!) : Token:= fair Wμ C (fun y=> (U.L W!).hat P (Tight S he H X g (x,y))) (fun y=> u (Tight S he H X g (x,y)))
include X C
include hc h A t ht L S he
omit h L hc in
lemma Gates_B (p:ScriptJ LK)(hp:p.B): ScriptJ.B (gatedB S he H X t Y g P C p):=by
       let T:=Tight S he H X g; let v:=p ∘ T; let w:=foldsP S he H X t Y g P; let Q:=PL w; have hP: ScriptJ.B v:=fun i=>(hp i).compLinear T.toLinearMap; have hx:ScriptJ.B w:=fun i=>((Y.L W!).hat_toll ht i).compLinear T.toLinearMap; change ScriptJ.B (fun x=>PL (v*w) x/Q x); have hx := crossB Wμ C w hx; have hB: ScriptJ.B (fun x=>(Q x)⁻¹):= mintInv Q hx fun i=>headD Wμ C _ fun y=>(Y.L W!).hat_full ht _
       exact ScriptJ.height (p:=PL (v*w)) (crossB Wμ C _ (ScriptJ.height hP (show ScriptJ.B w from fun i=>((Y.L W!).hat_toll ht i).compLinear T.toLinearMap))) hB
lemma Clover (α:ℝ)(hq:TEX U A.clip D.clip A.live D.live α P)(Bv:r+α=b)(hS:G.Simple):
     let d:= fun x:P!=> rayS H X G x
     PL (foldsP S he H X t Y g P)=fun x=> let i:=PL (foldsP S he H X t Y g P) 0; i*((V.L X).hat P x*flareTok 0 (CostH S he H U t g A P (d x))) :=by
       intro d; subst b; funext i; exact (inclusive S he H X U t h.1 V Y ht hc hS α hq i).trans (congr_arg (fun a:ℝ=> PL (foldsP S he H X t Y g P) 0*((V.L X).hat P i*flareTok 0 a)) (priced S he H U t ht hc hS α r hq h (X.rollX i)))
-- exact. uses identity hats C. No circular.
def Thunder (P:ChartRatio G)(V':Bor H D b) (Y:Boxes G S.patch S.kernel)(g:Bid.Dir G c→AxisChart G X!)(A:Alps K T i v)(x:P!):Token:= (V'.L X).hat P x* flareTok 0 (CostH S he H Y t g A P (rayS H X G x))
include Y
lemma ThunderB (α:ℝ)(hq:TEX U A.clip D.clip A.live D.live α P)(Bv:r+α=b)(hS:G.Simple): ScriptJ.B (Thunder S he H X t P V U g A):=by
     let Q:=PL (foldsP S he H X t Y g P); let f:=Q 0; let Vt:= Thunder S he H X t P V U g A; have hx: ∀ x: P!,Q x = f*Vt x:=fun i=> congr_fun (Clover S he H X U t h V Y ht hc α hq Bv hS) i
     have he' : ScriptJ.B Q:= crossB Wμ C (foldsP S he H X t Y g P) (fun i=> ((Y.L W!).hat_toll ht i).compLinear (Tight S he H X g).toLinearMap)
     have hp:f.s=1:= headD Wμ C _ fun _=> (Y.L W!).hat_full ht _
     change ScriptJ.B Vt;rw [show Vt=fun x:P!=> f⁻¹*Q x from ?_]; swap
     · funext i; rw [hx, ←mul_assoc,uniting (hp.trans_ne one_ne_zero),one_mul]
     exact ScriptJ.height (Bstar (E:=P!) f⁻¹) he'
end YM.OPE.Cascade.Rill
