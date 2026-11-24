import YM.OPE.Compatible.Gables.Tan
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
include X C Y hc h ht
lemma rainy (m:ScriptJ LK)(hm:m.B)(α:ℝ)(hq:TEX U A.clip D.clip A.live D.live α P)(Bv:r+α=b)(hS:G.Simple): (Y.L W!).pay P m= fair H! ZY (Thunder S he H X t P V U g A) (gatedB S he H X t Y g P C m) :=by
      let T:=Tight S he H X g; let M:=penon PY; let w:=(Y.L W!).hat P; let HX:= (Chart.tangent G (Stand.Free W!)); -- Not H shadow
      rw [(Y.L W!).cutOut ht M m (penon_shape _)]
      let Pq:= united ZY C; have hh (x:P! × J!): M.P (T x) (T x)= Pq.P x x:= polesT S he H X U t V Y hc h x.1 x.2
      have hx : (m*w).B:= ScriptJ.height hm ((Y.L W!).hat_toll ht); let q:= gatedB S he H X t Y g P C m; have hB: ScriptJ.B q:= Gates_B S he H X t Y ht m hm -- implicit g order
      have hv (p:ScriptJ LK)(h:p.B): draw p M HX =draw (PL (p ∘ T)) ZY H!:=by
          haveI: (Measure.prod H! Wμ).IsAddHaarMeasure:= Pilot.twoHaar (E:=P!) (F:=J!) H! Wμ
          rw [ease p h T.symm.toLinearEquiv M Pq (fun i=>by rw [← hh];change _= M.P (T (T.symm i)) (T (T.symm i)); simp) HX (Measure.prod H! Wμ)]; exact guest Wμ C H! ZY (p ∘ T) (fun i=>(h i).compLinear T.toLinearMap)
      let f:= w ∘ T; let s:= PL f; let σ:=s 0; let U':= Thunder S he H X t P V U g A; have hs(x): s x=σ*U' x:=congr_fun (Clover S he H X U t h V Y ht hc α hq Bv hS) x
      have hl(x):(s x).s=1 := headD Wμ C _ (fun i=>(Y.L W!).hat_full ht _)
      have hβ:= ThunderB S he H X U t h V Y ht hc α hq Bv hS; have hr :(draw U' ZY H!).s=1:= headD H! ZY _ (fun i=> by unfold U' Thunder; rw [ml_s,(V.L X).hat_full ht]; exact one_mul _)
      have ha(x): PL ((m*w) ∘ T) x= σ * ((q * U') x) :=by
           let D:=PL ((m*w) ∘ T) x; let U:= s x; have he:q x=D/U:=rfl;change D=σ * (q x * _); rw [he,dv]; calc
               _= D*(U⁻¹*U):=by rw [JetS.uniting (show U.s≠0 from (hl _).trans_ne one_ne_zero),mul_one]
               _= _:=by rw [show U= σ * U' x from hs x]; ring
      change draw (m*w) M HX / draw w M HX=fair H! ZY U' q; rw [hv _ hx,hv _ ((Y.L W!).hat_toll ht),show PL ((m*w) ∘ T)=fun x=>σ *((q*U') x) from funext ha,show PL _= _ from (show PL f=fun x=> σ * U' x from funext hs),coastM H! ZY _ U' hβ,coastM H! ZY _ (q*U') (height hB hβ)]; exact JetS.transfer _ _ _ ( (hl 0).trans_ne one_ne_zero) ( (hr).trans_ne one_ne_zero)
end YM.OPE.Cascade.Rill
