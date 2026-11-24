import YM.OPE.Compatible.Lark.Via
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
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- accounting index and oriented trans
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
local notation "M!"=>pane X! t A.clip A.live
local notation "U!"=> FUND S he U
local notation "K!"=> countingBasis X! G
include U
lemma costHalo (b α:ℝ)(ht:TEX U A.clip D.clip A.live D.live α P)(x:Bid.Dir G c):
    -jet (haloP (b+α) D) 2 x=b*jet (swornV D.clip D.live) 2 x/4+narrate c (U.talo A.live A.clip P) (spool G c x) /8:=by
        let M:= swornV D.clip D.live (n:=c); let V:=swornY D.live (n:=c); have hM:ContDiffAt ℝ ω M 0:=(chartK D.live D.clip c D.pays).1; have hv:ContDiffAt ℝ ω V 0:= (tubesY D.live D.clip c D.pays).1; let k:=spool G c x; have hR :=leafSongs D.live D.clip c 2 0 D.pays; have hz:= inkSongs D.live D.clip c 2 0 D.pays; let u:= leafV D.live 2; let v:= inkV D.live D.clip 2; have hA:ContDiffAt ℝ ω ((-(b+α)) • M) 0:= hM.const_smul (-(b+α)); have he' : ContDiffAt ℝ ω ((-1:ℝ) • V) 0:= hv.const_smul (-1:ℝ)
        have he :iteratedFDeriv ℝ 2 V 0 ![x,x]+α * iteratedFDeriv ℝ 2 M 0 ![x,x]=narrate c (U.talo A.live A.clip P) k:=by
             rw [← hR.2.2 ![x,x],← hz.2.2 ![x,x]]; rw [←regaled (U.talo A.live A.clip P) (folk_whole (folkT U.rocket2 (U.folk_crown A.pays))),← ht.2.2]; unfold narrate; rw [libAdd _ _ (sootS hR.2.1.choose_spec) (sootS (Sack.scale_line hz.2.1.choose_spec α)),libScale v _ α]; rw [show (spool G c).toContinuousLinearMap ∘ ![x,x]=fun _:Fin 2=> k from funext fun i=>by fin_cases i<;>rfl]
        unfold haloP; rw [arcConst _ (f:=((-(b+α)) • M+(-1:ℝ) • V)) ((hA.add he').of_le le_top), arcAdd (hA.of_le le_top) (he'.of_le le_top),arcConst _ (hM.of_le le_top),arcConst _ (hv.of_le le_top)]; change -(_ * (_ * jet M 2 x + _ * jet V 2 x))= b*jet M 2 x /4 + narrate c (U.talo A.live A.clip P) k/8; rw [njet,njet,← he];ring
-- sign bill abstract mat worm
def Matter (g: Bid.Dir G c→AxisChart G X!)(A:Alps K T i v)(w: Bid.Dir G c): Matrix Q! Q! ℝ:=
    let p:=fieldT (cabin g) w
    let q:=fieldU (cabin g) w w
    let D:=HATCH (pane X! t A.clip A.live) K! p
    U!⁻¹* HATCH (pane X! t A.clip A.live) K! q+ U!⁻¹ * ROACH (pane X! t A.clip A.live) K! p p-U!⁻¹ * D * U!⁻¹ * D
abbrev CostH (g: Bid.Dir G c→AxisChart G X!)(A:Alps K T i v)(P:ChartRatio G)(w: Bid.Dir G c):ℝ:=
    let p:= spool G c w
    (narrate c (U.talo A.live A.clip P) p-U.silo A.live A.clip P c ![p,p])/8 - (skipH S he H G * Matter S he U t g A w).trace /16
omit h
include S he H G U g A D L t ht C hc
lemma priced (hS:G.Simple)(α b:ℝ)(hd:TEX U A.clip D.clip A.live D.live α P)(h:ReadyV S he U A D L g)(x:Keys G (Limb H)):
   DriftH S he H t g A D P b (b+α) C (cloak H x)=CostH S he H U t g A P (cloak H x):=by
        let v:=cloak H x;let p:=fieldT (cabin g) v;let q:=fieldU (cabin g) v v; let tH:= πV S he t A 3; let xH:=πV S he t A 4; let B:=InV S he H G; let A':=C.average Wμ (τ21 xH p B); let B':= C.average Wμ ((τ2 tH p B)^2); let D':= C.average Wμ (τ2 tH q B); let T:=heatPay M! K! U!⁻¹ p p q; let R:=(skipH S he H G*Matter S he U t g A v).trace;let F:=viewer t h.1.2.1
        have he':A'-B'/2+D'/2=T/8+R/16:= coilTrace S he H U t h.1 hc hS x _
        have hr:U.silo A.live A.clip P c ![spool G c v,spool G c v]=2*jet (springF X! A.live) 2 p.2 + T - 2*jet (taxY X! P) 2 p.2:=by
            rw [teach S he U h.1 t A.pays ht v,njet,njet]; unfold p T;ring
        have hv:jet M! 2 p=jet (swornV D.clip D.live) 2 v:=by rw [njet,njet,TipL S he U A D h t]
        change _ - jet (haloP _ D) 2 v- A'+B'/2-D'/2= (_-U.silo A.live A.clip P c _)/8-R/16
        rw [sub_eq_add_neg (jet _ _ p) (jet (haloP (b+α) D) 2 v),costHalo S U b α hd v,show jet (HaloC S he t b A P) 2 p=_ from (bandC S he t ht b F.origin p).2,hv,hr]; unfold v at *;linarith only [he']
end YM.OPE.Cascade.Rill
