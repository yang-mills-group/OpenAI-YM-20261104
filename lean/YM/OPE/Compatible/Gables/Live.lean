import YM.OPE.Compatible.Gables.Arms
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
open Flume.Script Shell
local notation "T!"=> Flume.Script.Tile G S.ratio.count
open Planned.PrimaryIntegral295.Carrier
local notation "U!"=> FUND S he U
local notation "CAX" => actLight S he H G
open Page Libra.Char
include S he H G h A g L C hc U t
include ht
lemma mintMe (b:ℝ)(x: Keys G (Limb H)) (i:Ask) : Rookie C CAX (Piax S G U) (dance S he G (fieldT (cabin g) (cloak H x))) (Paloma (mintR S A P b) i) (1/4):=by
       let X:=mintR S A P b; obtain ⟨hu,hv,hq⟩:=tide_feed S (A:=A) b P; have h1 := voteLock S he H U t h 3 (-6:ℝ)⁻¹; have h2 := voteLock S he H U t h 4 (-24:ℝ)⁻¹
       have hp₁:= wardlock S he H U t h hc X.u x (folk_whole hv) h1; have hp₂:=wardlock S he H U t h hc X.v x (folk_whole hq) h2; have hp₃:=wardlock S he H U t h hc X.t x (folk_whole hu) (halock S he H U t h ht b)
       fin_cases i
       · exact hp₁
       · exact hp₁
       · exact hp₂
       · exact hp₃
       intro i; exact Fin.elim0 i
lemma borFlag (s K':ℝ)(hs:0<s)(hK:0≤K')(hv:U.dot.strip s K')(w:ℝ)(hp:2≤w)(k:ℕ)(a:Site c)(b:ℝ)(x: Keys G (Limb H)):
      Ribbon (mintR S A P b) (Piax S G U) CAX C (dance S he G (fieldT (cabin g) (cloak H x))) a k (fun i:ℕ=> cloudFee s K' (4*w) i) (1/4):=⟨ grainG S he H U t h hc hs hK hv k a hp,by norm_num, mintMe S he H U t h ht hc b x⟩
omit hc C H ht in
lemma burns (i:Ask)(h:i=(0:Ask) ∨ i=1)(b:ℝ)(P:ChartRatio G)(x:S!): library c (Paloma (mintR S A P b) i) (fun _ => dance S he G x)= -jet (pane X! t A.clip A.live) 3 x:=by
     rcases h with h|h<;>subst i<;>exact beam3 S he U t ‹licensed ..› _
omit hc C in
lemma mints (p:P!)(y:J!):
    let X':=dance S he G (fieldT (cabin g) (rayS H X G p))
    let D:=Char.Sketch (mintR S A P r) (1/4) X' CAX
    (Y.L W!).hat P (Tight S he H X g (p,y))=Stell D y * flareTok 0 (jet (looper P) 2 p):=by
          intro x d'; rw [SwiftF _ _ _ _ _ _ ht _ (viewer t h.2.1).origin]; dsimp only; let Z:= Tight S he H X g (p,y); let V:=lamps S he H X G Z; let M:= pane X! t A.clip A.live
          obtain ⟨h1,h2,h3⟩:= tide_feed S (A:=A) r P; let T:=dance S he G; let P':= mintR S A P r
          have hs: (T V)=(x+CAX y):=by rw [show V= _ from tight_ray S he H X g U h t p y]; exact map_add T _ _
          have hx(i:Ask)(h:folk (Paloma P' i)): d' i y=(1/4:ℝ)*library c (Paloma P' i) (fun _=> dance S he G V):=by
               change (1/4:ℝ)*listV (Paloma P' i) c (cue (x+(show deck (Flume.Script.Tile G S.ratio.count) c from CAX y)) x (0:ℕ) _) = _; rw [muses _ (folk_whole h)]; apply congr_arg (fun f=> (1/4:ℝ)*library c (Paloma P' i) f); rw [show cue _ _ 0 _= (fun _=>x+(show deck (Flume.Script.Tile G S.ratio.count) c from CAX y)) from funext (fun i=>by unfold cue; rw [if_pos]; have hl:= i.isLt; omega )]; exact funext fun i=> hs.symm
          have hA : d' 0 y= -jet M 3 V/4:=by erw [hx 0 h2,show library _ _ _= _ from beam3 S he U t h V]; unfold M;ring
          have hb : d' 2 y= -jet M 4 V/4:=by erw [hx 2 h3,show library _ _ _= _ from beam4 S he U t h V]; unfold M;ring
          have hu : d' 3 y=jet (HaloC S he t r A P) 2 V:=by erw [hx 3 h1,show library _ _ _= _ from beam2 S he U t h ht V r];ring
          unfold Stell brat; rw [Pi.add_apply,hA,hb,hu,blazeTok]; erw [(tight_p S he H X g p y).1]; simp only [add_zero];rfl
end YM.OPE.Cascade.Rill
