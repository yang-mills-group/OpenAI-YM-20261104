import YM.OPE.Compatible.Ivy.Aim
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
-- universal
private abbrev boxR (P: Patch)(K:KernelChoices)(b:ℝ)(R:PathData G)(c:Clip)(C: ChartRatio G): Story (Flume.Script.Tile G P.L):= ⟨tide3 P K R c,tide4 P K R c,tide2 P K R c C b⟩
def mintR (A:Alps K T i v)(p:ChartRatio G)(b:ℝ): Story (Flume.Script.Tile G S.patch.L):=boxR S.patch S.kernel b A.live A.clip p
-- marker raw on Fine Shade
abbrev Muse (G:Gauge):= Spring (Shade G)
def branchOut (P:Patch)(G:Gauge)(q:Muse G): Spring (Flume.Script.Tile G P.L):= moveS (drip G P.L) 0 q
def shapeOut (P:Patch)(A: Row (Flume.Script.Tile G P.L) (Shade G))(q:Spring (Flume.Script.Tile G P.L)):Muse G:= moveS (marry A) 0 q
-- evaluation bridges
lemma graphdam (p:Site c)(k:ℕ)(x:S!)(q:Muse G)(ha:∀ i,Bins (q i)): Libra.Char.go (branchOut S.patch G q) k (dance S he G x) p= Libra.Char.go q k (spool G f (ribz S he x)) (S.ratio.embed p):=by
      let A:Cross S.ratio.count _ _ := drip G S.ratio.count; let Y:=dance S he G x; have ht:branchOut S.patch G q=moveS A 0 q:=rfl
      erw [ht, movedV S.ratio A 0 q Y p k ha (drip_cash ..), paintDrip S he x,map_zero, add_zero]; try rfl
lemma sameSide (n:Side)(p:Site n)(l:ℕ)(A: Patch)(q:Spring (Flume.Script.Tile G A.L))(ha:∀ i,Bins (q i))(v:deck (Shade G) n)(x: Row (Flume.Script.Tile G A.L) (Shade G))(h:Whole x): Libra.Char.go (shapeOut A x q) l v p=Libra.Char.go q l (x.acts n *ᵥ v) p:=by
      let T:=shrinkS n; unfold shapeOut;erw [movedV T (marry x) _ _ _ _ l ha (payact x h),marries,map_zero,add_zero]; have he:T.embed p=p:=by rw [← wrap_lift p, Ratio.embed_wrap,show T.count.val=1 from rfl,one_smul]
      rw [he]
include h U t
lemma flightN {p:Site c}(k:ℕ)(q:Muse G)(ha: ∀ i,Bins (q i))(x:P!)(y:J!):
      let X':= dance S he G (fieldT (cabin g) (rayS H X G x))
      let v:= Tight S he H X g (x,y)
      cups (branchOut S.patch G q) k p X' CAX y= Libra.Char.go q k (spool G f (ribz S he (lamps S he H X G v))) (S.ratio.embed p):=by
         intro X' v; change Libra.Char.go _ k (X'+ CAX y) p=_; rw [show X'+ CAX y=dance S he G (lamps S he H X G v) from ?_]; exact graphdam S he p k _ _ ha
         rw [tight_ray S he H X g U h t x y]; exact (map_add (dance S he G) _ _).symm
end YM.OPE.Cascade.Rill
