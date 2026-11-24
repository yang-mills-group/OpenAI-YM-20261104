import YM.Integration.WilsonConditionalTaylorWheelPrimaryFlag
import YM.Integration.WilsonConditionalTaylorWheelFiledMark
import YM.Integration.WilsonConditionalTaylorWheelPineQuotient

/-! Through the prespecified order the one normalized real finite WUV
response, with the authentic folded vacuum, is the same finite FVA2
response on the entire submitted joint field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelTorusReed
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open AnalyticNext.QuarticMatch.Sheets Next.Foundations
open FormalBulk08 Flat Reef Jets Orb Wick Series Next.Free MSbar.Rolling MSbar.Cacao
open Work.F03 Work.F05 Work.F08 PowerSeries Stationary Lotus Shore
open Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Winding
open WilsonMovingPolynomialPull WilsonConditionalTaylorWick
open scoped Classical Matrix BigOperators Topology
variable {G:Gauge}

theorem transport {n f:Side} (S:StepData n f) (P:Patch) (K:KernelChoices)
    (hp:S.patch=P) (hk:S.kernel=K) (u:PoleRows S.patch) (v:PoleRows P) (row:HEq u v)
    (H:FreeResolvent.FaceRow) (O:ChartRatio G) (U:Crude G) (q:ℕ) (T:Crude G):
    reed S (repeatF S) H (installed S.ratio u) O (U f) q (T f)=
      reed (stepAt P K n) (xree P K n) H (installed (stepAt P K n).ratio v) O (U (n*P.L)) q (T (n*P.L)):=by
  rcases S with ⟨p,k,hs⟩
  change p=P at hp
  change k=K at hk
  subst p;subst k
  replace hs:f=n*P.L:=Subtype.ext hs
  subst f
  obtain rfl:=eq_of_heq row
  rfl

variable (R:Run G) (simple:G.Simple) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def filed (N j q:ℕ) (T:Crude G) (n:Side):PChart G n:=
  reed (stepAt (loose V j) (V).clock.kernel n) (xree (loose V j) (V).clock.kernel n)
    (freeForms V N (j+1)) (WilsonCoeffUV.Bank.roam V N j n) R.metals.O
    (emera (actionW V R.metals.O N (j+1)) (n*(loose V j).L)) q (T (n*(loose V j).L))

include simple in
theorem received (N j per E q:ℕ) (live:j<N)
    (history:WilsonConditionalTaylorWheelVacuumHistory.Identified R u N (j+1) E)
    (T:Crude G) (shape:∀n,shellK q (T n)) (pure:∀n e,Pure (T n e)):
    let P:=destination V N j
    let n:=R.family.side j per
    let W:=Dove.model V wood b R.metals.O u N (j+1)
    Through E (Blue.flash (filed R N j q T n))
      (Reef.tossed P R.metals.O (b j) (wood j) n (tags j n) (Mesa.stone W (n*P.L)) (Blue.flash (T (n*P.L)))):=by
  intro P n W
  let S:=(V).clock.op j per
  have book:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨v,C,hv,hC,stock,-⟩:=colors G (V).clock.kernel.penalty (V).clock.kernel.penalty_pos P.legal
  have head:=stoned_main hv.le hC.le (stock P.wing).1 book.toVivid book.ink (n*P.L)
  obtain ⟨tag,_,receipt⟩:=WilsonConditionalTaylorWheelPrimaryFlag.registered S P R.metals.O R.alloy.B.ratio
    ((V).clock.adm j) (b j) rfl rfl (tags j n) (predictionA V N j) HEq.rfl (Mesa.stone W) head
  let D:WilsonConditionalTaylorWheelKernel.Stage G:=⟨R,N,j,per,live,repeatF S,tag⟩
  let f:=R.family.side (j+1) per
  have recd:=transport S (loose V j) (V).clock.kernel rfl rfl (predictionA V N j) (predictionA V N j)
    HEq.rfl (freeForms V N (j+1)) R.metals.O (emera (actionW V R.metals.O N (j+1))) q T
  change _=filed R N j q T n at recd
  intro e he
  apply MvPolynomial.funext
  intro y
  have fare:=WilsonConditionalTaylorWheelFiledMark.normalized D simple u E history q (T f) (shape f) (pure f) y
  have port:=receipt (fun v=>Blue.flash (T v)) y
  have one:=(fare e he).trans (congrArg (coeff e) (WilsonConditionalTaylorWheelPineQuotient.recorded D _ _ _))
  rw [←recd]
  exact one.trans (congrArg (coeff e) port.symm)
end YM.Integration.WilsonConditionalTaylorWheelTorusReed
end
