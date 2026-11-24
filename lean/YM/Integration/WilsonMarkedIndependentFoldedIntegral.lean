import YM.Integration.WilsonMarkedPreResetMaterialHistory
import YM.Integration.WilsonVacuumPreResetFoldedCopyMoments
import YM.Integration.WilsonConditionalTaylorWheelTensors

/-! Finite normalized marked integral with the folded previous Wilson action at every side. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentFoldedIntegral
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open AnalyticNext.QuarticMatch.Sheets
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Soil
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)

def folded (N j q:ℕ)(T:Crude G)(n:Side):PChart G n:=
  let P:=loose V j
  reed (stepAt P (V).clock.kernel n) (xree P (V).clock.kernel n) (freeForms V N (j+1))
    (WilsonCoeffUV.Bank.roam V N j n) R.metals.O (emera (actionW V R.metals.O N (j+1)) (n*P.L)) q (T (n*P.L))

def upper (N j q:ℕ)(Z:Mesa.Pot G):Mesa.Pot G:=
  windsT (loose V j) (V).clock.kernel R.metals.O (shuttleM (conditional V N j))
    (shuttleM (feedA V N j)) (actionW V R.metals.O N (j+1)) q Z

theorem recorded (simple:G.Simple){N j:ℕ}(live:j<N)(q e r:ℕ)(T:Era G ℝ)(auth:Auth q T):
    Bends 0 (fun n=>folded R N j q T.1 n e r) (upper R N j q T.2 e r):=by
  exact river (loose V j) (V).clock.kernel R.metals.O _ _ _ (b j) R.alloy.B.ratio (resin V N j live)
    (fun a t=>WilsonVacuumPreResetFoldedCopyMoments.inlet R simple (N:=N) (m:=j+1) live a t)
    q 0 (U:=T.1) (fun i t=>by rw [coat0];exact auth.wing i t) e r

variable (u:G.ColorIndex) (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

theorem finite (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N)(q:ℕ)(T:Mer.Era G ℝ)(auth:Auth q T)(n:Side):
    let P:=destination V N j
    let W:=Dove.model V wood b R.metals.O u N (j+1)
    Blue.flash (folded R N j q T.1 n)=Reef.tossed P R.metals.O (b j) (wood j) n (tags j n)
      (Mesa.stone W (n*P.L)) (Blue.flash (T.1 (n*P.L))):=by
  intro P W
  let S:=primary (P).patch (V).clock.kernel n
  let F:=Reef.floor (V).clock.kernel P (wood j) n
  let f:=n*(P).patch.L
  let Y:=freeForms V N (j+1)
  let X:=emera (actionW V R.metals.O N (j+1)) f
  let M:=installed S.ratio (predictionA V N j)
  have prior:=(WilsonVacuumPreResetIndependentHistory.original R u simple v funded tags N (j+1) live).1
  have fold:-Blue.flash X=Mesa.stone W f:=Through.top fun e=>
    WilsonVacuumPreResetCanonicalPrefix.retained R simple N (j+1) live W e (fun a _ r _=>prior a r) f
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  have head:coeff 0 (-Blue.flash X)=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing f):=by
    rw [fold]
    obtain ⟨s,C,hs,hc,hv,-⟩:=colors G (V).clock.kernel.penalty (V).clock.kernel.penalty_pos P.legal
    exact Mesa.stoned_main hs.le hc.le (hv _).1 dossier.toVivid dossier.ink _
  have old:=emera_far V simple R.alloy.B.ratio (N:=j+1) (m:=N) live f
  have marked:=WilsonMarkedPreResetCanonicalBlock.normalized P (b j) (wood j) n R.metals.O R.alloy.B.ratio
    ((V).clock.adm j) (tags j n) Y rfl X old.1 head (age_sym V ..) old.2 q (T.1 f) (auth.span f) (auth.pale f)
  have fix:repeatF S=F:=WilsonConditionalTaylorWheelCanonicalForest.original S
  change Blue.flash (reed S (repeatF S) Y M R.metals.O X q (T.1 f))=_
  rw [fix]
  exact (marked.trans (congrArg (fun A=>Reef.tossed P R.metals.O (b j) (wood j) n (tags j n) A (Blue.flash (T.1 f))) fold))

end YM.Integration.WilsonMarkedIndependentFoldedIntegral
end
