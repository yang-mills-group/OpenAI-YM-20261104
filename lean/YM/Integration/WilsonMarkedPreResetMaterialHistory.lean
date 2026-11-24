import YM.Integration.WilsonMarkedPreResetCanonicalBlock
import YM.Integration.WilsonConditionalTaylorWheelClassicalHead
import YM.Integration.WilsonConditionalTaylorWheelCanonicalForest
import YM.Integration.WilsonVacuumPreResetIndependentHistory

/-! Complete positive-order occupied integral on the original finite Wilson history. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedPreResetMaterialHistory
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open AnalyticNext.QuarticMatch.Sheets
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}

variable (R:Run G) (simple:G.Simple)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def energy (N j:ℕ) (n:Side):Pap (wire G n):= -Blue.flash ((story V R.metals.O N j).1 n)

include simple in
theorem head (N j:ℕ) (hi:j≤N) (n:Side):
    coeff 0 (energy R N j n)=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty (location V N j) n):=by
  have enrolled:=((WilsonCoeffUV.Bank.old V R.metals.O simple R.alloy.B.ratio N j hi).basis n).stem
  rw [energy,map_neg,Blue.flash,coeff_mk,enrolled,Blue.visible_shine]
  exact WilsonConditionalTaylorWheelClassicalHead.kernel R N j n

def before (N j q:ℕ) (T:Crude G) (n:Side):PChart G n:=
  let P:=loose V j
  reed (stepAt P (V).clock.kernel n) (xree P (V).clock.kernel n) (freeForms V N (j+1))
    (WilsonCoeffUV.Bank.roam V N j n) R.metals.O ((story V R.metals.O N (j+1)).1 (n*P.L)) q (T (n*P.L))


include simple in
theorem received (N j q:ℕ) (live:j<N) (T:Crude G) (shape:∀n,shellK q (T n))
    (pure:∀n e,Pure (T n e)) (n:Side):
    let P:=destination V N j
    Blue.flash (before R N j q T n)=Reef.tossed P R.metals.O (b j) (wood j) n (tags j n)
      (energy R N (j+1) (n*P.L)) (Blue.flash (T (n*P.L))):=by
  intro P
  let S:=primary (P).patch (V).clock.kernel n
  let F:=Reef.floor (V).clock.kernel P (wood j) n
  let f:=n*(P).patch.L
  let Y:=freeForms V N (j+1)
  let X:=(story V R.metals.O N (j+1)).1 f
  let M:=installed S.ratio (predictionA V N j)
  have dossier:=(WilsonCoeffUV.Bank.old V R.metals.O simple R.alloy.B.ratio N (j+1) live).basis f
  have given:=head R simple N (j+1) live f
  change coeff 0 (-Blue.flash X)=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing f) at given
  have marked:=WilsonMarkedPreResetCanonicalBlock.normalized P (b j) (wood j) n R.metals.O R.alloy.B.ratio
    ((V).clock.adm j) (tags j n) Y rfl X dossier.lamp given (age_sym V ..) dossier.shape q (T f) (shape f) (pure f)
  have fix:repeatF S=F:=WilsonConditionalTaylorWheelCanonicalForest.original S
  change Blue.flash (reed S (repeatF S) Y M R.metals.O X q (T f))=_
  rw [fix]
  exact marked

end YM.Integration.WilsonMarkedPreResetMaterialHistory
end
