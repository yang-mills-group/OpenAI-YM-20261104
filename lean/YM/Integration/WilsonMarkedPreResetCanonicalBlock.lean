import YM.Integration.WilsonMarkedPreResetCommonMarginal
import YM.Integration.WilsonVacuumPreResetCanonicalBlock

/-! Exact normalization of the original marked marginal against the same quiet vacuum on the block. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedPreResetCanonicalBlock
open Function Matrix Lattice Laurent Wilson RG Precision Tree Bloch Exterior PowerSeries
open Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets
open FormalBulk08.Wick FormalBulk08.Lotus FormalBulk08.Mesa Next.Free
open scoped Classical BigOperators Matrix
variable {G:Gauge}{K:KernelChoices}{j t:ℕ}(P:Flight j t)
variable (br:P.patch.Branches K G)(L:Lodge P.patch)(n:Side)
set_option quotPrecheck false in
local notation "S" => primary P.patch K n
set_option quotPrecheck false in
local notation "F" => Reef.floor K P L n
set_option quotPrecheck false in
local notation "E" => Reef.pines (G:=G) F
set_option quotPrecheck false in
local notation "H" => Reef.ferry P br L n
set_option quotPrecheck false in
local notation "D" => Turner.door E (H).saddle
set_option quotPrecheck false in
local notation "M" => installed (S).ratio (P.duo K.penalty).A0

theorem normalized (O:ChartRatio G)(law:LocalRatio O)(ht:4≤t)(k:(S).Choices)
    (Y:FaceRow)(same:Precision.K (Y.acts (n*P.patch.L))=Precision.K ((pink K.penalty P.wing).acts (n*P.patch.L)))
    (X:PChart G (n*P.patch.L))(shape:shellK 2 X)(head:coeff 0 (-flash X)=Reef.crunch (Reef.kernelP G K.penalty P.wing _))
    (sym:(Y.acts (n*P.patch.L)).transpose=Y.acts (n*P.patch.L))(pure:∀d,Pure (X d))
    (q:ℕ)(T:PChart G (n*P.patch.L))(bounded:shellK q T)(smooth:∀d,Pure (T d)):
    flash (reed S F Y M O X q T)=Reef.tossed P O br L n k (-flash X) (flash T):=by
  have dm (y:Rays (wire G n)):(fun v=>traceP y ((H).drift v))=Flat.rawMean G S F M *ᵥ y:=
    Reef.draught_fee (Reef.pMean G K P n F) y
  have solved:=Reef.consolidate P O br L n law k (-flash X) head ht
  let p:=Reef.flush F k O (-flash X)
  have cash:Orb.vocal H p≠0:=by
    intro zero
    have paid:=Orb.voice H p solved
    rw [zero,map_zero] at paid
    exact zero_ne_one paid
  have quiet:=WilsonVacuumPreResetCanonicalBlock.observed P br L n O law ht k Y same X shape head
  have placed:=WilsonMarkedPreResetCommonMarginal.joint S F M H dm O law X shape br k D rfl solved (flash T)
  apply mul_left_cancel₀ cash
  change Orb.vocal H p*flash (reed S F Y M O X q T)=Orb.vocal H p*Orb.flag H p (Reef.seat F (flash T))
  rw [←quiet,←inside_reed S F Y M q shape law bounded br sym pure smooth,quiet]
  unfold insideMark
  rw [WilsonVacuumPreResetCanonicalBlock.precision P br L n Y same,WilsonConditionalTaylorWheelHeat.full]
  exact placed

end YM.Integration.WilsonMarkedPreResetCanonicalBlock
