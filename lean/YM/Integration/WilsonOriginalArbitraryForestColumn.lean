import YM.Integration.WilsonMarkedPreResetCanonicalBlock
import YM.Integration.WilsonNeutralNormalizedForestStep

/-! Read the same normalized marked Gaussian on each forest of the admitted complete program. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalArbitraryForestColumn
open Function Matrix Lattice Laurent Wilson RG Precision Tree Bloch Exterior PowerSeries
open Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets
open FormalBulk08.Wick FormalBulk08.Lotus FormalBulk08.Mesa Next.Free
open scoped Classical BigOperators Matrix
variable {G:Gauge}{K:KernelChoices}{j t:ℕ}(P:Flight j t)
open WilsonNeutralNormalizedForestStep (chamber)
variable (br:P.patch.Branches K G)(n:Side)
local notation "S" => primary P.patch K n
variable (F:Forest (primary P.patch K n).ratio)(tag:(primary P.patch K n).Choices)
local notation "E" => Reef.pines (G:=G) F
local notation "H" => chamber P br n F tag
local notation "D" => Turner.door E (H).saddle
local notation "M" => installed (S).ratio (P.duo K.penalty).A0
theorem precision (Y:FaceRow)
    (same:Precision.K (Y.acts (n*P.patch.L))=Precision.K ((pink K.penalty P.wing).acts (n*P.patch.L))):
    treeInverse G S F Y 0=(D).q:=by
  let T:=Flat.testPrecision G S F P.wing
  have inv:T⁻¹=(H).saddle.q:=rfl
  have full:=MSFixedRatioGaussianGeometry.restricted (G:=G) S F P.wing Y same
  have selected:T.submatrix E E=treeMatrix G S F Y:=by
    simpa only [MSFixedRatioGaussianGeometry.address,Reef.pines] using full
  change resolve (treeMatrix G S F Y) 0=(H).saddle.q.submatrix E E
  rw [resolve,zero_smul,add_zero,←selected,←inv,Matrix.inv_submatrix_equiv]

theorem observed (O:ChartRatio G)(law:LocalRatio O)(ht:4≤t)
    (Y:FaceRow)(same:Precision.K (Y.acts (n*P.patch.L))=Precision.K ((pink K.penalty P.wing).acts (n*P.patch.L)))
    (X:PChart G (n*P.patch.L))(shape:shellK 2 X)
    (head:coeff 0 (-flash X)=Reef.crunch (Reef.kernelP G K.penalty P.wing _)):
    inside S F Y M O X=Orb.vocal H (Reef.flush F tag O (-flash X)):=by
  have dm (y:Rays (wire G n)):(fun v=>traceP y ((H).drift v))=Flat.rawMean G S F M *ᵥ y:=
    Reef.draught_fee (Reef.pMean G K P n F) y
  have solved:=Reef.baked G K P n F ht br O law tag (H).saddle rfl (-flash X) head
  rw [WilsonCoeffUV.inside,precision P br n F tag Y same,WilsonConditionalTaylorWheelHeat.full]
  exact WilsonVacuumPreResetIndependentMarginal.integrated S F M H dm O law X shape br tag D rfl solved


theorem normalized (O:ChartRatio G)(law:LocalRatio O)(ht:4≤t)
    (Y:FaceRow)(same:Precision.K (Y.acts (n*P.patch.L))=Precision.K ((pink K.penalty P.wing).acts (n*P.patch.L)))
    (X:PChart G (n*P.patch.L))(shape:shellK 2 X)(head:coeff 0 (-flash X)=Reef.crunch (Reef.kernelP G K.penalty P.wing _))
    (sym:(Y.acts (n*P.patch.L)).transpose=Y.acts (n*P.patch.L))(pure:∀d,Pure (X d))
    (q:ℕ)(T:PChart G (n*P.patch.L))(bounded:shellK q T)(smooth:∀d,Pure (T d)):
    flash (reed S F Y M O X q T)=Orb.flag H (Reef.flush F tag O (-flash X)) (Reef.seat F (flash T)):=by
  have dm (y:Rays (wire G n)):(fun v=>traceP y ((H).drift v))=Flat.rawMean G S F M *ᵥ y:=
    Reef.draught_fee (Reef.pMean G K P n F) y
  have solved:=Reef.baked G K P n F ht br O law tag (H).saddle rfl (-flash X) head
  let p:=Reef.flush F tag O (-flash X)
  have cash:Orb.vocal H p≠0:=by
    intro zero
    have paid:=Orb.voice H p solved
    rw [zero,map_zero] at paid
    exact zero_ne_one paid
  have quiet:=observed P br n F tag O law ht Y same X shape head
  have placed:=WilsonMarkedPreResetCommonMarginal.joint S F M H dm O law X shape br tag D rfl solved (flash T)
  apply mul_left_cancel₀ cash
  change Orb.vocal H p*flash (reed S F Y M O X q T)=Orb.vocal H p*Orb.flag H p (Reef.seat F (flash T))
  rw [←quiet,←inside_reed S F Y M q shape law bounded br sym pure smooth,quiet]
  unfold insideMark
  rw [precision P br n F tag Y same,WilsonConditionalTaylorWheelHeat.full]
  exact placed

end YM.Integration.WilsonOriginalArbitraryForestColumn
