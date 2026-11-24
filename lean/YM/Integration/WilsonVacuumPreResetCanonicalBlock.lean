import YM.Integration.WilsonVacuumPreResetIndependentMarginal

/-! The held vacuum in the two independently presented block integrals on the native forest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCanonicalBlock
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
theorem precision (Y:FaceRow)
    (same:Precision.K (Y.acts (n*P.patch.L))=Precision.K ((pink K.penalty P.wing).acts (n*P.patch.L))):
    treeInverse G S F Y 0=(D).q:=by
  let T:=Flat.testPrecision G S F P.wing
  obtain ⟨pos,paid⟩:=Reef.honey P br L n
  have inv:T⁻¹=(H).saddle.q:=
    left_inv_eq_right_inv (Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr pos.det_pos.ne')) paid
  have full:=MSFixedRatioGaussianGeometry.restricted (G:=G) S F P.wing Y same
  have selected:T.submatrix E E=treeMatrix G S F Y:=by
    simpa only [MSFixedRatioGaussianGeometry.address,Reef.pines] using full
  change resolve (treeMatrix G S F Y) 0=(H).saddle.q.submatrix E E
  rw [resolve,zero_smul,add_zero,←selected,←inv,Matrix.inv_submatrix_equiv]

theorem observed (O:ChartRatio G)(law:LocalRatio O)(ht:4≤t)(k:(S).Choices)
    (Y:FaceRow)(same:Precision.K (Y.acts (n*P.patch.L))=Precision.K ((pink K.penalty P.wing).acts (n*P.patch.L)))
    (X:PChart G (n*P.patch.L))(shape:shellK 2 X)
    (head:coeff 0 (-flash X)=Reef.crunch (Reef.kernelP G K.penalty P.wing _)):
    inside S F Y M O X=Orb.vocal H (Reef.flush F k O (-flash X)):=by
  have dm (y:Rays (wire G n)):(fun v=>traceP y ((H).drift v))=Flat.rawMean G S F M *ᵥ y:=
    Reef.draught_fee (Reef.pMean G K P n F) y
  have solved:=Reef.consolidate P O br L n law k (-flash X) head ht
  rw [WilsonCoeffUV.inside,precision P br L n Y same,WilsonConditionalTaylorWheelHeat.full]
  exact WilsonVacuumPreResetIndependentMarginal.integrated S F M H dm O law X shape br k D rfl solved

end YM.Integration.WilsonVacuumPreResetCanonicalBlock
