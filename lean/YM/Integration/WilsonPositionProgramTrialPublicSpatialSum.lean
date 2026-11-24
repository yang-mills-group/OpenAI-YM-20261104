import YM.Integration.WilsonPositionProgramTrialPublicVisits
import YM.Integration.WilsonIndependentMatchedOpeningProfile
import YM.Integration.WilsonIndependentMatchedOpeningMass

/-! The original compact pulse and its actual independent normalized pupil have the same spatial sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicSpatialSum
open Function Finset Lattice RG Wilson Precision Laurent Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Flooring WilsonFiniteMarkedHistoryStep
open WilsonIndependentMatchedOrdinarySeat (here)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentRawRosterWord (fold)
open WilsonPositionProgramTrialPublicGather (gather)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonOriginalPublicNodalPlainSensor (sensor)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}

theorem scale (R:Run G)(W:Initialize G){d D:ℕ}(fit:d<D)(v:(R.family.labels.level d).Coeff)
    (φ:ℂ→L[ℝ]ℝ)(x:ℝ)(T:Volume D)(o:Cover):
    planted R W false fit (x • T) (written _ v φ) o=x • planted R W false fit T (written _ v φ) o:=by
  rw [WilsonPositionProgramTrialPublicSticker.original,WilsonPositionProgramTrialPublicSticker.original]
  unfold WilsonPositionProgramTrialPublicSticker.paidWord
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [WilsonIndependentMatchedOpeningComposite.money,map_smul,smul_eq_mul,map_mul]
  ring_nf

def visit (D:ℕ)(φ:Rarity D)(x y:ℝ)(o:CellR):Type:=↥(VisitsT φ x y o)
instance (D:ℕ)(φ:Rarity D)(x y:ℝ)(o:CellR):Fintype (visit D φ x y o):=
  inferInstanceAs (Fintype (↥(VisitsT φ x y o)))

def held (D:ℕ)(φ:Rarity D)(x y:ℝ)(o:CellR)(d:ℕ)(z:Cover):Volume D:=
  drumB d x • wheelC x y z φ.ψ o

theorem leg (R:Run G)(W:Initialize G){d D:ℕ}(cut:d<D)(v:(R.family.labels.level d).Coeff)
    (φ:ℂ→L[ℝ]ℝ)(T:Rarity D)(x y:ℝ)(o:CellR)(positive:0<x):
    word (Shrine (plate (sectionAt R W false d) cut) (written _ v φ)) T x y o d=
    ∑z:visit D T x y o,planted R W false cut (held D T x y o d z.val) (written _ v φ) z.val:=by
  rw [WilsonIndependentMatchedOpeningProfile.original R W false cut _ T x y o d positive]
  change _=∑z:↥(VisitsT T x y o),_
  rw [←Finset.sum_coe_sort (VisitsT T x y o)]
  apply Finset.sum_congr rfl
  intro z _
  rw [held,scale,WilsonIndependentMatchedOpeningFiled.original]

theorem combine {I:Type}[DecidableEq I][Fintype I][Nonempty I]
    (J:I→Type)[∀i,Fintype (J i)](d:I→ℕ)(X:(i:I)→J i→Era G ℝ)
    (paid:∀i z,Auth (d i) (X i z)):
    gather (fun i=>∑z,X i z) ordered=∑z:((i:I)→J i),gather (fun i=>X i (z i)) ordered:=by
  let H:=(ordered (I:=I)).accounts d
  have all (i:I):Auth (d i) (∑z,X i z):=Auth.sum fun z _=>paid i z
  have ready (z:(i:I)→J i):Auth H (gather (fun i=>X i (z i)) ordered):=
    WilsonPositionProgramTrialPublicGather.funded _ d (fun i=>paid i (z i)) ordered
  apply WilsonIndependentMatchedOpeningFaithful.original
    (WilsonPositionProgramTrialPublicGather.funded _ d all ordered) (Auth.sum fun z _=>ready z)
  intro n v
  rw [WilsonPositionProgramTrialPublicGather.read _ d all n v ordered,
    WilsonIndependentMatchedOpeningMass.sum _ _ H ready n v,entered.product]
  simp_rw [WilsonIndependentMatchedOpeningMass.sum _ _ _ (paid _) n v]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [WilsonPositionProgramTrialPublicGather.read _ d (fun i=>paid i (z i)) n v ordered,entered.product]

end YM.Integration.WilsonPositionProgramTrialPublicSpatialSum
end
