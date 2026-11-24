import YM.Integration.WilsonPositionProgramTrialPublicOldReturn
import YM.Integration.WilsonPositionProgramTrialPublicJoint
import YM.Integration.WilsonOriginalPublicNodalMeasuredSensor

/-! Each native test visit uses its own true K site and unchanged earlier vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicVisits
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil
open WilsonFiniteMarkedHistoryStep
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonOriginalPublicNodalChildSites (digits here)
open WilsonOriginalPublicNodalPlainSensor (sensor)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonPositionProgramTrialPublicGather (gather ear)
open WilsonPositionProgramTrialPublicOldReturn (portfolio)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentRawPhysicalFaces (ordered)
open WilsonOriginalPhysicalFruitVerse (written)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem atRoot (L:Levels G)(K c:ℕ)(cK:c≤K)(o:I → Cover):
    roots L (digits L K o) (K-c) c (here L K o c)=o:=by
  have track (days j:ℕ)(before:j+days≤K):
      roots L (digits L K o) days j (here L K o j)=here L K o (j+days):=by
    induction days generalizing j with
    | zero=>rfl
    | succ n ih=>
      rw [roots,WilsonOriginalPublicNodalChildSites.next L K o (by omega),ih (j+1) (by omega)]
      rw [show j+1+n=j+(n+1) by omega]
  rw [track _ _ (by omega),show c+(K-c)=K by omega,WilsonOriginalPublicNodalChildSites.here,
    dif_neg (lt_irrefl K)]

theorem sameSensor (R:Run G)(W:Initialize G){d D:ℕ}(fit:d<D)(B:Volume D)
    (v:(R.family.labels.level d).Coeff)(φ:ℂ→L[ℝ]ℝ)(o:Cover):
    planted R W false fit (ear D (sensor D B)) (written _ v φ) o=
    planted R W false fit B (written _ v φ) o:=by
  rw [WilsonPositionProgramTrialPublicSticker.original,WilsonPositionProgramTrialPublicSticker.original]
  simp only [WilsonPositionProgramTrialPublicSticker.paidWord,WilsonPositionProgramTrialPublicGather.heard]

theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ)(cut:∀i,d i<D i)(S:Finset I)[Nonempty S]
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(A:Case D)(L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N m c K:ℕ)(mc:m≤c)(cK:c≤K)(KN:K≤N)(o:I → Cover):
    portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ A L O N (digits L K o)
      m c K (here L K o c)=
    cruises L O N (mass d S) K m (gather (fun i:S=>planted R W false (cut i) (A i)
      (written _ (v i) (φ i)) (o i)) ordered):=by
  rw [WilsonPositionProgramTrialPublicOldReturn.original R W D d cut _ _ S fill v φ A L O simple ratio N
    (digits L K o) m c K mc cK KN,atRoot L K c cK o,←WilsonPositionProgramTrialPublicJoint.original]
  apply congrArg (cruises L O N (mass d S) K m)
  apply congrArg (fun P=>gather P (ordered (I:=S)))
  funext i
  exact sameSensor R W (cut i) (A i) (v i) (φ i) (o i)

end YM.Integration.WilsonPositionProgramTrialPublicVisits
end
