import YM.Integration.WilsonPositionProgramTrialPublicOldReturn
import YM.Integration.WilsonPositionProgramTrialPublicGather
import YM.Integration.WilsonMaxwellThermometerNominatedTests

/-! Exact signed test and engineering weights on the complete original K group reading at any one visited placement. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicSocketFactors
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Winding WilsonFiniteMarkedHistoryStep
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonPositionProgramTrialPublicPaidFace (amount key columns originalRow)
open WilsonReceivedDepositedVerseCensus (ordinary)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]
open WilsonPositionProgramTrialPublicOldReturn (portfolio)
open WilsonMaxwellThermometerNominatedTests (applied)
open WilsonOriginalPublicNodalPlainSensor (sensor)
open WilsonPositionProgramTrialPublicGather (ear heard)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonReceivedFixedDigitHistory (sound itinerary)

private theorem withdraw (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N K m k:ℕ)(older:m≤K)(top:K≤N)(A:Era G ℝ)(paid:Auth k A)(v:ℝ):
    cruises L O N k K m (v • A)=v • cruises L O N k K m A:=by
  have sale:=WilsonOriginalPublicNodalProfiles.sum L O simple ratio N K m k older top ({()}:Finset Unit)
    (fun _=>v) (fun _=>A) (fun _ _=>paid)
  simpa using sale

theorem linear (R:Run G)(D d:I→ℕ)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(S:Finset I)
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(A:Case D)(t:I→ℝ)(L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N:ℕ)(cells:Digits L I)(m c K:ℕ)(mc:m≤c)(cK:c≤K)(KN:K≤N)(y:I → Cover):
    portfolio R D d κ pt S fill v φ (applied t A) L O N cells m c K y=
     (∏i∈S,t i) • portfolio R D d κ pt S fill v φ A L O N cells m c K y:=by
  let B:=((i:S)→(R.family.labels.level (d i)).Index)
  let Y (b:B):=WilsonOlderFreshSoftFigures.stencil R D d (key R d S fill b) κ pt
  obtain ⟨_,_,sold⟩:=WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one
  have ready (b:B):Wellness d (Y b):=(sold (key R d S fill b) κ pt).1
  unfold portfolio
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  let Z:=levelsO (itinerary L O d N cells (K-c) c (Y b) y) S
  have qualified:=sound L O d N cells simple ratio (Y b) (ready b) (K-c) c (by omega)
  have buy:Auth (mass d S) (tuftV (touch A S) Z):=(placedO _ (qualified.level' y) S).tuft _
  have exactTest:tuftV (touch (applied t A) S) Z=(∏i∈S,t i) • tuftV (touch A S) Z:=by
    apply Prod.ext
    · funext period
      exact (WilsonMaxwellThermometerNominatedTests.ordinary t A S Z period).1
    · exact (WilsonMaxwellThermometerNominatedTests.ordinary t A S Z 1).2
  change _ • cruises L O N (mass d S) c m (tuftV (touch (applied t A) S) Z)=
    (∏i∈S,t i) • (_ • cruises L O N (mass d S) c m (tuftV (touch A S) Z))
  rw [exactTest,withdraw L O simple ratio N c m (mass d S) mc (cK.trans KN) _ buy]
  exact smul_comm .. 

theorem same (R:Run G)(W:Initialize G)(D d:I→ℕ)(cut:∀i,d i<D i)
    (S:Finset I)[Nonempty S](fill:∀i,(R.family.labels.level (d i)).Index)
    (v:∀i,(R.family.labels.level (d i)).Coeff)(φ:I→ℂ→L[ℝ]ℝ)(A A':Case D)
    (live:∀i,sensor (D i) (A i)=sensor (D i) (A' i))
    (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)(N:ℕ)(cells:Digits L I)
    (m c K:ℕ)(mc:m≤c)(cK:c≤K)(KN:K≤N)(y:I → Cover):
    portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ A L O N cells m c K y=
    portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ A' L O N cells m c K y:=by
  rw [WilsonPositionProgramTrialPublicOldReturn.original R W D d cut _ _ S fill v φ A L O simple ratio N cells m c K mc cK KN y,
    WilsonPositionProgramTrialPublicOldReturn.original R W D d cut _ _ S fill v φ A' L O simple ratio N cells m c K mc cK KN y]
  apply congrArg (cruises L O N (mass d S) K m)
  unfold columns WilsonPositionProgramTrialPublicPaidFace.cost
  have eq (i:I):claim (D i) (contact (D i)) zeroC (A i)=
      claim (D i) (contact (D i)) zeroC (A' i):=live i
  simp_rw [eq]

theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ)(cut:∀i,d i<D i)
    (S:Finset I)[Nonempty S](fill:∀i,(R.family.labels.level (d i)).Index)
    (v:∀i,(R.family.labels.level (d i)).Coeff)(φ:I→ℂ→L[ℝ]ℝ)(A:Case D)
    (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)(N:ℕ)(cells:Digits L I)
    (m c K:ℕ)(mc:m≤c)(cK:c≤K)(KN:K≤N)(y:I → Cover):
    portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ A L O N cells m c K y=
    (∏i∈S,sensor (D i) (A i)) • portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ
      (fun i=>ear (D i) 1) L O N cells m c K y:=by
  let t i:=sensor (D i) (A i)
  let basis i:=ear (D i) 1
  rw [same R W D d cut S fill v φ A (applied t basis) ?_ L O simple ratio N cells m c K mc cK KN y]
  · exact linear R D d _ _ S fill v φ basis t L O simple ratio N cells m c K mc cK KN y
  · intro i
    simp [applied,t,basis,map_smul]

end YM.Integration.WilsonPositionProgramTrialPublicSocketFactors
end

