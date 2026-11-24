import YM.Integration.WilsonPositionProgramTrialPublicPaidFace
import YM.Integration.WilsonOriginalPublicNodalTestedCore
import YM.Integration.WilsonOriginalPublicNodalProfiles

/-! Restore all real fitted K coefficients before the second conditional draw. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicOldReturn
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

def portfolio (R:Run G)(D d:I→ℕ)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(S:Finset I)
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(A:Case D)(L:Levels G)(O:ChartRatio G)(N:ℕ)(cells:Digits L I)
    (m c K:ℕ)(y:I → Cover):Era G ℝ:=
  ∑b:((i:S)→(R.family.labels.level (d i)).Index),(∏i:S,amount R d v φ i (b i)) • cruises L O N (mass d S) c m
    (WilsonOlderFreshSoftOrdinary.material D d L O (WilsonOlderFreshSoftFigures.stencil R D d
      (key R d S fill b) κ pt) N cells c K y S (touch A S))

theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(S:Finset I)[Nonempty S]
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(A:Case D)(L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N:ℕ)(cells:Digits L I)(m c K:ℕ)(mc:m≤c)(cK:c≤K)(KN:K≤N)(y:I → Cover):
    portfolio R D d κ pt S fill v φ A L O N cells m c K y=
    cruises L O N (mass d S) K m (columns R W D d cut κ pt (roots L cells (K-c) c y) S v φ A):=by
  let o:=roots L cells (K-c) c y
  let B:=((i:S)→(R.family.labels.level (d i)).Index)
  let Y (b:B):=WilsonOlderFreshSoftFigures.stencil R D d (key R d S fill b) κ pt
  obtain ⟨_,_,sold⟩:=WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one
  have ready (b:B):Wellness d (Y b):=(sold (key R d S fill b) κ pt).1
  have paid (b:B):Auth (mass d S) (ordinary (Y b o) A S):=(placedO _ ((ready b).level' o) S).tuft (touch A S)
  rw [←WilsonPositionProgramTrialPublicPaidFace.original R W D d cut κ pt o S fill v φ A]
  unfold originalRow portfolio
  rw [WilsonOriginalPublicNodalProfiles.sum L O simple ratio N K m (mass d S) (mc.trans cK) KN _ _ _
    (fun b _=>paid b)]
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg ((∏i:S,amount R d v φ i (b i)) • ·)
  exact WilsonOriginalPublicNodalTestedCore.original L O d N cells simple ratio (Y b) (ready b) m c K
    mc cK KN y S (touch A S)

end YM.Integration.WilsonPositionProgramTrialPublicOldReturn
end
