import YM.Integration.WilsonOlderFreshSoftSocketSourceDeposits
import YM.Integration.WilsonPositionProgramTrialPublicOldReturn

/-! A single genuine public source projection on its own K-ancestral sites.
The complete thermal read includes the accumulated old scalar and every
positive-to-unit contribution before the independently chosen stopping date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketPublicDose
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


open WilsonOlderFreshSoftSocketSourceDeposits (paidScalar split)
open WilsonOlderFreshSoftOrdinary (material)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftRoseScalarLedger (front)
open WilsonOlderFreshSoftFigures (stencil)
open WilsonOlderFreshSoftSocketTotal (listen)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedFixedDigitHistory (sound)
open WilsonCoeffUV.Winding
open WilsonCoeffUV.Soil
open WilsonIndependentCollarRootedWidth

theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(S:Finset I)[Nonempty S]
    (fill:∀i,(R.family.labels.level (d i)).Index)(x:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(A:Case D)(L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N:ℕ)(routes:Digits L I)(v w c K:ℕ)(vw:v≤w)(wc:w≤c)(ck:c≤K)(kn:K≤N)(y:I → Cover)(j:ℕ)(θ:ℝ):
    let source b:=material D d L O (stencil R D d (key R d S fill b) κ pt) N routes c K y S (touch A S)
    let income (b:(i:S)→(R.family.labels.level (d i)).Index):=∏ i:S,amount R d x φ i (b i)
    flat (cruises L O N (mass d S) K v (columns R W D d cut κ pt (roots L routes (K-c) c y) S x φ A)) j θ=
      ∑b,income b*(paidScalar L O N (mass d S) c w v (source b) j θ+
        flat (cruises L O N (mass d S) w v (axeR (front L O N (mass d S) c w (source b)))) j θ):=by
  classical
  intro source income
  rw [←WilsonPositionProgramTrialPublicOldReturn.original R W D d cut κ pt S fill x φ A L O simple ratio
    N routes v c K (vw.trans wc) ck kn y]
  change (listen j θ) (∑b,income b • cruises L O N (mass d S) c v (source b))=_
  rw [map_sum]
  apply sum_congr rfl
  intro b _
  rw [map_smul,smul_eq_mul]
  congr 1
  let Y:=stencil R D d (key R d S fill b) κ pt
  have lawful:Wellness d Y:=((WilsonOlderFreshSoftFigures.original R D d 0 (w:=1) zero_lt_one).choose_spec.2
    (key R d S fill b) κ pt).1
  have permitted:=sound L O d N routes simple ratio Y lawful (K-c) c (by omega)
  have valid:Auth (mass d S) (source b):=(placedO _ (permitted.level' y) S).tuft (touch A S)
  have signed:=split L O simple ratio N (mass d S) c w v vw wc (ck.trans kn) (source b) valid j θ
  change flat (front L O N (mass d S) c v (source b)) j θ=_
  linarith only [signed]

end YM.Integration.WilsonOlderFreshSoftSocketPublicDose
end
