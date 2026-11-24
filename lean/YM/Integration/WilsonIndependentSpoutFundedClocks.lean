import YM.Integration.WilsonIndependentSpoutChronologicalClock
import YM.Integration.WilsonIndependentSpoutClockWitness

/-! Positive finite-order real clock realization of the complete old
Wilson history on all pages of one Run, including the native kinetic
response and its parity. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFundedClocks
open PowerSeries WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue RegulatorIR
open RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open RG RegulatorIR.Ward RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Binding RegulatorIR.Pupil
open RegulatorIR.Profiles RegulatorIR.Oracle RegulatorIR.Momentum Precision
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open WilsonIndependentSpoutKineticToken
variable {G:Gauge}{W:Type}{d:W→ℕ}(A:W→Levels G)(Ñ:ChartRatio G)(s:W→ℕ)

def age (v:Page d) : ℕ:=s v.bindW+(d v.bindW-v.downW)

def clock (v:Page d):Writing:=
  relativeC (A v.bindW) Ñ (s v.bindW+d v.bindW) (age s v) v.downW

theorem original (simple:G.Simple)(ratio:LocalRatio Ñ)(p:ℕ):
    ∃K:Tent d,(∀w,K (Page.opening d w)=Calibration.dawn)∧∀v,
      Squares p (tale (K v).dine) (clock A Ñ s v)∧
      Squares p (tale (sheet K v).beta) (((clock A Ñ s v)⁻¹)^2)∧
      Seconds (sheet K v) p∧
      ∀e≤p,∀c:G.ColorIndex,Rules.token (direct (mix (clock A Ñ s v)
        (actionW (A v.bindW) Ñ (s v.bindW+d v.bindW) (age s v)) e 2)) c=
        biases (sheet K v) e:=by
  have hit (v:Page d):age s v+v.downW ≤ s v.bindW+d v.bindW:=by
    have h:=v.good;unfold age;omega
  have unit (v:Page d):constantCoeff (clock A Ñ s v)=1:=angularC simple ratio (hit v)
  have bare (w:W):clock A Ñ s (Page.opening d w)=1:=rfl
  obtain ⟨K,start,cash⟩:=WilsonIndependentSpoutClockWitness.original p (clock A Ñ s) unit bare
  refine ⟨K,start,fun v=>⟨(cash v).1,(cash v).2,?_,?_⟩⟩
  · have even:evenC (clock A Ñ s v):=WilsonIndependentSpoutChronologicalClock.parity
      (A v.bindW) Ñ simple ratio (hit v)
    intro i hi odd
    exact ((cash v).2 i hi).trans (even_pow (even_inv even (unit v)) 2 i (by omega))
  · intro e he c
    exact (WilsonIndependentSpoutKineticReading.income (A v.bindW) Ñ simple ratio
      (Nat.le_trans (Nat.le_add_right _ _) (hit v)) _ (unit v) e c).trans ((cash v).2 e he).symm

end YM.Integration.WilsonIndependentSpoutFundedClocks
