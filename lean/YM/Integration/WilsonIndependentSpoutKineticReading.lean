import YM.Integration.WilsonIndependentSpoutKineticExchange
import YM.Integration.WilsonIndependentSpoutKineticToken

/-! The actual elected color sees the positive-order compensated vacuum
bias on both clocks, including the reversal of the two tensor slots. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutKineticReading
open Lattice RG Exterior WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue RegulatorIR
open RegulatorIR.Budget RegulatorIR.Prim RegulatorIR.Pupil RegulatorIR.Momentum
open Precision PowerSeries WilsonIndependentSpoutKineticToken
open scoped Classical BigOperators
variable {G:Gauge}

theorem physical {P:Canvas G}(H:swing P)(j:ℕ)(c:G.ColorIndex):
    Rules.token (direct (P j 2)) c=azur (P j 2) c := by
  rw [←reversed]
  unfold Rules.token Pupil.shine recital
  apply tsum_congr
  intro x
  apply congrArg (fun t:ℝ=>t*(dial (step 0) x)^2)
  have slots:placed ∘ ![ask 0 ((1:Axis),c),ask x ((1:Axis),c)]=
      ![stone (0,1) c,stone (x,1) c] := by funext i;fin_cases i <;> rfl
  unfold Pupil.starE Pupil.twin direct
  rw [slots]
  change -P j 2 ![stone (0,1) c,stone (x,1) c] =
      -P j 2 ![stone (x,1) c,stone (0,1) c]
  rw [WilsonIndependentSpoutKineticExchange.actual H j x c]

private lemma uniformColor {P:Canvas G}(paid:leanTwo P)(α:PowerSeries ℝ)(e:ℕ)
    (z:Cover)(c d:G.ColorIndex):
    Blue.mix α P e 2 ![stone (z,1) c,stone (0,1) c] =
      Blue.mix α P e 2 ![stone (z,1) d,stone (0,1) d] := by
  simp only [Blue.mix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨k,h⟩:=paid j (z,1) (0,1)
  rw [h c c,h d d]
  simp

theorem selected {P:Canvas G}(H:swing P)(paint:leanTwo P)(α:PowerSeries ℝ)
    (e:ℕ)(c:G.ColorIndex):
    Rules.token (direct (Blue.mix α P e 2)) c = readSun (Blue.mix α P e 2) := by
  let any:Nonempty G.ColorIndex:=⟨c⟩
  rw [physical (WilsonIndependentSpoutKineticExchange.changed H α),read_azur _ any]
  unfold azur tailor
  congr 1
  apply tsum_congr
  intro z
  exact congrArg (fun t:ℝ=>(chalk 0*chalk 0) z*t) (uniformColor paint α e z c any.some)

theorem income (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(chart:LocalRatio Ñ)
    {N m:ℕ}(le:m≤N)(α:PowerSeries ℝ)(unit:constantCoeff α=1)(e:ℕ)(c:G.ColorIndex):
    Rules.token (direct (Blue.mix α (actionW A Ñ N m) e 2)) c=coeff e ((α⁻¹)^2) := by
  have H:=catchment A Ñ simple chart le
  rw [selected H.signs H.paintU]
  rw [←stellar_read,WilsonIndependentSpoutUnmarkedClock.original A Ñ simple chart le α unit]

end YM.Integration.WilsonIndependentSpoutKineticReading
