import YM.Integration.WilsonOlderFreshSoftFigureReading
import YM.Integration.WilsonOlderFreshSoftCoverScalar

/-! The terminal hearing values the previously deposited one-name scalar with its own dated changes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftCoveredRead
open Function Filter Finset Lattice RG Laurent Wilson Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Bank
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Power
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOlderFreshHybridClock (flat)
open WilsonOlderFreshTerminalProgramme (series)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftFigureReading (reading)
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[Fintype ι][LinearOrder ι](R:Run G)(d:ι→ℕ)
local notation "F" i:max=>R.family.labels.level (d i)

def announced (L:Levels G)(O:ChartRatio G)(N w v q:ℕ)(t:ℝ)(X:Era G ℝ):ℝ:=
  series q t (fun e=>coeff e (WilsonOlderFreshSoftCoverScalar.clock L O N w v (ScalarTrim X.2)))

def cost (L:Levels G)(O:ChartRatio G)(N w v q:ℕ)(t g:ℝ)(x:∀i,(F i).Coeff)
    (H:((i:ι)→(F i).Index)→Era G ℝ):ℂ:=
  ∑b,WilsonOriginalPublicTrialFigure.weight R d g x b*(announced L O N w v q t (H b):ℂ)

theorem original (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(auth:LocalRatio O)
    (N k w v q:ℕ)(vw:v≤w)(wn:w≤N)(t g:ℝ)(x:∀i,(F i).Coeff)(H:((i:ι)→(F i).Index)→Era G ℝ):
    reading R d g x (fun b=>cruises L O N k w v (scalarOnly (H b))) q t=cost R d L O N w v q t g x H:=by
  apply sum_congr rfl
  intro b _
  congr 2
  change flat (cruises L O N k w v (scalarOnly (H b))) q t=announced L O N w v q t (H b)
  unfold flat announced
  rw [WilsonOlderFreshSoftCoverScalar.received L O simple auth N k w v wn vw]
  simp only [uband,shine_lit]

end YM.Integration.WilsonOlderFreshSoftCoveredRead
end
