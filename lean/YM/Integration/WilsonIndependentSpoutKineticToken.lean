import YM.Integration.WilsonIndependentSpoutUnmarkedClock

/-! Comparison of the actual signed kinetic moments in the two tensor conventions.
Both slots keep their real color, orientation and relative lattice site. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutKineticToken
open Lattice Exterior WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue RegulatorIR
open RegulatorIR.Budget RegulatorIR.Prim RegulatorIR.Pupil RegulatorIR.Momentum
open scoped Classical BigOperators
variable {G:Gauge}

def placed (x:Foot G):YForest G:=stone x.1 x.2

def direct (K:Ten ℝ (YForest G) 2):Packet (Foot G) 2 :=
  fun x=>-K (placed ∘ x)

def reverse (K:Ten ℝ (YForest G) 2):Packet (Foot G) 2 :=
  fun x=>-K (Fin.cons (placed (x 1)) ![placed (x 0)])

theorem reversed (K:Ten ℝ (YForest G) 2)(c:G.ColorIndex):
    Rules.token (reverse K) c=azur K c := by
  unfold Rules.token Pupil.shine recital Pupil.starE Pupil.twin reverse azur tailor
  rw [←tsum_neg]
  apply tsum_congr
  intro x
  rw [dial_probe]
  change (-K (Fin.cons (stone (x,1) c) ![stone (0,1) c]))*(x 0:ℝ)^2=
    -(((x 0:ℝ)*(x 0:ℝ))*K (Fin.cons (stone (x,1) c) ![stone (0,1) c]))
  ring

theorem colored (K:Ten ℝ (YForest G) 2)(h:Nonempty G.ColorIndex):
    Rules.token (reverse K) h.some=readSun K := by
  rw [reversed,read_azur K h]

end YM.Integration.WilsonIndependentSpoutKineticToken
