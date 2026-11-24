import YM.Integration.WilsonConditionalTaylorWheelClock
import YM.FormalBulk08.Cork.Cents

/-! The original two schemes test the same held-site moment, with opposite
signs between energy and log weight. No averaging or arbitrary replacement
of the finite kernel occurs here. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelKineticRead
open PowerSeries FormalBulk08 Lattice RG Wilson Precision Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {G:Gauge}

theorem moment (K:Ten ℝ (YForest G) 2) (u:G.ColorIndex):azur K u= -Cork.value u K:=by
  unfold azur tailor Cork.value Cork.mir Cork.net
  congr 1
  apply tsum_congr
  intro v
  rw [mul_comm]
  rfl

theorem original (K:Ten ℝ (YForest G) 2) (color:Medium K) (u:G.ColorIndex):readSun K= -Cork.value u K:=by
  let h:Nonempty G.ColorIndex:=⟨u⟩
  rw [read_azur K h]
  have diagonal:=liner color 1 1 h.some h.some u (chalk 0*chalk 0)
  rw [if_pos rfl] at diagonal
  exact (congrArg Neg.neg diagonal).trans (moment K u)

theorem canonical (A:Levels G) (O:ChartRatio G) (N t e:ℕ) (u:G.ColorIndex):
    coeff e (pitch A O N t)= -Cork.value (Nonempty.intro u).some (freshet A O N t e 2):=by
  rw [pitch,stellar_read,read_azur _ (Nonempty.intro u),moment]

end YM.Integration.WilsonConditionalTaylorWheelKineticRead
end

