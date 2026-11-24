import YM.Integration.WilsonConditionalTaylorWheelClock
import YM.Integration.WilsonMovingBareVacuum

/-! The upper bare energy and the independent bare logarithmic action
have opposite signs on the identical finite, unreduced group field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelBare
open Function PowerSeries FormalBulk08 FormalBulk08.Reef FormalBulk08.Series FormalBulk08.Jets
open Lattice RG Wilson Precision Exterior WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {G:Gauge}

theorem germ {U:Type} [Fintype U] [DecidableEq U] (f:(U→ℝ)→ℝ):Blue.jet f=Jets.paste f:=by
  apply PowerSeries.ext
  intro e
  apply Jets.orbit_ext
  intro z
  rw [Jets.trace_paste]
  change MvPolynomial.eval z (coeff e (Blue.jet f))=_
  exact Blue.rayon f e z

theorem energy (G:Gauge) (n:Side):(eWilson (G:=G) (c:=n))=Reef.fundamental G n:=rfl

private theorem full {U:Type} [Fintype U] [DecidableEq U] (f:(U→ℝ)→ℝ):
    lop (sprig f 2)=sprig f 2:=by
  funext e r
  by_cases h:r=0
  · subst r
    rw [lop,if_pos rfl,sprig,shine_dark (by omega : 2+e≠0)]
  · simp only [lop,if_neg h]

theorem original (G:Gauge) (n:Side):
    flash (topW G n) = -(Mesa.stone (Mesa.Enter G) n):=by
  rw [topW,full,sprig_flash,germ,energy,←Mesa.top_word,Reef.seed,neg_neg]
  rfl

end YM.Integration.WilsonConditionalTaylorWheelBare
end

