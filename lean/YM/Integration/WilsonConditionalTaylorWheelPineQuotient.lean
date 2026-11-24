import YM.Integration.WilsonConditionalTaylorWheelResponse
import YM.Integration.WilsonConditionalTaylorWheelKernel
import YM.Integration.WilsonMovingRunWickCoordinates

/-! The full normalized response in the original physical link coordinates
equals exactly the response in the independently filed free pine coordinates.
An arbitrary (signed) joint source is kept on one Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelPineQuotient
open Function PowerSeries Lattice RG Matrix Precision Tree FreeResolvent
open FormalBulk08 FormalBulk08.Orb FormalBulk08.Series WilsonCoeffUV
open FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Lava FormalBulk08.Mesa FormalBulk08.Bank PhysicalNext.Repeat.Legato
open Next.Free
open WilsonConditionalTaylorWheelKernel WilsonConditionalTaylorWick WilsonMovingPolynomialPull
open scoped Classical BigOperators Matrix
variable {G:Gauge} (D:Stage G)
local notation "op" => D.R.family.path.levels.clock.op D.j D.per
local notation "coarse" => D.R.family.side D.j D.per
local notation "P" => destination D.R.family.path.levels D.N D.j
private theorem stay {I:Type} (T:Pap I):place id T=T:=by
  unfold place
  simp

theorem recorded (x:Pine G op D.forest⊕wire G coarse→ℝ)
    (A T:Pap (Pine G op D.forest⊕wire G coarse)):
    quotient (WilsonConditionalTaylorWheelResponse.lift (G:=G) op D.forest) x (saddle D).q A T =
      quotient (WilsonMovingFiniteConditional.lift (wire G coarse) (Pine G op D.forest)) x
        (Flat.testPrecision G op D.forest (P).wing)⁻¹ A T:=by
  let L:=WilsonConditionalTaylorWheelResponse.lift (G:=G) op D.forest
  have inc : L.submatrix id (Reef.pines (G:=G) D.forest).symm=
      WilsonMovingFiniteConditional.lift (wire G coarse) (Pine G op D.forest):=by
    ext i j
    change WilsonMovingFiniteConditional.lift (wire G coarse) (Pine G op D.forest) i
        (Reef.pines D.forest ((Reef.pines D.forest).symm j))=_
    rw [Equiv.apply_symm_apply]
  have cov:(saddle D).q.submatrix (Reef.pines (G:=G) D.forest).symm (Reef.pines D.forest).symm=
      (Flat.testPrecision G op D.forest (P).wing)⁻¹:=
    WilsonMovingRunWickCoordinates.precision D.R D.N D.j D.per D.live D.forest D.tag
  have src:=WilsonMovingWickReindex.normalized L x (saddle D).q
      (((RunFormalChain.fromRun D.R).step D.N D.j D.per D.live).positive D.forest D.tag)
      id (Reef.pines (G:=G) D.forest).symm A T
  rw [inc,cov,stay,stay] at src
  exact src.symm
end YM.Integration.WilsonConditionalTaylorWheelPineQuotient
end
