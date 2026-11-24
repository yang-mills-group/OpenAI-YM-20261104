import YM.Integration.WilsonConditionalTaylorWheelIssuedResponse
import YM.Integration.WilsonRunVacuumWickCubature

/-! The entire unnormalized mass of the authentic upper nonlinear heat
step equals the independently constructed finite partition function, at
nonzero coarse configurations as well as zero, for its actual input. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelMassTransfer
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries Next.Foundations
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb FormalBulk08.Series
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel
open WilsonConditionalTaylorWheelKernel WilsonConditionalTaylorWick WilsonMovingNormalizedBank
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open Comparison.RG02 Push.Uniform PhysicalNext.Repeat.Legato Next.Free Work.F03 Work.F05 Work.F08
open FormalBulk08.Wine FormalBulk08.Roof FormalBulk08.Dove Stationary
open Planned.PrimaryIntegral295 Source Source.Drops Labels
open scoped Classical BigOperators Matrix
variable {G:Gauge} (D:Stage G)
local notation "op" => D.R.family.path.levels.clock.op D.j D.per
local notation "coarse" => D.R.family.side D.j D.per
local notation "fine" => D.R.family.side (D.j+1) D.per
set_option quotPrecheck false in
local notation "K" => (RunFormalChain.fromRun D.R).step D.N D.j D.per D.live
set_option quotPrecheck false in
local notation "mean" => installed (op).ratio (predictionA D.R.family.path.levels D.N D.j)
local notation "B" => WilsonMovingFiniteConditional.lift (wire G coarse) (Active G D.forest)

theorem ported (y:wire G coarse→ℝ) (T:Pap (Pine G op D.forest⊕wire G coarse)):
    contract (WilsonConditionalTaylorWheelResponse.lift (G:=G) op D.forest)
      (WilsonConditionalTaylorWheelResponse.center (G:=G) op D.forest mean y) (saddle D).q T=
    contract (WilsonMovingFiniteConditional.lift (wire G coarse) (Pine G op D.forest))
      (Sum.elim (Flat.rawMean G op D.forest mean*ᵥy) y)
      (Flat.testPrecision G op D.forest (destination D.R.family.path.levels D.N D.j).wing)⁻¹ T:=by
  let E:=Reef.pines (G:=G) D.forest
  let Q:=((saddle D).q).submatrix E.symm E.symm
  have pos:Q.PosDef:=(((RunFormalChain.fromRun D.R).step D.N D.j D.per D.live).positive D.forest D.tag).submatrix E.symm.injective
  have original:Q=(Flat.testPrecision G op D.forest (destination D.R.family.path.levels D.N D.j).wing)⁻¹:=
    WilsonMovingRunWickCoordinates.precision D.R D.N D.j D.per D.live D.forest D.tag
  have eqn:=WilsonMovingWickReindex.contracted (WilsonMovingFiniteConditional.lift (wire G coarse) _)
    (WilsonConditionalTaylorWheelResponse.center (G:=G) op D.forest mean y) Q pos id E T
  have same:Q.submatrix E E=(saddle D).q:=by ext i j;simp [Q,Matrix.submatrix]
  have identity:WilsonMovingPolynomialPull.place id T=T:=by
    apply PowerSeries.ext
    intro e
    rw [WilsonMovingPolynomialPull.place,coeff_map]
    change MvPolynomial.rename id (coeff e T)=_
    simp
  rw [same,identity,original] at eqn
  exact eqn

theorem bank (P:PChart G fine) (degree:shellK 2 P) (u:Positions (Primary coarse G)):
    let y:=FreeResolvent.flatten (tint G (Body 1 coarse) u)
    glimpse y (amount D (expan (shot op D.forest mean D.R.metals.O P))) =
      WilsonRunVacuumWickCubature.bank K D.forest D.tag u (-flash P):=by
  intro y
  let f:=shot op D.forest mean D.R.metals.O P
  let g:=WilsonMovingFiniteConditional.interaction (Reef.flush D.forest D.tag D.R.metals.O (-flash P))
  have hf:Kind f:=by
    change coeff 0 (shot op D.forest mean D.R.metals.O P)=0
    rw [shot,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero op D.R.alloy.B.ratio),map_zero]
  have pull:=WilsonConditionalTaylorWheelResponse.received op D.forest mean y f g
    (fun e z=>WilsonConditionalTaylorWheelCommonInput.signed op D.forest D.R.metals.O D.R.alloy.B.ratio P degree
      (D.R.family.path.levels.blocks D.j D.per).branches D.tag mean z e)
  have share:contract B (Sum.elim 0 y) (saddle D).q (Spring f)=
      contract (WilsonConditionalTaylorWheelResponse.lift (G:=G) op D.forest)
        (WilsonConditionalTaylorWheelResponse.center (G:=G) op D.forest mean y) (saddle D).q (Spring g):=by
    simp only [contract,←sunshine,pull]
  rw [WilsonConditionalTaylorWheelIssuedResponse.deposited]
  change contract B (Sum.elim 0 y) (saddle D).q (expan f)=_
  rw [WilsonMovingExponentialConvention.exp f hf,share,ported]
  exact WilsonRunVacuumWickCubature.measured D.R D.N D.j D.per D.live D.forest D.tag u (-flash P)

end YM.Integration.WilsonConditionalTaylorWheelMassTransfer
end

