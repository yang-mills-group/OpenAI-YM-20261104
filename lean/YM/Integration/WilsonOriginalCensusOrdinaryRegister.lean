import YM.Integration.WilsonReceivedDepositedOrbitalGrade
import YM.Integration.WilsonCapturedPrimaryWindingVerseRoster

/-! Evaluate the whole deposited ordinary family on the physical thermal
register after selecting the original quiet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusOrdinaryRegister
open Function Finset Marker Multi PowerSeries Next.Rank Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonCoeffUV WilsonCoeffUV.Blue
open Extra.Trajectories (pass_add pass_zero)
open WilsonVacuumPreResetFiniteRegister WilsonOriginalSingleMarkedRegister WilsonOriginalMixedGaussianTable
open OriginalRadialSeries (observed)
open scoped Classical BigOperators
open private multiplied absent from YM.Integration.WilsonOriginalJointGaussianIncome
open WilsonReceivedDepositedOrbitalGrade (booked thermal at_row)
open WilsonReceivedDepositedOrbitalColumns (row)
open WilsonCoeffUV.Wheel.Mark
variable {V U:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V
variable (r:ℕ)(z:U→ℝ)(w:V→ℂ)

theorem blank (T:Finset V→Ink U):
    (booked r z w T).part (Board (J) r).quiet=((thermal V r z) (T ∅)).part (indices r).quiet:=by
  have h:=congrArg (fun b:Poly (indices r)=>b.part (indices r).quiet) (at_row r z w T ∅)
  simp only [Finset.prod_empty,one_smul] at h
  change (booked r z w T).part (Join.pair (J).quiet (indices r).quiet)=_ at h
  simpa only [Join.pair_quiet] using h

theorem coefficient (T:Finset V→Ink U)(s:(J).Mode)(u:Index r):
    (booked r z w T).part (Join.pair s u)=
      (u.val.card.factorial:ℂ)*((∏v∈s.val,w v)*Complex.ofReal (MvPolynomial.eval z (coeff u.val.card (T s.val)))):=by
  have h:=congrArg (fun b:Poly (indices r)=>b.part u) (at_row r z w T s.val)
  change (booked r z w T).part (Join.pair s u)=(∏v∈s.val,w v)*
    (register (J) r (observed z (T s.val))).part (Join.pair (J).quiet u) at h
  rw [WilsonVacuumPreResetFiniteRegister.read,if_pos rfl] at h
  rw [h]
  change _*(↑u.val.card.factorial*Complex.ofReal (MvPolynomial.eval z (coeff u.val.card (T s.val))))=_ 
  ring

theorem conditioned (S:Ink U)(T:Finset V→Ink U):
    register (J) r (observed z S)*booked r z w T=booked r z w (fun s=>S*T s):=by
  unfold booked stock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [term,map_mul]
  ring

theorem original (S:Ink U)(vac:constantCoeff S=0){M L:Finset V→Ink U}(law:Equation M L):
    Poly.pass (register (J) r (observed z S)+booked r z w L)=
      booked r z w (fun s=>raiseE S*M s):=by
  have measured:constantCoeff (observed z S)=0:=by
    change MvPolynomial.eval z (constantCoeff S)=0
    rw [vac,map_zero]
  have quiet:(register (J) r (observed z S)).part (Board (J) r).quiet=0:=by
    rw [←Join.pair_quiet,WilsonVacuumPreResetFiniteRegister.read,if_pos rfl]
    change ((_ : ℕ).factorial:ℂ)*↑(coeff 0 (observed z S))=0
    rw [coeff_zero_eq_constantCoeff_apply,measured]
    simp
  have unit:(booked r z w M).part (Board (J) r).quiet=1:=by
    rw [blank,law.1,map_one,Poly.one_part,if_pos rfl]
  have empty:(booked r z w L).part (Board (J) r).quiet=0:=by
    rw [blank,law.2.1,map_zero]
    rfl
  have variable0:constantCoeff (observed z PowerSeries.X)=0:=by simp [OriginalRadialSeries.observed]
  rw [pass_add quiet empty,←WilsonVacuumPreResetFiniteRegister.exponential (J) r _ measured,
    ←raise_map (observed z) variable0 vac,←WilsonReceivedDepositedOrbitalGrade.logged r z w law,
    Extra.Trajectories.pass_connected unit]
  exact conditioned r z w _ _

end YM.Integration.WilsonOriginalCensusOrdinaryRegister
end
