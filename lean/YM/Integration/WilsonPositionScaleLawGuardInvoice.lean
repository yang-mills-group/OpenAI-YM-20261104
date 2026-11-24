import YM.Integration.WilsonPositionScaleLawGuardLift
import YM.Integration.WilsonPositionScaleLawGuardSheet

/-! The complete finite native conjugacy invoice for the nominated field scale.
Every matrix and every coefficient is fixed by the single independent MS book. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardInvoice
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawGuardLift (act pack)
open WilsonPositionScaleLawGuardPoly (value mass)
open WilsonPositionScaleLawGuardCancellation (fringe)
open WilsonPositionScaleLawDressedGear (engine)
open WilsonPositionScaleLawDressedTransport (adjust)
open scoped Topology Polynomial Classical BigOperators
local instance {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]:NormedRing (X→L[ℂ]X):=
  ContinuousLinearMap.toNormedRing
local instance {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]:NormedAlgebra ℂ (X→L[ℂ]X):=
  ContinuousLinearMap.toNormedAlgebra

variable {G:Gauge}(C:Family G){d:ℕ}

theorem paidSub (p:Cn)(A:Guard G d):
    pack C (Reg.Point.stepV p A)=WilsonPositionScaleLawGuardSubstitute.system p (pack C A):=by
  apply PowerSeries.ext;intro k
  rw [WilsonPositionScaleLawGuardSubstitute.system,coeff_mk,WilsonPositionScaleLawGuardLift.coefficient,
    Reg.Point.stepV,coeff_mk,rules,rules]
  change act C d (∑j∈Finset.Iic k,cut p j k • coeff j A)=_
  rw [map_sum];apply Finset.sum_congr rfl;intro j _
  rw [map_smul,WilsonPositionScaleLawGuardLift.coefficient];rfl

abbrev issue (q:ℕ)(A:Guard G d)(z:ℂ):=value (trunc (q+1) (pack C A)) z

theorem acted (t:Ratio)(A:Guard G d)(q:ℕ)(z:ℂ):
    issue C q A z*engine C d t=engine C d t*issue C q (convertT (WilsonPositionScaleLawIndependent.time t) A) z:=by
  simp only [issue,WilsonPositionScaleLawGuardEval.printed,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro k _
  rw [smul_mul_assoc,mul_smul_comm,WilsonPositionScaleLawGuardLift.coefficient,
    WilsonPositionScaleLawGuardLift.coefficient,convertT,coeff_mk]
  exact congrArg (fun a=>z^k • a) (WilsonPositionScaleLawGuardLift.transfer C t (coeff k A))

variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    (t:Ratio)(d:ℕ)
set_option quotPrecheck false
local notation "sT"=>WilsonPositionScaleLawIndependent.time t
local notation "aT"=>adjust Z d
local notation "cT"=>convertT sT aT
local notation "pT"=>GroupS.ψ Z.criterion M ν sT
local notation "bT"=>GroupS.gaugeB Z.criterion M ν sT d
local notation "nT"=>WilsonPositionScaleLawDressedTransport.guard Z M ν sT d

def sheet:WilsonPositionScaleLawGuardSheet.Book ((Bel C.book).Field d→L[ℂ](Bel C.book).Field d):=
  ⟨pT,pack C aT,pack C cT,pack C nT,pack C bT⟩

include H in
theorem strict:WilsonPositionScaleLawGuardSheet.Valid (sheet C Z M ν t d):=by
  refine ⟨((H.details.normative ν).first.led sT).start,?_⟩
  change pack C cT*pack C nT=pack C bT*WilsonPositionScaleLawGuardSubstitute.system pT (pack C aT)
  rw [←paidSub C pT aT]
  exact WilsonPositionScaleLawGuardLift.original C Z M H ν t d

theorem gears:WilsonPositionScaleLawGuardSheet.carries (sheet C Z M ν t d) (engine C d t):=by
  intro q z
  exact acted C t aT q z

include H in
theorem original:WilsonPositionScaleLawGuardSheet.Quote (sheet C Z M ν t d) (engine C d t):=
  WilsonPositionScaleLawGuardSheet.booked _ (strict C Z M H ν t d) _ (gears C Z M ν t d)

end YM.Integration.WilsonPositionScaleLawGuardInvoice
