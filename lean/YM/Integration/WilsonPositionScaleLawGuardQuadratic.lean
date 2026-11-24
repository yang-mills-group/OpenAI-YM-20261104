import YM.Integration.WilsonPositionScaleLawGuardLittle
import YM.Integration.WilsonPositionScaleLawGuardFirst

/-! The real quadratic size of the first homogeneous transition, using the true vanishing first MS coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardQuadratic
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open Asymptotics PowerSeries
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed guard)
open WilsonPositionScaleLawGuardSheet (atValue)
open WilsonPositionScaleLawGuardInvoice (sheet)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics Polynomial

theorem nextTerm {R:Type*}[NormedRing R][NormedAlgebra ℂ R](q:ℕ)(a:PowerSeries R)(z:ℂ):
    atValue (q+1) a z=atValue q a z+z^(q+1) • coeff (q+1) a:=by
  rw [atValue,atValue,WilsonPositionScaleLawGuardEval.printed,WilsonPositionScaleLawGuardEval.printed,
    WilsonPositionScaleLawGuardValue.count,WilsonPositionScaleLawGuardValue.count,Finset.sum_range_succ]

variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
include H in
theorem independent (d:ℕ):∃B:ℝ,0≤B ∧ ∀(t:Ratio)(z:ℂ),
    ‖atValue 2 (sheet C Z M ν t d).homogeneous z-1‖≤B*‖z‖^2:=by
  let X:=(Bel C.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  let p(t:Ratio):=(sheet C Z M ν t d).homogeneous
  obtain ⟨B,hB,full⟩:=WilsonPositionScaleLawGuardBanks.bounded 2 (fun k t=>coeff k (p t)) (WilsonPositionScaleLawGuardBanks.homogeneous C Z M H ν d)
  refine ⟨B,hB,?_⟩
  intro t z
  have first:atValue 1 (p t) z=1:=WilsonPositionScaleLawGuardFirst.original C Z M H ν _ d z
  change ‖atValue (1+1) (p t) z-1‖≤B*‖z‖^2
  rw [nextTerm,first,add_sub_cancel_left,norm_smul,norm_pow]
  exact (mul_le_mul_of_nonneg_left (full t 2 le_rfl) (sq_nonneg _)).trans_eq (mul_comm ..)

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field
local notation "gθ"=>kinetic Z F J
include H in
theorem original (d:ℕ)(paid:WilsonPositionScaleLawGuardLittle.scale F J Z M ν d 2):∃K:ℝ,0≤K ∧ ∀ᶠz:ℝ×Ratio in sweep,
    ‖dressed Z F J d z.1 z.2-ContinuousLinearMap.id ℂ (E d)‖≤K*(gθ z.1)^2:=by
  let I:=ContinuousLinearMap.id ℂ (E d)
  letI :NormedAddCommGroup (E d→L[ℂ]E d):=ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨B,hB,base⟩:=independent R.family Z M H ν d
  refine ⟨1+B,by linarith,?_⟩
  filter_upwards [isLittleO_iff.mp paid (c:=1) one_pos] with z fee
  let T:=WilsonPositionScaleLawGuardPhysical.expected F J Z M ν d 2 z.1 z.2
  have short:‖dressed Z F J d z.1 z.2-T‖≤(gθ z.1)^2:=by
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (_root_.sq_nonneg (gθ z.1))] using fee
  have bill:‖T-I‖≤B*(gθ z.1)^2:=by
    have one:(1:E d→L[ℂ]E d)=I:=by ext v;rfl
    rw [←one]
    change ‖atValue 2 (sheet R.family Z M ν z.2 d).homogeneous (gθ z.1:ℂ)-1‖≤B*(gθ z.1)^2
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using base z.2 (gθ z.1:ℂ)
  calc
    ‖dressed Z F J d z.1 z.2-I‖=‖(dressed Z F J d z.1 z.2-T)+(T-I)‖:=by congr 1;abel
    _≤‖dressed Z F J d z.1 z.2-T‖+‖T-I‖:=norm_add_le _ _
    _≤(gθ z.1)^2+B*(gθ z.1)^2:=add_le_add short bill
    _=_:=by ring

end YM.Integration.WilsonPositionScaleLawGuardQuadratic
