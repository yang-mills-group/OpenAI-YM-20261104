import YM.Integration.WilsonPositionScaleLawGuardMarket
import YM.Integration.WilsonPositionScaleLawGuardMeasured
import YM.Integration.WilsonPositionScaleLawBookedThermometer

/-! A common numerical constant for the actual signed field, signed clock and next order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardReduction
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale PowerSeries
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawGuardInvoice (sheet issue)
open WilsonPositionScaleLawGuardReceipt (fee)
open WilsonPositionScaleLawDressedBudget (home residual)
open WilsonPositionScaleLawDressedGear (engine cap)
open WilsonPositionScaleLawDressedTransport (dressed guard)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Polynomial Classical BigOperators

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}
    {b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J

open WilsonPositionScaleLawGuardHomePrint (taylor)
open WilsonPositionScaleLawGuardCombine (Cover)
open WilsonPositionScaleLawGuardLipschitz (slope)
local instance half:WilsonPositionScaleLawWindow.RangeSpec:=⟨1/2,by norm_num⟩

def fieldFee (d q:ℕ)(z:ℝ×Ratio):ℝ:=‖exactOp F J Z.store d z-WilsonPositionScaleLawQinter.prediction Z M ν F J d q z‖
def clockFee (q:ℕ)(z:ℝ×Ratio):ℝ:=‖(gθ (z.2.val*z.1):ℂ)-WilsonPositionScaleLawThermometerPay.target Z M ν F J q z‖
def remainder (d q:ℕ)(z:ℝ×Ratio):ℝ:=fieldFee F J Z M ν d q z+clockFee F J Z M ν q z+‖(gθ z.1:ℂ)‖^(q+1)

include H in
theorem named (d q:ℕ)(z:ℝ×Ratio):WilsonPositionScaleLawGuardCombine.signal
    (sheet R.family Z M ν z.2 d) q (gθ z.1:ℂ) (gθ (z.2.val*z.1):ℂ) (exactOp F J Z.store d z)=remainder F J Z M ν d q z:=by
  rw [remainder,fieldFee,WilsonPositionScaleLawGuardMeasured.original Z M H ν F J]
  rfl

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (funded:Coupling G (kinetic Z F J))
include H lead paid funded in
theorem original (d q:ℕ):∃K:ℝ,0≤K ∧ ∀ᶠz:ℝ×Ratio in WilsonPositionScaleLawHome.sweep,
    ‖dressed Z F J d z.1 z.2-WilsonPositionScaleLawGuardPhysical.expected F J Z M ν d q z.1 z.2‖≤
      K*remainder F J Z M ν d q z:=by
  obtain ⟨L,hL,full⟩:=WilsonPositionScaleLawGuardMarket.original F J Z M H ν lead paid funded d q
  let A:=2*cap R.family d
  have a0:0≤A:=mul_nonneg (by norm_num) (WilsonPositionScaleLawDressedGear.capPositive R.family)
  refine ⟨A*(2*L^2+3*L^3),mul_nonneg a0 (by positivity),?_⟩
  filter_upwards [full,(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually
    (WilsonPositionScaleLawGuardPhysical.original F J Z M H ν lead paid d)] with z covered original
  obtain ⟨bill,hx,hy,hw⟩:=covered
  have funds:=WilsonPositionScaleLawGuardCombine.original _ _ q _ _ (exactOp F J Z.store d z) _ _ bill
  calc
    _≤A*WilsonPositionScaleLawGuardPhysical.offered F J Z M ν d q z.1 z.2:=original z.2 q hx hy hw
    _≤A*((2*L^2+3*L^3)*WilsonPositionScaleLawGuardCombine.signal _ q _ _ _):=mul_le_mul_of_nonneg_left funds a0
    _=_:=by rw [named F J Z M H ν d q z];dsimp only [A];ring

end YM.Integration.WilsonPositionScaleLawGuardReduction
