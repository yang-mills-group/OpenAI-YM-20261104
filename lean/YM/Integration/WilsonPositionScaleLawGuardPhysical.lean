import YM.Integration.WilsonPositionScaleLawGuardInvoice
import YM.Integration.WilsonPositionScaleLawGuardReceipt
import YM.Integration.WilsonPositionScaleLawDressedBudget
import YM.Integration.WilsonPositionScaleLawGuardHomeTaylor

/-! A numerical homogeneous field-scale invoice on the one physical F,J.
The second scalar is always read on the newly positioned true home first. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardPhysical
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

def offered (d q:ℕ)(r:ℝ)(t:Ratio):ℝ:=fee (sheet R.family Z M ν t d) (engine R.family d t) q
  (gθ r:ℂ) (gθ (t.val*r):ℂ) (exactOp F J Z.store d (r,t)) (home F J Z d r) (home F J Z d (t.val*r))

abbrev expected (d q:ℕ)(r:ℝ)(t:Ratio):=issue R.family q (guard Z M ν (WilsonPositionScaleLawIndependent.time t) d) (gθ r:ℂ)

include H in
theorem account (d q:ℕ)(r:ℝ)(t:Ratio)(hz:‖(gθ r:ℂ)‖≤1)(hz':‖(gθ (t.val*r):ℂ)‖≤1)
    (hw:‖(trunc (q+1) (sheet R.family Z M ν t d).scalar).eval (gθ r:ℂ)‖≤1):
    ‖residual F J Z d r t (expected F J Z M ν d q r t)‖≤offered F J Z M ν d q r t:=
  WilsonPositionScaleLawGuardReceipt.original _ _ (WilsonPositionScaleLawGuardInvoice.original R.family Z M H ν t d)
    q _ _ _ _ _ hz hz' hw

variable (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)

include H lead paid in
theorem original (d:ℕ):∀ᶠr in trail,∀t:Ratio,∀q:ℕ,‖(gθ r:ℂ)‖≤1→‖(gθ (t.val*r):ℂ)‖≤1→
    ‖(trunc (q+1) (sheet R.family Z M ν t d).scalar).eval (gθ r:ℂ)‖≤1→
    ‖dressed Z F J d r t-expected F J Z M ν d q r t‖≤2*cap R.family d*offered F J Z M ν d q r t:=by
  filter_upwards [WilsonPositionScaleLawDressedBudget.original F J Z hG lead paid d] with r fit t q hz hz' hw
  exact (fit t _).trans (mul_le_mul_of_nonneg_left (account F J Z M H ν d q r t hz hz' hw)
    (mul_nonneg (by norm_num) (WilsonPositionScaleLawDressedGear.capPositive R.family)))

end YM.Integration.WilsonPositionScaleLawGuardPhysical
