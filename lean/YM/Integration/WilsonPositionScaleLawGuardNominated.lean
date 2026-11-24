import YM.Integration.WilsonPositionScaleLawGuardBooked
import YM.Integration.WilsonPositionScaleLawGuardIncludedUnit

/-! The all-orders signed scale tests available on one nominated original leading and obedient frame, before selection of fields, positions or precision. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardNominated
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawGuardInvoice (issue)
open WilsonPositionScaleLawDressedTransport (guard)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(simple:G.Simple)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

local instance half:WilsonPositionScaleLawWindow.RangeSpec:=⟨1/2,by norm_num⟩

structure After:Prop where
  included (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}{b:Bool}
    (H:Main.Match Z simple M σ b)(ν:ℝ)(d:ℕ):∀ᶠr in trail,∀t:ℝ,∀ht:0<t,t≤1→∀q j:ℕ,∀h:j≤d,j<4→∀v:E j,
      change (WilsonPositionHomogeneousFrame.homogeneous F J Z) d r t ht ((scheme R.family.labels).rise h v)=
        issue R.family q (guard Z M ν (-Real.log t) d) (kinetic Z F J r:ℂ) ((scheme R.family.labels).rise h v)
  scale (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ:Prescription (Press.portDeck G)}{b:Bool}
    (H:Main.Match Z simple M σ b)(ν:ℝ)(d q:ℕ)(funded:Coupling G (kinetic Z F J))
    (branch:WilsonPositionScaleLawCompactBranch.Raw J d)(clockBranch:WilsonPositionScaleLawCompactBranch.Raw J 6)
    (fields:WilsonPositionScaleLawGuardBooked.fieldPaid Z M ν F J d q)(clock:WilsonPositionScaleLawThermometerScale.Earned Z M ν F J q):
    WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q

theorem original {Y:(Bel R.family.book).Hierarchy}(lead:Leading F J)(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d):After F J simple where
  included Z M _ _ H ν d:=WilsonPositionScaleLawGuardIncludedUnit.original F J Z M H ν lead d
  scale Z M _ _ H ν d q funded branch clockBranch fields clock:=
    WilsonPositionScaleLawGuardLittle.original F J Z M H ν lead paid funded d q branch clockBranch fields clock

end YM.Integration.WilsonPositionScaleLawGuardNominated
