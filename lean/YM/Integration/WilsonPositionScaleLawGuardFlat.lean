import YM.Integration.WilsonPositionScaleLawGuardForcing
import YM.Integration.WilsonPositionScaleLawGuardContraction

/-! Lower projections of a fixed actual homogeneous field decay faster than every inverse dyadic-clock power. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardFlat
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawGuardOrbit (size sizePos total)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawWholeGrowth (weight)
open scoped Topology Classical Asymptotics

variable {G:Gauge}
variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
variable (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:∀q,WilsonPositionScaleLawGuardLittle.scale F J Z M ν d q)(r:ℝ)(hr:0<r)
open WilsonPositionScaleLawGrade (grade half)
open WilsonPositionScaleLawGuardForcing (amount)
include H funded law hr in
theorem dyadic (i:Fin (d+1))(lower:i.val<d)(m:ℕ):∃N:ℕ,∀O:S.Field d,∃B:ℝ,0≤B ∧ ∀n,N≤n→
    weight m n*‖grade R.family i (physical F J Z d (radius r n) O)‖≤B:=by
  obtain ⟨q,N,fees⟩:=WilsonPositionScaleLawGuardForcing.original Z M H ν F J d funded law r hr m
  choose A pos sold using fees
  let P:=grade R.family i
  let v(n:ℕ)(O:S.Field d):=‖P (physical F J Z d (radius r n) O)‖
  let budget (O:S.Field d):=4*‖P‖*A O
  apply WilsonPositionScaleLawGuardContraction.original m v budget (fun _ _=>norm_nonneg _)
  have raw:=(WilsonPositionScaleLawClock.falls r hr).eventually (WilsonPositionScaleLawGuardBlock.original Z M H ν F J funded q i lower)
  filter_upwards [raw,Filter.eventually_ge_atTop N] with n draw hn O
  have fee:=sold O n hn half
  rw [WilsonPositionScaleLawWholeGrowth.next] at fee
  let cost:=amount Z M ν F J d r q n half
  let y:=physical F J Z d (radius r (n+1)) O
  let w:=weight m (n+1)
  have step:=draw half O
  dsimp only at step
  rw [WilsonPositionScaleLawWholeGrowth.next] at step
  change 3*v (n+1) O≤4*(1/2)*v n O+4*‖P‖*cost*‖y‖ at step
  have pay:w*cost*‖y‖≤A O:=fee
  have hw:0≤w:=zero_le_one.trans (WilsonPositionScaleLawWholeGrowth.positive ..)
  have weighted:=mul_le_mul_of_nonneg_left step hw
  have spill:=mul_le_mul_of_nonneg_left pay (mul_nonneg (by norm_num : (0:ℝ)≤4) (norm_nonneg P))
  change 3*w*v (n+1) O≤2*w*v n O+4*‖P‖*A O
  linarith only [weighted,spill]

end YM.Integration.WilsonPositionScaleLawGuardFlat
