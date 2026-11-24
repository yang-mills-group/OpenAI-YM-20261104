import YM.Integration.WilsonOriginalMicroscopicEntranceOpticalUnits
import YM.Integration.WilsonOriginalMicroscopicEntranceTwoExits
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldRefund

/-! The two honestly spent mixed withdrawals and the actual failed K guard on one earlier flat. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceSettledHeld
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceOpticalUnits (pole rank dye fare)
open WilsonOriginalMicroscopicGuardedFlat (peak count)
open Trace.Physical.Germ Trace.Physical.GermGraph
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ)

local notation "CF" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "H" i:max => (CF).path.levels.clock.hatBeta i
local notation "mesh" i:max => (CF).S.a i

open WilsonOriginalMicroscopicEntranceHaloIncome (all)

open MeasureTheory WilsonOriginalMicroscopicEntranceTwoExits
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open OPE.Therm WilsonCoeffUV.Embroider
open WilsonOriginalMicroscopicEntranceGridRow (pin)
variable {N per m k f n u:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
    (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (live:f+n≤N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q)(floor:m≤u)(uf:u≤f)
    (fixed:WilsonSingleHardRadius.first R simple≤u)(capture:WilsonCenteredCaptureClock.first R simple≤f+n)
    {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
    (Y v:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f per))
local notation "K_" => f+n
local notation "fk" => Nat.le_add_right f n

include κ pt course top way ticket floor fixed capture in
theorem original {t:ℕ}(before:u+1≤f+n)(housing:mesh f/mesh (f+n)≤(H (f+n))^t)
    (V:Fin 3→ℝ)(vp:∀a,0≤V a)(earned:∀a,slotFare R d f (f+n) v a≤(mesh f)^(d a)*V a)
    (q:ℕ){ε:ℝ}(positive:0<ε)(late:(eventually_atTop.mp
      (WilsonOriginalFlatHaloRate.calendar R simple (q+all R d t) positive)).choose≤f+n)
    (s:(J).Mode)(W:Config G (R.family.side u per))(b c:Config G (R.family.side f per)→ℂ)
    (left:Integrable (fun U=>(R.family.path.rep N per f).eval U • b U) (prior G _))
    (right:Integrable (fun U=>(R.family.path.rep N per f).eval U • c U) (prior G _))
    {oldFee trialFee:ℝ}
    (priorBill:‖actualTransport R.family (N:=N) (cutoffFace R d live Y o s-b) uf W‖≤oldFee)
    (trialBill:‖actualTransport R.family (N:=N) (trialFace R d (N:=N) (n:=n) o v s-c) uf W‖≤trialFee):
    ‖originalRead R d live Y o v s uf W-
      (actualTransport R.family (N:=N) b uf W-actualTransport R.family (N:=N) c uf W)‖≤
    oldFee+trialFee+WilsonOriginalMicroscopicEntranceHeldHalo.spring R u N per W*
      (fare R d V s*((count R d s.val:ℝ)*(4*Real.exp ((R.alloy.B.a.budget (f+n)).supportExponent+2))*(ε/(H (f+n))^q))):=by
  have guard:=WilsonOriginalMicroscopicEntranceHeldRefund.original R d π Γ Ψ course live top simple way D Q ticket
    floor fixed capture fk housing (pin R fk o) v V vp earned q positive late s (le_refl u) before W
  exact (WilsonOriginalMicroscopicEntranceTwoExits.priced R d live Y o v s b c uf W κ pt left right
    priorBill trialBill).trans (add_le_add le_rfl guard)

end YM.Integration.WilsonOriginalMicroscopicEntranceSettledHeld
end
