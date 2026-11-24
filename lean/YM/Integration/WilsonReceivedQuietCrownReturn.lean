import YM.Integration.WilsonReceivedQuietCrownFlat

/-! Return the failed masks of all blocks of the ordinary face at their
actual older flat stops on the elected dated prior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedQuietCrownReturn
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b ≤ N) {d:ℕ} {F:Frame G d} (S:SectionData F) (A:Hol G)
   (y:Site (R.family.side b per)) (q:Coefficient F (R.family.side b per))
   (law:q.Format y A (Ψ b)) {M:ℝ} (income:q.remBound y (Ψ b) (LocalComparison.forcedDivisor R.family b) M)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "vac" => R.family.path.rep N per b
local notation "W" => Ψ b
local notation "J" => Stock.census (Fin 1)
local notation "wallet" => Wallet WilsonMeasuredOwnerReserve.disk
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonReceivedQuietCrownOwner WilsonCapturedPrimarySoftPartition WilsonRootedKioskOccupiedSlip
open WilsonFullFaceSignedMasks Comparison.RG02.Cumulants
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected
open Source Labels Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureRegularAtoms WilsonCenteredLampCapture
open WilsonCenteredFiledAtoms WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftRoster
open WilsonRootedKioskOccupiedSlip Comparison.RG02.Cumulants WilsonCenteredCaptureSlots WilsonCenteredFailedHalo

open WilsonThermometerEarlierWallet
variable (simple:G.Simple) (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q) {u:ℕ} (floor:m ≤ u) (ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
   

include way ticket course top floor ub fixed S A in
theorem original {V X ι:Type}[Fintype V][DecidableEq V][Countable ι]{T:Census V}
    {o : V → Site (R.family.side b per)} (L:Lamps X ι G (W).p o T)(x:X)(s:T.Mode)
    (Z:Support (R.family.side b per))(hold:y∈Z)(landing:∀j∈s.val,o j∈Z)
    (rad:ℕ)(near:∀j∈s.val,separation (o j) y≤rad)
    (w:V→ℝ)(hw:∀v,0<w v){cash price:ℝ}
    (paid:L.Paid w (W).p.B ((W).p.supportExponent+2) cash)
    (stock:Gross L w (W).p.B ((W).p.supportExponent+2) price)
    {σ E Λ δ v:ℝ}(K:Guard.Keeper (W).p (W).activities)
    (law:(W).Lawful σ E Λ δ v)(div:0<κ)(hv:0≤v)(room:hitWidth (W).p*v≤1)
    (p:ℕ){ε:ℝ}(ep:0<ε)(late:WilsonSingleHardRadius.start R simple p ep ≤ b):
    let face:=fun U:Config G (R.family.side b per)=>((W).eval U:ℂ)*
      ((Poly.pass (L.log x U)).part s-(Poly.pass (bare L x U)).part s)
    let fee:=fun q:(parts T).Mode=>4*(1+|WilsonFullFaceSignedMasks.charge (W).p Z w cash price v κ q|)*ε/(β)^p
    Admitted (u:=u) (N:=N) R (le_refl b) face (∑q∈shards T s,fee q):=by
  intro face fee
  let trial:=fun(q:(parts T).Mode) U=>((W).eval U:ℂ)*((∏t∈q.val,(L.log x U).part t.val)-(∏t∈q.val,(bare L x U).part t.val))
  have separate(q)(hq:q∈shards T s):Admitted (u:=u) (N:=N) R (le_refl b) (trial q) (fee q):=by
    obtain owner:=WilsonReceivedQuietCrownOwner.partition (F:=F) L x s q hq y Z hold landing rad near w hw paid stock K law div hv room A
    exact WilsonReceivedQuietCrownFlat.one R π Γ Ψ course top S A y simple way D Q ticket floor ub fixed owner p ep late
  have same:face=∑q∈shards T s,trial q:=by
    funext U
    have width:0≤(W).p.supportExponent+2:=by linarith only [(W).p.exponent_pos]
    simp only [face,trial,Finset.sum_apply]
    rw [pass_partition _ (L.quiet_of_hasSum x U (paid.sums width hw x U)),
      pass_partition _ (WilsonRootedKioskCompleteFiling.quiet L hw width stock x U),
      ←sum_sub_distrib,mul_sum]
  rw [same]
  exact WilsonReceivedQuietCrownFlat.sum R (shards T s) trial fee separate

end YM.Integration.WilsonReceivedQuietCrownReturn
