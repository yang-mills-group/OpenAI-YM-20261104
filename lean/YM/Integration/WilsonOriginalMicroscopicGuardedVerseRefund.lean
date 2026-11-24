import YM.Integration.WilsonOriginalMicroscopicGuardedVerseBalance
import YM.Integration.WilsonOriginalMicroscopicGuardedFlat

/-! The original guarded Wilson portfolio versus its independently filed
finite socket sum on the same earlier flat field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedVerseRefund
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicGuardedFlat (peak count)
open WilsonOriginalMicroscopicGuardedVerseBalance (printed)
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ)
variable {N per m k K:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (live:K≤N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m≤u)(start:u ≤ K)
   (fixed:WilsonSingleHardRadius.first R simple≤u)
   (capture:WilsonCenteredCaptureClock.first R simple ≤ K)
   (o:Fin 3→Site (R.family.side K per))(v:∀a:Fin 3,R.family.label (d a))(M:Fin 3→ℝ)
   (earned:∀a,(R.family.labels.level (d a)).coeffSize (v a)≤M a)(s:Finset (Fin 3))
local notation "X" => Config G (R.family.side K per)
local notation "Y" => gap R d N per K o v s
local notation "S₀" => footprint R d per K o s
local notation "K₀" => R.alloy.B.a.budget K
local notation "B" => R.alloy.B.a.clock.hatBeta K
local notation "μ" => R.alloy.B.a.clock.forcedAllowance K

variable {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
include course top floor start fixed capture live way ticket earned in
theorem original {i:ℕ}(reach:u ≤ i)(before:i+1 ≤ K):
    ‖printed R d κ pt N per K o v s ((Nat.le_succ i).trans before) 1-
      actualTransport R.family (N:=N) (face (guarded R d N per K o v) s) ((Nat.le_succ i).trans before) 1‖ ≤
      peak R d K M s*((count R d s:ℝ)*(4*hitWidth (K₀)*Real.exp ((K₀).supportExponent+2)*B*μ)):=by
  rw [WilsonOriginalMicroscopicGuardedVerseBalance.original R d κ pt N per K live o v s]
  exact WilsonOriginalMicroscopicGuardedFlat.original R d π Γ Ψ course live top simple way D Q ticket floor start fixed capture o v M earned s reach before

include course top floor start fixed capture live way ticket earned in
theorem power (q:ℕ){ε:ℝ}(ep:0<ε)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple q ep)).choose ≤ K)
    {i:ℕ}(reach:u ≤ i)(before:i+1 ≤ K):
    ‖printed R d κ pt N per K o v s ((Nat.le_succ i).trans before) 1-
      actualTransport R.family (N:=N) (face (guarded R d N per K o v) s) ((Nat.le_succ i).trans before) 1‖ ≤
      peak R d K M s*((count R d s:ℝ)*((4*Real.exp ((K₀).supportExponent+2))*(ε/B^q))):=by
  rw [WilsonOriginalMicroscopicGuardedVerseBalance.original R d κ pt N per K live o v s]
  exact WilsonOriginalMicroscopicGuardedFlat.power R d π Γ Ψ course live top simple way D Q ticket floor start fixed capture o v M earned s q ep late reach before

end YM.Integration.WilsonOriginalMicroscopicGuardedVerseRefund
end
