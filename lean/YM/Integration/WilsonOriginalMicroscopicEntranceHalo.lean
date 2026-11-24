import YM.Integration.WilsonOriginalMicroscopicEntranceSockets
import YM.Integration.WilsonOriginalMicroscopicGuardedVerseRefund

/-! On the actual earlier field, opening the canonical K guard in the jointly
born N trial costs only its original failed halo, at the physical powers of spacing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHalo
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
   (earned:∀a,(R.family.labels.level (d a)).coeffSize (v a)≤M a)(s:(Stock.census (Fin 3)).Mode)
local notation "X" => Config G (R.family.side K per)
local notation "new₀" => raw R d N per K o v
local notation "old₀" => guarded R d N per K o v
local notation "S₀" => footprint R d per K o s.val
local notation "K₀" => R.alloy.B.a.budget K
local notation "B" => R.alloy.B.a.clock.hatBeta K
local notation "μ" => R.alloy.B.a.clock.forcedAllowance K

variable {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
variable (high:∀a:Fin 3,R.family.book.Ref (d a))(born:Fin 3→Site (R.family.side N per))
local notation "receive" => WilsonOriginalMicroscopicEntranceSockets.read R d high born live
local notation "scale" => WilsonOriginalMicroscopicEntranceFiling.units R d K s

include κ pt in
theorem held {i:ℕ}(before:i+1≤K)(W:Config G (R.family.side i per)):
    let step:i≤K:=(Nat.le_succ i).trans before
    let E:=SelectedCofactorAnchoredRegister.hot (G:=G) (R.family.path.rep N per K).p.threshold (S₀)
    ‖receive step new₀ s W-receive step old₀ s W‖≤
      ‖scale‖*(WilsonOriginalMicroscopicGuardedPosterior.gross R d N per K v s.val*
        (WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W).real E):=by
  dsimp only
  rw [WilsonOriginalMicroscopicEntranceSockets.correction R d κ pt high born o v live,norm_mul,norm_neg]
  exact mul_le_mul_of_nonneg_left (WilsonOriginalMicroscopicGuardedHeld.original R d live before o v s.val W).2 (norm_nonneg _)

include course top floor start fixed capture live way ticket earned κ pt in
theorem flat (q:ℕ){ε:ℝ}(ep:0<ε)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple q ep)).choose ≤ K)
    {i:ℕ}(reach:u ≤ i)(before:i+1≤K):
    let step:i≤K:=(Nat.le_succ i).trans before
    ‖receive step new₀ s 1-receive step old₀ s 1‖≤
      ‖scale‖*(peak R d K M s.val*((count R d s.val:ℝ)*((4*Real.exp ((K₀).supportExponent+2))*(ε/B^q)))):=by
  dsimp only
  rw [WilsonOriginalMicroscopicEntranceSockets.correction R d κ pt high born o v live,norm_mul,norm_neg]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have bought:=WilsonOriginalMicroscopicGuardedVerseRefund.power R d π Γ Ψ course live top simple way D Q ticket
    floor start fixed capture o v M earned s.val κ pt q ep late reach before
  rwa [WilsonOriginalMicroscopicGuardedVerseBalance.original R d κ pt N per K live o v s.val] at bought

end YM.Integration.WilsonOriginalMicroscopicEntranceHalo
end
