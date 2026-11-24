import YM.Integration.WilsonVacuumPreResetColdInput
import YM.RG01Estimate.Horoscope
import YM.RG01Estimate.RoutedAdapter
import YM.RG01Estimate.Stamped

/-! Charge the high part on the literal re-expressed representative, then
return the complete physical push at the measured beta to the original run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedIntake
open WilsonLimitConstruction IterationFour.Vacuum
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Geo Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum

open scoped Topology BigOperators Classical
variable {G:Gauge}


variable (R:Run G){m N per:ℕ}
local notation "a" => R.alloy.B.a
set_option quotPrecheck false
local notation "β" => (R.family.path.rep N per (m+1)).beta

theorem physical (hm:m<N)(U:RG.Rep G (R.family.side (m+1) per))
    (authorized:Routed.EquivalentParameters (A:=R.alloy) N m per U)
    (exactβ:U.beta=β)(same:U.eval=(R.family.path.rep N per (m+1)).eval):
    ∃ H:Opera.Guide R.alloy.B R.kit.shape N m per U,Opera.Price R.alloy.B R.kit.shape N m per U H ∧
      let M:=Match.staple (H:=H) (J:=H) rfl rfl rfl
      ∀O W,(R.family.path.rep N per m).eval W=earlyValue (ledger R.kit H)
        (R.alloy.B.kin.path N m) ((a).params m).clip ((a).budget m)
        (vacuum R.kit H H M) β (Song.weighty H Chi.canonical O) (R.alloy.B.kin.alpha N m) W:=by
  obtain ⟨H,price⟩:=Routed.supplies R.kit U authorized hm
  refine ⟨H,price,?_⟩
  intro M O W
  have op:=congr_fun (R.makes.wilson.steps N per m hm).1 W
  rw [←exactβ]
  refine op.trans ?_
  have eq:=Board.direct R.kit hm ((a).S.oneStep m per).exact_size H price M (F:=O) W
  refine Eq.trans ?_ eq.symm
  exact congrArg₂ (fun b (f:Config G (R.family.side (m+1) per)→ℝ)=>((a).clock.op m per).push b f W) exactβ.symm same.symm

theorem routed (hm:m<N)(U:RG.Rep G (R.family.side (m+1) per))
    (authorized:Routed.EquivalentParameters (A:=R.alloy) N m per U)
    (exactβ:U.beta=β)(same:U.eval=(R.family.path.rep N per (m+1)).eval)
    (paid:Routed.Allowed R.kit)(E:Set ℕ)(r:ℕ)(two:2≤r)(late:r≤(a).clock.J (m+1))
    {τ:ℝ}(debit:Inherit.Debits U E τ)(cap:τ≤Fate.debt r G (R.rolls.L ((a).clock.J (m+1))) ((a).clock.hatBeta m)):
    ∃ H:Opera.Guide R.alloy.B R.kit.shape N m per U,Opera.Price R.alloy.B R.kit.shape N m per U H ∧
      let M:=Match.staple (H:=H) (J:=H) rfl rfl rfl
      let L:=ledger R.kit H
      let γ:=R.alloy.B.kin.alpha N m
      let K:=CensusStep.hardCost R.kit m
      let B:=(a).budget m
      Collection.Local L B (Pruned.high H Chi.canonical M E r γ)
        (Routed.retention R.kit m*τ+Routed.spill (A:=R.alloy) m r) K ∧
      (∃v,Collection.Local L B (Pruned.low H Chi.canonical M E r γ) v K ∧
        Collection.Local L B (vacuum R.kit H H M) v K) ∧
      ∀O W,(R.family.path.rep N per m).eval W=earlyValue L (R.alloy.B.kin.path N m)
        ((a).params m).clip B (vacuum R.kit H H M) β (Song.weighty H Chi.canonical O) γ W:=by
  obtain ⟨H,price,eq⟩:=physical R hm U authorized exactβ same
  refine ⟨H,price,?_⟩
  intro M L γ K B
  have ticket:=Routed.step R.kit paid hm H price authorized.beta authorized.point M rfl E r two late debit cap
  exact ⟨ticket.1,ticket.2,eq⟩

end YM.Integration.WilsonVacuumPreResetPrunedIntake
