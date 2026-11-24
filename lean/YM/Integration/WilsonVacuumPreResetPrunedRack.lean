import YM.Integration.WilsonVacuumPreResetPrunedIntake
import YM.RG01Estimate.SafeVac

noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedRack
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

open Evoc
local notation "B" => (a).budget m
local notation "hero" => (R.kit.target ((a).clock.J (m+1)) ((a).clock.J m)).halo

/-- The catalogue size is fixed from the actual two funded stages before the
    fine cutoff, physical period, finite subroster or gauge field. -/
theorem original (r span:ℕ) :
    ∃ ℓ≥hero,∀ (N per:ℕ)(_hm:m<N)(Γ:Type)
      (A:Board.Insured R.alloy N m (span*(B).B) ((a).S.oneStep m per).exact_size (R.family.path.rep N per (m+1)).beta Γ)
      (_same:A.rep.eval=(R.family.path.rep N per (m+1)).eval),
      ∃ H:Opera.Guide R.alloy.B R.kit.shape N m per A.rep,Opera.Price R.alloy.B R.kit.shape N m per A.rep H ∧
      let M:=Match.staple (H:=H) (J:=H) rfl rfl rfl
      let γ:=R.alloy.B.kin.alpha N m
      let L:=ledger R.kit H
      (∀O W,(R.family.path.rep N per m).eval W=earlyValue L (R.alloy.B.kin.path N m)
        ((a).params m).clip B (vacuum R.kit H H M) (R.family.path.rep N per (m+1)).beta (Song.weighty H Chi.canonical O) γ W) ∧
      (∀(P:ℕ→Finset Γ), (∀i,∀ᶠ k in atTop,i∈P k) →
        ∀z,Pruned.chosen H M A.sacrifice r z→∀ᶠ k in atTop,z∈Evoc.board H A.music r (P k) k) ∧
      ∀(P:Finset Γ)(k:ℕ),∃ C:Abacus.Rack L (Meadow.studio ℓ (B).B)
        (Caddy.cut Chi.canonical H M γ A.sacrifice r (Evoc.board H A.music r P k)),
        C.polygon=Evoc.aspect H A.music (Fate.steps r) Chi.canonical γ P k:=by
  classical
  obtain ⟨ℓ,hℓ,bound⟩:=Precise.passport_hub span r hero
  refine ⟨ℓ,hℓ,?_⟩
  intro N per hm Γ A same
  have auth:Routed.EquivalentParameters (A:=R.alloy) N m per A.rep:=
    ⟨A.pathU,A.clip,A.point,by rw [A.β']; exact (R.makes.wilson.represents N per (m+1) hm).band,A.legal⟩
  obtain ⟨H,price,real⟩:=WilsonVacuumPreResetPrunedIntake.physical R hm A.rep auth A.β' same
  refine ⟨H,price,?_⟩
  intro M γ L
  refine ⟨real,?_,?_⟩
  · exact fun P hP z hz=>Evoc.exhausts H A.music r A.sacrifice A.coverage P hP z hz
  intro P k
  obtain ⟨rooted,halo⟩:=bound (B).B (B).B_pos
  have houses:Evoc.house hero (B).B (span*(B).B) (Fate.steps r) ≤Meadow.studio ℓ (B).B:=by omega
  refine ⟨Evoc.node H A.music r A.sacrifice Chi.canonical B γ k P A.cost rfl houses halo,?_⟩
  exact Evoc.pasture H A.music r A.sacrifice A.coverage Chi.canonical B γ k P A.cost rfl houses halo

end YM.Integration.WilsonVacuumPreResetPrunedRack
