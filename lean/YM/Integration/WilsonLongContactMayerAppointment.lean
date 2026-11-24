import YM.Integration.WilsonLongContactMayerBooking
import YM.Integration.WilsonCoherentMayerElection
import YM.Integration.WilsonRootedSubmittedTail

/-! A single physical nonbare source, derivative booking, and finite Wilson-to-Wick comparison on the original regulator calendar. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactMayerAppointment
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical

open RGLocalTaylor RGLocalTaylor.Laminate

open QLocalRequestedHeirPurchase WilsonCoherentMayerElection
open WilsonPositionSeparatedProfileMayerThermalElection (Sales)
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V}
    (J:Request V) (Δ:Daisy.Charity.RG12.Decal G) (extra:Stage→ℕ→ℝ) (γ:ℝ)
    (ρ:WilsonLongContactSectorProtection.Premium G J.outputFieldOrder) (test:Demand G) (R:Run G) (licensed:WilsonLongContactMayerBooking.Sold J Δ extra γ ρ test R.kit) (A:NumericSchedule R.family J) (d:LocalFormal.Datum R.family Γ)
local notation "a₀" => R.alloy.B.a
local notation "m₀" => d.level
local notation "j₁" => (a₀).clock.J (m₀+1)
local notation "j₀" => (a₀).clock.J (m₀)
local notation "x₀" => (a₀).clock.hatBeta (m₀)
local notation "S₀" => (a₀).clock.op (m₀) d.period
local notation "T₀" => ships R.alloy.B d.cutoff (m₀) d.period
local notation "P₀" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "C₀" => libretto J R.metals.p R.metals.K (j₁) (j₀)
local notation "Q₀" => R.kit.target (j₁) (j₀)
local notation "b₀" => licensed.choose (j₁) (j₀)


omit [Fintype V] in
theorem booking : WilsonLongContactSectorProtection.Offered J ρ Δ (Q₀) (C₀) (b₀) (S₀).patch (x₀) γ ∧
    Earlier J R.metals.p R.metals.K extra (j₁) (j₀) (S₀).patch.L.val ∧
    (Sales J (Q₀) (S₀).patch (b₀) (j₁) (x₀) ∧ test (Q₀) (S₀).patch (b₀) (j₁) (x₀)):=by
  have st:=step_paid (a₀) (m₀)
  have fr:=first_le R.alloy.B.valid (m₀)
  have hL:(S₀).patch.L=R.rolls.L (j₁):=block_eq R.alloy.B.valid _
  have hJ:(S₀).patch.J=(j₁):=(Testing.proceeds R.alloy.B d.cutoff (m₀) d.period d.below).atStep
  have hP:(S₀).patch=Clockwork.patch R.rolls st fr:=by
    cases he:(S₀).patch;rw [he] at hL hJ;unfold Clockwork.patch;congr
  have shelf:=licensed.choose_spec.2 _ _ (R.alloy.B.valid.pays _) _ st fr
  rw [hP];exact ⟨shelf.1,licensed.choose_spec.1 _ _ st,shelf.2.2⟩

theorem original (simple:G.Simple):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let lev:=R.alloy.B.a
      let i:=lev.clock.J d.level
      let j:=lev.clock.J (d.level+1)
      let b:=licensed.choose j i
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let S:=lev.clock.op d.level d.period
      let Q:=R.kit.target j i
      let x:=lev.clock.hatBeta d.level
      ∃ H:WilsonRootedSubmittedTail.CashAt I b,Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
        Crossed J γ R A d b H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
        WilsonLongContactSectorProtection.Offered J ρ Δ Q (libretto J R.metals.p R.metals.K j i) b S.patch x γ ∧ (Sales J Q S.patch b j x ∧ test Q S.patch b j x):=by
  have warm:=(tendsto_add_atTop_nat 1).eventually (QLocalRequestedSectorIntake.affordable (J:=J) R simple)
  filter_upwards [ManuscriptQLocalVacuumCash.funds (Γ:=Γ) R A simple,warm] with m charge money d hm F η I admitted
  subst m
  let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  let old:=ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
  let Y:=QLocalInheritedRegularSlots.carrier old
  have row:=ManuscriptQLocalVacuumFamily.bought I admitted 1
  have hin:=QLocalRequestedSectorIntake.intake R I admitted (I.inherited_bound.trans (money d.cutoff d.period d.below))
  have e:=ManuscriptQLocalVacuumCash.intake R A d F I admitted hin (charge d rfl F I)
  have orig:=QLocalInheritedRegularSlots.intake old e
  have full:=(QLocalInheritedRegularSlots.original old).Ebound row.1.boundE
  obtain ⟨window,early,market⟩:=booking J Δ extra γ ρ test R licensed d
  obtain ⟨H,ren,cross⟩:=QLocalRequestedSectorCalendar.source_at_on J Δ extra γ R A d _ window.window early Y orig rfl rfl _ full
  exact ⟨H,ren,cross,window,market⟩

end YM.Integration.WilsonLongContactMayerAppointment
