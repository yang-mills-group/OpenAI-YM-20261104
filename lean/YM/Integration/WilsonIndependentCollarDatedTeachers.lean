import YM.Integration.WilsonIndependentCollarFiledOpening
import YM.Integration.WilsonOriginalCensusAngularClock

/-! Both dated lower teachers on the original preselected Wilson course.
The same width opens the independent connected file and the real angular
receiver, even when the two adjacent dates have different teacher widths. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedTeachers
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth OPE.Owl
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonOriginalCollarTeacher WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse WilsonOriginalCensusTariffDate
open Comparison.Density.Mirrors Comparison.Density.Transport WilsonEmittedFiledCatalogue WilsonOriginalCollarElection
open QuadraticLocal.Earn WilsonOriginalAllOrderCalendar Push.AbsoluteSums
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}{n e:ℕ}{D k:Fin n→ℕ}{S:Type}[Fintype S]{a:Axis}{simple:G.Simple}
  {ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}

def At (s:WilsonOriginalAllOrderCourse.Schedule G)(R:Run G)(simple:G.Simple)(V:Realm G (e+1) Credit.leanC)(D k:Fin n→ℕ)
    (K P:ℕ)(δ:ℝ)(tube:LinkTube G)(pieces physical:ℕ)(p:Bool→ℕ)(span:S→ℕ)(lag:S→Bool→ℕ)(i:ℕ):Prop:=
  let L:=R.family.path.levels
  let roots:=WilsonOlderFreshGraphSchool.roots (menu (teacher (prepared s))) simple R.metals.p R.metals.K
  let σ:=Poetry.Agenda.seed roots MintClock.splits K (L.clock.J (i+1))
  let H:=L.clock.hatBeta (i+1)
  ∀hi:V.anchor ≤ i+1,WilsonOlderFreshConnectedAppointment.Paid R V hi D k δ σ ∧
    ∀(m N per p₀:ℕ)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per p₀ Ψ → m ≤ i+1 → i+1 ≤ N →
    0<σ ∧ Real.exp (σ⁻¹^2)≤H ∧
    ((Ψ (i+1)).p.supportExponent+2)*(((Ψ (i+1)).p.B:ℝ)⁻¹)≤σ/2 ∧
    (H/2≤(Ψ (i+1)).beta ∧ (Ψ (i+1)).beta≤2*H) ∧ (Real.sqrt (Ψ (i+1)).beta)⁻¹ ≤ 1/2 ∧
    (Ψ (i+1)).p.B=Nat.ceil ((Real.log H)^2) ∧ (Ψ (i+1)).p.supportExponent+2≤102 ∧
    (∀v,Begun tube pieces physical (3*span v) (span v) p (lag v) H) ∧
    ∀(M α g:ℝ),Invoice.Supports (Ψ (i+1)).p M α g σ (σ/4) → α≤102 →
      Real.exp (-(σ/4))^((Ψ (i+1)).p.B/32)≤(H^P)⁻¹

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (V:Realm G (e+1) Credit.leanC)(app:Appointed R simple V s D k)
    (K P:ℕ)(order:1≤K)(room:n≤K)(δ:ℝ)(positive:0<δ)
    (tube:LinkTube G)(pieces physical:ℕ)(p:Bool→ℕ)(span:S→ℕ)(lag:S→Bool→ℕ):
    ∀ᶠj:ℕ in atTop,At s R simple V D k K P δ tube pieces physical p span lag j ∧
      At s R simple V D k K P δ tube pieces physical p span lag (j+1):=by
  let L:=R.family.path.levels
  have grows:Tendsto (fun i=>L.clock.hatBeta (i+1)) atTop atTop:=
    (RG01.Physical.hats simple R.alloy.B.a).comp (tendsto_add_atTop_nat 1)
  have opened:=WilsonOriginalCensusAngularClock.original (teacher (prepared s)) simple MintClock.splits R
    paid.first paid.support K tube pieces physical p span lag
  have late:∀ᶠ i:ℕ in atTop,At s R simple V D k K P δ tube pieces physical p span lag i:=by
    filter_upwards [opened,(tendsto_add_atTop_nat 1).eventually (app δ positive),
      (Real.tendsto_log_atTop.comp grows).eventually_ge_atTop ((256*((P:ℝ)+1))^2)] with i actual issued big
    intro hi
    refine ⟨issued hi MintClock.splits K (L.clock.J (i+1)) order room (Or.inl rfl),?_⟩
    intro m N per p₀ π Γ Ψ law lodged cap
    obtain ⟨σpos,fee,held,band,small,size,tax,head⟩:=
      actual (L.clock.J (i+1)) le_rfl m N per p₀ π Γ Ψ law lodged cap
    refine ⟨σpos,fee,held,band,small,size,tax,head,?_⟩
    intro M α g support bounded
    have cut:=(WilsonEmittedLengthWindow.decays support size fee bounded P big).2
    simpa only [WilsonEmittedLengthWindow.strip,max_eq_left (min_le_right ..)] using cut
  exact late.and ((tendsto_add_atTop_nat 1).eventually late)

end YM.Integration.WilsonIndependentCollarDatedTeachers
end
