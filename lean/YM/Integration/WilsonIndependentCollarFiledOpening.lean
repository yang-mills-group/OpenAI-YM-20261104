import YM.Integration.WilsonIndependentCollarOriginalWages
import YM.Integration.WilsonIndependentCollarPhysicalCharges

/-! The enrolled clock supplies both the actual connected appointment
and the exponential reserve at precisely the same original teacher width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarFiledOpening
open Filter Function Finset Lattice RG RG.Supply Org Wilson Precision QuadraticLocal QuadraticLocal.Earn Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Ticket WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonOriginalAllOrderCalendar WilsonOriginalCollarTeacher
open WilsonOriginalCollarElection WilsonIndependentCollarCensusCourse
open scoped Classical Topology
universe u
variable {G:Gauge}{a:Axis}{simple:G.Simple}{ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}
variable {n e:ℕ}{D k:Fin n→ℕ}

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (V:Realm G (e+1) Credit.leanC)(app:Appointed R simple V s D k)
    (K P:ℕ)(order:1≤K)(room:n≤K)(δ:ℝ)(pos:0<δ):
    let L:=R.family.path.levels
    let D₀:=WilsonOlderFreshGraphSchool.roots (menu (teacher (prepared s))) simple R.metals.p R.metals.K
    ∀ᶠ m:ℕ in atTop,∀hm:V.anchor ≤ m,∀x:ℕ,(x=L.clock.J m ∨ x=L.clock.J (m+1)) →
      let σ:=QuadraticLocal.Poetry.Agenda.seed D₀ MintClock.splits K x
      let H:=L.clock.hatBeta (m+1)
      WilsonOlderFreshConnectedAppointment.Paid R V hm D k δ σ ∧
        0<σ ∧ Real.exp (σ⁻¹^2)≤H ∧ (102:ℝ)/(Nat.ceil ((Real.log H)^2):ℝ)≤σ/2 ∧
        ∀(B:BudgetPoint)(M α g:ℝ),Invoice.Supports B M α g σ (σ/4) →
          B.B=Nat.ceil ((Real.log H)^2) → α≤102 →
          Real.exp (-(σ/4))^(B.B/32)≤(H^P)⁻¹:=by
  intro L D₀
  have rise:Tendsto L.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (L.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have fast:=Real.tendsto_log_atTop.comp (rise.comp (tendsto_add_atTop_nat 1))
  filter_upwards [app δ pos,paid.first K,fast.eventually_ge_atTop ((256*((P:ℝ)+1))^2)]
    with m earned filed late
  intro hm x stage σ H
  have xm:x ≤ L.clock.J (m+1):=by
    rcases stage with eq|eq
    · exact eq.le.trans (L.fits.mono (Nat.le_succ m))
    · exact eq.le
  obtain ⟨positive,tariff,span⟩:=filed x xm
  refine ⟨earned hm MintClock.splits K x order room stage,positive,tariff,span,?_⟩
  intro B M α g supports size bounded
  have fare:=(WilsonEmittedLengthWindow.decays supports size tariff bounded P late).2
  have strip:WilsonEmittedLengthWindow.strip (σ/4) σ=σ/4:=max_eq_left (min_le_right ..)
  simpa only [strip] using fare

end YM.Integration.WilsonIndependentCollarFiledOpening
end
