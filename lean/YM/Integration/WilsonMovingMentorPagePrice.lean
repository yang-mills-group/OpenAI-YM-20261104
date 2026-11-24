import YM.Integration.WilsonMovingMentorPageStudy

/-! The genuine page for the marked course, evaluated at the physical
temperature on the original factor. The monitor exponent is chosen before
the temperature, cutoff, circumference and all probes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorPagePrice
open Push.AbsoluteSums Pressure
open Precision RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.PriceCompiler Org AllOrder AllOrder.Floe.Step QuadraticLocal QuadraticLocal.Mentor
open scoped Classical

theorem at_date {G : Gauge} (R : Run G) {ψ : ℕ → ℕ}
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel} {Q : r.Tab R.rolls}
    (books : Offices.Books r R.rolls Q ψ) (Qa : Forecast r R.rolls Q ψ books)
    (active : ∀ j, MintClock.Employment r ψ j (R.rolls.L j))
    (calendar : MintClock.Regency r R.rolls Q R.kit.target ψ books Qa R.alloy.delay) (m : ℕ) :
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let x := R.alloy.B.a.clock.hatBeta m
    ∀ (op : Opportunity j i) (K : Epoch r R.rolls j i op) (k n : ℕ), n ≤ i → k+1 ≤ op.stage →
      op.count ≤ Burn.horizon K.vac+2 →
      let page := MintClock.ink r R.rolls Q R.kit.target ψ books Qa op K k n
      let amount := MintClock.Page.beam G (R.rolls.L j) page (R.metals.p.profile j) (R.metals.p.profile i)
      MintClock.Page.Eligible G (R.rolls.L j) page ∧ 4 ≤ amount x ∧
        amount x ≤ MintClock.Page.reward (R.alloy.B.a.clock.hatBeta (m+1)) (Beaming.grain i) ∧
        ∃ e : ℕ, ∀ ξ : ℝ, R.alloy.delay.betaEntry j ≤ ξ →
          amount ξ ≤ Delay.fineMonitor G (R.rolls.L j) ξ ^ e ∧
            Delay.fineMonitor G (R.rolls.L j) ξ ^ e ≤ MintClock.Page.reward (betaF G ξ (R.rolls.L j)) (Beaming.grain i) := by
  intro j i x op K k n hn hk hr page amount
  obtain ⟨e,earned⟩ := calendar.calendar j i k n op K hn hk hr
  have paid := earned x (R.alloy.B.valid.pays m)
  refine ⟨MintClock.Page.actual r R.rolls Q R.kit.target ψ books Qa op K k n (active j) hk hr,
    MintClock.Page.roofers ..,?_,e,earned⟩
  simpa only [j,x,← beta_eq R.alloy.B.valid m] using paid.1.trans paid.2

end YM.Integration.WilsonMovingMentorPagePrice
end
