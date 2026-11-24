import YM.Integration.WilsonMovingMentorPageCoupling
import YM.Integration.WilsonMovingMentorPagePrice
import YM.Integration.WilsonMovingMentorPageReserve

/-! An advance contraction for all the genuinely filed probes at a stage.
It depends only on the physical clock, and compensates every admissible
course page before any period, configuration or exterior is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorPageRefund
open Filter Precision RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.PriceCompiler Org AllOrder AllOrder.Floe.Step QuadraticLocal QuadraticLocal.Mentor
open scoped Classical Topology

def cap {G : Gauge} (R : Run G) (m : ℕ) : ℝ :=
  (R.alloy.B.a.clock.hatBeta (m+1))^(Beaming.grain (R.alloy.B.a.clock.J m))

theorem original {G : Gauge} (R : Run G) (simple : G.Simple) {ψ : ℕ → ℕ}
    (enrollment : WilsonMovingMentorPageStudy.Enrolled ψ R.kit) (slots : ℕ) {δ : ℝ} (positive : 0 < δ) :
    ∃ (r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : r.Tab R.rolls)
      (books : Offices.Books r R.rolls Q ψ) (Qa : Forecast r R.rolls Q ψ books),
      AllOrder.Transit.Pass r Q R.alloy R.kit ∧ Offices.Sales r R.rolls Q R.kit.shape R.kit.scout ψ books ∧
      Educated r R.rolls Q R.kit.shape R.kit.scout ψ books R.alloy.delay ∧
      MintClock.Hospital r R.rolls Q R.kit.target ψ books Qa R.alloy.delay ∧
      MintClock.Regency r R.rolls Q R.kit.target ψ books Qa R.alloy.delay ∧
      Spill.Raffle.Warm G r R.alloy.delay ψ ∧ WilsonMovingMentorRootRadius.Income (M:=R.metals) r ψ R.alloy.delay ∧
      ∀ᶠ m : ℕ in atTop, 0 < (cap R m)⁻¹ ∧
        (cap R m)^slots ≤ (R.alloy.B.a.clock.hatBeta (m+1))^δ ∧
        let j := R.alloy.B.a.clock.J (m+1)
        let i := R.alloy.B.a.clock.J m
        let x := R.alloy.B.a.clock.hatBeta m
        ∀ (op : Opportunity j i) (K : Epoch r R.rolls j i op) (k n : ℕ), n ≤ i → k+1 ≤ op.stage →
          op.count ≤ Burn.horizon K.vac+2 →
          let page := MintClock.ink r R.rolls Q R.kit.target ψ books Qa op K k n
          let Ω := MintClock.Page.beam G (R.rolls.L j) page (R.metals.p.profile j) (R.metals.p.profile i) x
          4 ≤ Ω ∧ (cap R m)⁻¹ ≤ Ω⁻¹ := by
  obtain ⟨r,Q,books,Qa,pass,scheduled,education,crews,hire,hospital,calendar,insured,radius⟩ := enrollment
  refine ⟨r,Q,books,Qa,pass,scheduled,education,hospital,calendar,insured,radius,?_⟩
  obtain ⟨start,warm⟩ := eventually_atTop.1
    ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_ge_atTop start,WilsonMovingMentorPageReserve.powers R simple slots positive] with m late priced
  have hot : 1 ≤ R.alloy.B.a.clock.hatBeta (m+1) := warm (m+1) (by omega)
  have realCap : 0 < cap R m := Real.rpow_pos_of_pos (zero_lt_one.trans_le hot) _
  refine ⟨inv_pos.mpr realCap,priced (cap R m) realCap.le le_rfl,?_⟩
  intro j i x op K k n hn hk hr page Ω
  obtain ⟨_,roof,spent,_⟩ := WilsonMovingMentorPagePrice.at_date R books Qa hire calendar m op K k n hn hk hr
  exact ⟨roof,inv_anti₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<4) roof) (spent.trans (min_le_right ..))⟩

/-- The physical order spent in restoring all occupied entries of the registered page. -/
theorem restored {G : Gauge} (R : Run G) (simple : G.Simple) {ψ : ℕ → ℕ}
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel} {Q : r.Tab R.rolls}
    (books : Offices.Books r R.rolls Q ψ) (Qa : Forecast r R.rolls Q ψ books)
    (active : ∀ j, MintClock.Employment r ψ j (R.rolls.L j))
    (calendar : MintClock.Regency r R.rolls Q R.kit.target ψ books Qa R.alloy.delay)
    (slots q : ℕ) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      let j := R.alloy.B.a.clock.J (m+1)
      let i := R.alloy.B.a.clock.J m
      let x := R.alloy.B.a.clock.hatBeta m
      ∀ (op : Opportunity j i) (K : Epoch r R.rolls j i op) (k n : ℕ), n ≤ i → k+1 ≤ op.stage →
        op.count ≤ Burn.horizon K.vac+2 →
        let page := MintClock.ink r R.rolls Q R.kit.target ψ books Qa op K k n
        let Ω := MintClock.Page.beam G (R.rolls.L j) page (R.metals.p.profile j) (R.metals.p.profile i) x
        4 ≤ Ω ∧ (cap R m)⁻¹ ≤ Ω⁻¹ ∧ ∀ N per : ℕ, m < N →
          let g := ConnectedActivityE6.Coat.gStep (R.family.path.rep N per (m+1)).beta
          Ω^slots*g^(q+1) ≤ ε*g^q ∧ (cap R m)^slots*g^(q+1) ≤ ε*g^q := by
  filter_upwards [WilsonMovingMentorPageCoupling.repaid R simple slots q positive] with m income
  intro j i x op K k n hn hk hr page Ω
  obtain ⟨_,roof,row,_⟩ := WilsonMovingMentorPagePrice.at_date R books Qa active calendar m op K k n hn hk hr
  have charged : Ω ≤ cap R m := row.trans (min_le_right ..)
  have positiveRow : 0 < Ω := (by norm_num : (0:ℝ)<4).trans_le roof
  have positiveCap := positiveRow.trans_le charged
  refine ⟨roof,inv_anti₀ positiveRow charged,?_⟩
  intro N per live
  exact ⟨income Ω positiveRow.le charged N per live,income (cap R m) positiveCap.le le_rfl N per live⟩

end YM.Integration.WilsonMovingMentorPageRefund
end
