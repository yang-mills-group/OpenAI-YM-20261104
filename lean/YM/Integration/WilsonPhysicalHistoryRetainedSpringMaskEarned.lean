import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskBudget
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskReturn

/-! An earlier measured spectator may be correlated with the present deposited
vacuum vertex. Its error is heard once at the reporting date, followed by the
original normalized physical conditional expectation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice RG Wilson Stationary MeasureTheory OPE.Therm
open IterationFour IterationFour.Vacuum PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Ticket WilsonLimitConstruction Pert.Asymptotics
open scoped Classical Topology
variable {G : Gauge}

def SpringMaskEstimate (R:Run G) (m N:ℕ) (Z:SeriesA G) (σ C:ℝ) (r q:ℕ) (ε:ℝ) : Prop :=
  ∀per,let j:=m+1
    let g:=regulatorRun R.family N per j
    ∀(x:Site (R.family.side j per)) (k:ℕ) (ek:k≤j),
      let f (U:Config G (R.family.side j per)):ℂ:=((maskedSpringAt R N per j r Z σ C g x U-springAt R N per j r Z g x U:ℝ):ℂ)
      let F:=actualTransport R.family (N:=N) f ek
      let μ:=scene R.family.path N per k
      Integrable F μ ∧ Integrable (fun U=>‖F U‖^2) μ ∧
        (∫U,‖F U‖ ∂μ)≤ε*g^q ∧ (∫U,‖F U‖^2 ∂μ)≤(ε*g^q)^2 ∧
        ∀H:Config G (R.family.side k per)→ℂ,AEStronglyMeasurable H μ→Integrable (fun U=>‖H U‖^2) μ→
        Integrable (fun U=>H U*F U) μ ∧ (∫U,‖H U*F U‖ ∂μ)≤Real.sqrt (∫U,‖H U‖^2 ∂μ)*(ε*g^q)

theorem cofinal_spring_mask_return (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (heat : Poetry R.family.path.levels) (v:ℕ→Gear G→ℝ) (rows:FundedMarkedCoverRows.prices v R.kit)
    (credit:Credit) (d M r q:ℕ) {ε:ℝ} (ep:0<ε) :
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,let j:=m+1
      let C:=credit.buy (zz V j)+zz V j*V.clock.loopCap j
      ∀(N:ℕ),j<N→∀σ,0<σ→σ⁻¹≤zz V j→∀Z:SeriesA G,Draw Z σ C→Z.length≤M→
      (∀a∈Z,0<a.grade)→(∀a∈Z,a.grade≤d)→SpringMaskEstimate R m N Z σ C r q ε := by
  intro V
  let A:=maskSpringConstant G d M
  have an: 0≤A:=by dsimp [A,maskSpringConstant,gramCost,maskRosterPrice];positivity
  filter_upwards [cofinal_spring_mask_budget R simple slow heat v rows credit d M r,
    (tendsto_add_atTop_nat 1).eventually (spring_mask_clock R simple 10 q an ep),
    (tendsto_add_atTop_nat 1).eventually (spring_mask_clock R simple 20 (2*q) (sq_nonneg A) (sq_pos_of_pos ep))]
    with m budget one two
  intro j C N later σ hs width Z draw count lower upper per date g x k ek f F μ
  let w:=1+V.clock.hatBeta j
  let B:=A*w^10
  let fee:=(625*(Fintype.card PlaqAxes:ℝ))*V.clock.forcedAllowance j
  let raw (U:Config G (R.family.side j per)):=maskedSpringAt R N per j r Z σ C g x U-springAt R N per j r Z g x U
  have invoice:=budget N later σ hs width Z draw count lower upper per x
  have measured:Measurable f:=Complex.continuous_ofReal.measurable.comp invoice.1
  have cap (U):‖f U‖≤B:=by simpa only [f,Complex.norm_real] using invoice.2.1 U
  have paid : (∫U,‖f U‖ ∂scene R.family.path N per j)≤B*fee:=by
    simpa only [f,Complex.norm_real] using invoice.2.2
  have ret:=spring_mask_return R.family R.makes later.le f measured cap paid ek
  have small1 : B*fee≤ε*g^q:=one N later.le per
  have small2 : B*(B*fee)≤(ε*g^q)^2:=calc
    B*(B*fee)=A^2*w^20*fee:=by dsimp only [B];ring
    _≤ε^2*g^(2*q):=two N later.le per
    _=(ε*g^q)^2:=by rw [Nat.mul_comm 2 q,pow_mul,mul_pow]
  have second:=ret.2.2.2.trans small2
  have gp:=IterationFour.Currency.g_pos R.makes N per j later.le
  exact ⟨ret.1,ret.2.1,ret.2.2.1.trans small1,second,
    fun H hm hi=>spring_mask_spectator F H ret.1.1 hm ret.2.1 hi (mul_nonneg ep.le (pow_nonneg gp.le _)) second⟩

end YM.Integration.OriginalMarkedRunAction
