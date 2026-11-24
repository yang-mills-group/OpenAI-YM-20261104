import YM.Integration.WilsonPhysicalHistoryRetainedSpringRosterPrice
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRosterProduct

/-! Each named site carries the complete actual finite list. Positions, choices
of the low signed path, and the marked cofactor all follow the uniform purchase. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open scoped Topology BigOperators Classical
variable {G : Gauge}

def RosterJointEstimate (R : Run G) (m N : ℕ) (Z : SeriesA G) (r n K : ℕ) (ε η : ℝ) : Prop :=
  let V:=R.family.path.levels
  ∀ per : ℕ,
    let j:=m+1
    let S:=V.clock.op m per
    let s:=V.clock.hatBeta m
    let g:=Pert.Asymptotics.regulatorRun R.family N per j
    let p:=finitePitch R N j r g
    let w:=g^2*pitchTail R N j r g+R.alloy.B.kin.alpha N j
    let path:=(R.family.path.rep N per j).path
    ∀ {W μ budget : ℝ} {P : Teller G} {Q : Target G P} {o : Target.Order G W}
      {T : Tube G S} {Y : Rep G (R.family.side j per)},
      (H : Cash W s μ S.patch.L Q o budget T Y) → 0≤Pressure.temp s →
      WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L o≤1+Real.log (betaF G s S.patch.L) →
      ∀ (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil (R.family.side m per) (R.family.side j per)))
        (i : Greenbelt.Reserve S) (tag : S.Choices) (y : (Greenbelt.allot i).Slice G)
        (x : Fin (n+1)→Site (R.family.side j per)) (bare : Fin (n+1)→Bool),
      let F:=Greenbelt.allot i
      let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 fan i tag
      let β:=Integral.temperature g
      let a:=fun l z=>rosterSource path Z w (β*p) (g/Real.sqrt p) (bare l) (x l)
        ((X.wrapY y).input ((X.wrapY y).liftA β z))
      let t:=fun l z=>rosterTaylor path Z w (β*p) (g/Real.sqrt p) (bare l) (x l) (angularSample F z) K g
      ∀ (J : Air (R.family.side j per) G→ℂ) {B : ℝ}, 0≤B → AEStronglyMeasurable J X.dice →
      (Integrable (fun z=>‖J z‖^(n+2)) X.dice ∧ (∫ z,‖J z‖^(n+2) ∂X.dice)≤B^(n+2)) →
      let E:=fun z=>J z*((∏ l,t l z)-∏ l,a l z)
      Integrable E X.dice ∧ ‖∫ z,E z ∂X.dice‖≤B*(ε*g^(((K+3*(n+1):ℕ):ℝ)-η))

theorem funded_roster_product (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (credit : Credit) (d M r n K : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N : ℕ,m+1<N →
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀ σ : ℝ,0<σ → σ⁻¹≤zz V (m+1) →
      ∀ Z : SeriesA G,Draw Z σ D → Z.length≤M → (∀ a∈Z,3≤a.grade) → (∀ a∈Z,a.grade≤d) →
        RosterJointEstimate R m N Z r n K ε η := by
  intro V
  let k:=min 1 ε/(2:ℝ)^(n+2)
  let u:=η/((n:ℝ)+1)
  have kp : 0<k:=div_pos (lt_min zero_lt_one ep) (by positivity)
  have up : 0<u:=div_pos hp (by positivity)
  filter_upwards [cofinal_roster_site R simple slow v rows credit d M r 0 (n+1) kp up,
    cofinal_roster_site R simple slow v rows credit d M r K (n+1) kp up,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)]
    with m first last small
  intro N later D σ width dated Z filed limit low high per j S s g p w path W μ budget P Q o T Y H temp cost χ fan i tag y x bare F X β a t J B B0 jm marked E
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per j later.le
  have gs : g≤1:=(small N per later.le).le
  have raw:=first N later σ width dated Z filed limit low high per H temp cost χ fan i tag y
  have altered:=last N later σ width dated Z filed limit low high per H temp cost χ fan i tag y
  apply roster_product X.dice n K gp gs ep a t
  · intro h
    simpa only [roster_taylor_zero,sub_zero,Nat.zero_add,Nat.cast_ofNat] using raw (x h) (bare h)
  · exact fun h=>altered (x h) (bare h)
  · exact B0
  · exact jm
  · exact marked

end YM.Integration.OriginalMarkedRunAction
