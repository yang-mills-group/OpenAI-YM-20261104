import YM.Integration.WilsonPhysicalHistoryRetainedSpringRosterSite
import YM.Integration.WilsonPhysicalHistoryRetainedSpringFundedMoment
import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature

/-! Pointwise choice of the occupied site follows the purchase of the entire
earlier list and its physical moment, uniformly in the later period. -/
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

def RosterSiteEstimate (R : Run G) (m N : ℕ) (Z : SeriesA G) (r K l : ℕ) (ε η : ℝ) : Prop :=
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
        (x : Site (R.family.side j per)) (bare : Bool),
      let F:=Greenbelt.allot i
      let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 fan i tag
      let β:=Integral.temperature g
      let E:=fun z=>rosterSource path Z w (β*p) (g/Real.sqrt p) bare x
        ((X.wrapY y).input ((X.wrapY y).liftA β z))-
        rosterTaylor path Z w (β*p) (g/Real.sqrt p) bare x (angularSample F z) K g
      Integrable E X.dice ∧ Integrable (fun z=>‖E z‖^(l+1)) X.dice ∧
        (∫ z,‖E z‖^(l+1) ∂X.dice)≤(ε*g^(((K+3:ℕ):ℝ)-η))^(l+1)

theorem cofinal_roster_site (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (credit : Credit) (d M r K l : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N : ℕ,m+1<N →
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀ σ : ℝ,0<σ → σ⁻¹≤zz V (m+1) →
      ∀ Z : SeriesA G,Draw Z σ D → Z.length≤M → (∀ a∈Z,3≤a.grade) → (∀ a∈Z,a.grade≤d) →
        RosterSiteEstimate R m N Z r K l ε η := by
  intro V
  let ε':=ε/((M:ℝ)+1)
  have ep' : 0<ε':=div_pos ep (by positivity)
  obtain ⟨_,pitch⟩:=cofinal_temperature R simple v rows r
  filter_upwards [funded_chamber_moment R simple credit d K l ep' hp,
    funded_interaction R simple slow v rows r K l ep' hp,
    (tendsto_add_atTop_nat 1).eventually pitch,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)]
    with m loan barePay priced small
  intro N later D σ width dated Z filed limit low high per j S s g p w path W μ budget P Q o T Y H temp cost χ fan i tag y x bare F X β E
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per j later.le
  have gs : g≤1:=(small N per later.le).le
  have tuning:=priced N later per
  let fee:=ε'*g^(((K+3:ℕ):ℝ)-η)
  have fee0 : 0≤fee:=mul_nonneg ep'.le (Real.rpow_nonneg gp.le _)
  let U:=fun z=>(X.wrapY y).input ((X.wrapY y).liftA β z)
  let zdir:=angularSample (G:=G) F
  have marked : ∀ a∈Z,
      let d:=fun z=>((β*p*(g/Real.sqrt p)^(a.grade-a.rise):ℝ):ℂ)*
        ((sitePacket a.cells x (U z):ℂ)-siteTaylor a.cells x (zdir z) (a.rise+K+1) g)
      Integrable d X.dice ∧ Integrable (fun z=>‖d z‖^(l+1)) X.dice ∧
        (∫ z,‖d z‖^(l+1) ∂X.dice)≤fee^(l+1):=by
    intro a member d
    have one:=chamber_vertex H temp χ fan i tag y Z width filed a member x (a.rise+K+1) g p gp
      (fun _=>1) (B:=1) (fun _=>by simp) aestronglyMeasurable_const
    have full:=loan N per (Nat.lt_of_succ_lt later) H temp width dated cost Z filed a member
      (high a member) p tuning.2.2.1 tuning.2.2.2.1 χ fan i tag y x
    have degree : K+3≤a.grade+K:=by have :=low a member; omega
    have scaled : ε'*g^(((a.grade+K:ℕ):ℝ)-η)≤fee :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge gp gs
        (sub_le_sub_right (Nat.cast_le.mpr degree) η)) ep'.le
    refine ⟨?_,full.1,full.2.trans (pow_le_pow_left₀ (mul_nonneg ep'.le (Real.rpow_nonneg gp.le _)) scaled _)⟩
    simpa only [one_mul] using one.1
  have fixed:=barePay N per later H temp cost χ fan i tag y x
  have joint:=roster_site_moment X.dice U zdir path Z w (β*p) (g/Real.sqrt p) x K l M g
    limit fee0 marked fixed bare
  have funded : ((M:ℝ)+1)*fee=ε*g^(((K+3:ℕ):ℝ)-η):=by
    dsimp only [fee,ε']
    field_simp
  exact ⟨joint.1,joint.2.1,joint.2.2.trans_eq (congrArg (·^(l+1)) funded)⟩

end YM.Integration.OriginalMarkedRunAction
