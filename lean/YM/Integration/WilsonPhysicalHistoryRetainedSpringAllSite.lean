import YM.Integration.WilsonPhysicalHistoryRetainedSpringFundedKinetic
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRosterPrice
/-! At a fixed occupied site, replace the entire original entering Wilson
action on its own measured chamber by the finite sum of its paid jets. -/
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

def springTaylorAt (R : Run G) (N per j r : ℕ) (Z : SeriesA G)
    (x : Site (R.family.side j per)) (z : Dir G (R.family.side j per)) (K : ℕ) (g : ℝ) : ℂ:=
  let p:=finitePitch R N j r g
  let γ:=g^2*pitchTail R N j r g
  let B:=(R.family.path.levels.params j).clip
  let path:=(R.family.path.rep N per j).path
  (γ:ℂ)*kineticTaylor B path x z (K+1) g+rosterTaylor path Z (γ+R.alloy.B.kin.alpha N j)
    (Integral.temperature g*p) (g/Real.sqrt p) true x z K g

theorem spring_taylor_zero (R : Run G) (N per j r : ℕ) (Z : SeriesA G)
    (x : Site (R.family.side j per)) (z : Dir G (R.family.side j per)) (g : ℝ) :
    springTaylorAt R N per j r Z x z 0 g=0:=by
  simp only [springTaylorAt,Nat.zero_add,kinetic_first,roster_taylor_zero,mul_zero,add_zero]

def SpringSiteEstimate (R : Run G) (m N : ℕ) (Z : SeriesA G) (r K l : ℕ) (ε η : ℝ) : Prop :=
  let V:=R.family.path.levels
  ∀ per : ℕ,
    let j:=m+1
    let S:=V.clock.op m per
    let s:=V.clock.hatBeta m
    let g:=Pert.Asymptotics.regulatorRun R.family N per j
    ∀ {W μ budget : ℝ} {P : Teller G} {Q : Target G P} {o : Target.Order G W}
      {T : Tube G S} {Y : Rep G (R.family.side j per)},
      (H : Cash W s μ S.patch.L Q o budget T Y) → 0≤Pressure.temp s →
      WilsonCoherentMayerCovarianceCalendar.deviation G S.patch.L o≤1+Real.log (betaF G s S.patch.L) →
      ∀ (χ : Chi) (fan : Finset (LocalLTE.Fan.Veil (R.family.side m per) (R.family.side j per)))
        (i : Greenbelt.Reserve S) (tag : S.Choices) (y : (Greenbelt.allot i).Slice G)
        (x : Site (R.family.side j per)),
      let F:=Greenbelt.allot i
      let X:=WilsonCoherentMayerHearing.chamber T s o.K χ 1 fan i tag
      let β:=Integral.temperature g
      let E:=fun z=>(springAt R N per j r Z g x ((X.wrapY y).input ((X.wrapY y).liftA β z)):ℂ)-
        springTaylorAt R N per j r Z x (angularSample F z) K g
      Integrable E X.dice ∧ Integrable (fun z=>‖E z‖^(l+1)) X.dice ∧
        (∫ z,‖E z‖^(l+1) ∂X.dice)≤(ε*g^(((K+3:ℕ):ℝ)-η))^(l+1)

theorem cofinal_spring_site (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (credit : Credit) (d M r K l : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N : ℕ,m+1<N →
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀ σ : ℝ,0<σ → σ⁻¹≤zz V (m+1) →
      ∀ Z : SeriesA G,Draw Z σ D → Z.length≤M → (∀ a∈Z,3≤a.grade) → (∀ a∈Z,a.grade≤d) →
        SpringSiteEstimate R m N Z r K l ε η := by
  intro V
  have half : 0<ε/2:=half_pos ep
  filter_upwards [cofinal_roster_site R simple slow v rows credit d M r K l half hp,
    funded_kinetic R simple slow v rows r K l half hp,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)]
    with m roster kinetic small
  intro N later D σ width clock Z draw length low upper per j S s g W μ budget P Q o T Y H temp bill χ fan i tag y x F X β E
  let p:=finitePitch R N j r g
  let γ:=g^2*pitchTail R N j r g
  let w:=γ+R.alloy.B.kin.alpha N j
  let B:=(V.params j).clip
  let path:=(R.family.path.rep N per j).path
  let U (z : Air (R.family.side j per) G):=(X.wrapY y).input ((X.wrapY y).liftA β z)
  let f (z : Air (R.family.side j per) G):=(γ:ℂ)*((secondAt B path x (U z):ℂ)-
    kineticTaylor B path x (angularSample F z) (K+1) g)
  let h (z : Air (R.family.side j per) G):=rosterSource path Z w (β*p) (g/Real.sqrt p) true x (U z)-
      rosterTaylor path Z w (β*p) (g/Real.sqrt p) true x (angularSample F z) K g
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per j later.le
  have gs : g≤1:=(small N per later.le).le
  let a:=ε/2*g^(((K+4:ℕ):ℝ)-η)
  let b:=ε/2*g^(((K+3:ℕ):ℝ)-η)
  have a0 : 0≤a:=by dsimp only [a]; positivity
  have b0 : 0≤b:=by dsimp only [b]; positivity
  have both:=added_error X.dice f h l a0 b0 (kinetic N per later H temp bill χ fan i tag y x)
    (roster N later σ width clock Z draw length low upper per H temp bill χ fan i tag y x true)
  have same : E=fun z=>f z+h z:=by
    funext z
    change (springAt R N per j r Z g x (U z):ℂ)-springTaylorAt R N per j r Z x (angularSample F z) K g=_
    rw [roster_incoming]
    simp only [f,h,springTaylorAt,Complex.ofReal_mul,γ,w,B,path,p,β]
    ring
  have compare : g^(((K+4:ℕ):ℝ)-η)≤g^(((K+3:ℕ):ℝ)-η):=by
    apply Real.rpow_le_rpow_of_exponent_ge gp gs
    push_cast
    linarith
  have total : a+b≤ε*g^(((K+3:ℕ):ℝ)-η):=by
    have p:=mul_le_mul_of_nonneg_left compare half.le
    dsimp only [a,b]
    linarith
  rw [same]
  exact ⟨both.1,both.2.1,both.2.2.trans (pow_le_pow_left₀ (add_nonneg a0 b0) total _)⟩

end YM.Integration.OriginalMarkedRunAction
