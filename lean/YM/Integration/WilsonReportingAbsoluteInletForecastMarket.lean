import YM.Integration.WilsonReportingAbsoluteInletForecastIssued
import YM.Integration.WilsonWindowJointPurchase
import YM.MSbar.Ballet.Wild

/-! The original pre-launch reports and ticket, on precisely the same sheet
and map price as the incumbent campaign. Each independently realized course
then forecasts the true physical kinetic ratio on all periods and dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletForecastMarket
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Extra.Histories Source PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open WilsonLimitConstruction.FundedCompanySelection Pert.Asymptotics MSbar.Midpoint
open WilsonReportingAbsoluteInletNativeInvoice
open scoped Classical Topology BigOperators
variable {G:Gauge}

def Terms (u:G.ColorIndex) (V:MSbar.Heath.Voice G):Prediction G:=fun {M} {_} {A} F=>
  MSbar.Alto.Reports M.K M.p M.O A.B.a ∧ MSbar.Ballet.Load M.K M.p.kernel M.O A.B.a u V ∧
    (∀j,A.B.a.clock.hatBeta (j+1)≤2*A.B.a.clock.hatBeta j) ∧
    (∀j per,MSbar.Mosaic.hatW (A.B.a.clock.hatBeta j)^4≤(A.B.a.S.side j per).val) ∧
    Mallow.Hoard F.shape A.delay

theorem prepaid (simple:G.Simple) (u:G.ColorIndex) (V:MSbar.Heath.Voice G)
    (clear:MSbar.Heath.Clear G V) (s:Sheet G) (price:MapPrices):
    WilsonFundedWindowMenu.Prepared (@Terms G u V) s price:=by
  intro C E flags programs wages baton
  obtain ⟨p,hb⟩:=MSbar.Ballet.paymentP (G:=G) price
  refine ⟨p,?_⟩
  intro l hl D w q Z post scouts pocket θ records P menu start quarter
  let M:Metals G:=⟨ThroughLaunch.raise s l,price,chart G,chart_ok G⟩
  have ready:=fun i=>hb i (D.L i) ((hl i).trans (D.large i).need)
  obtain ⟨W₁,h₁,H₁⟩:=MSbar.Alto.album simple θ M.K M.O (fun i=>(ready i).pre) start
  obtain ⟨W₂,h₂,H₂⟩:=MSbar.Ballet.stage M.O M.K u V W₁ simple (chart_ok G) ready clear
  obtain ⟨W₃,h₃,H₃⟩:=Mallow.loft W₂
  obtain ⟨W₄,h₄,H₄⟩:=Mallow.stocking Z W₃
  refine ⟨W₄,h₁.trans (h₂.trans (h₃.trans h₄)),?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η Q exchange aux rider booth sheltered works divides
  have dome:=H₃.height Y (h₄.trans hY) bar wait B.a B.valid
  exact ⟨H₁ Y (h₂.trans (h₃.trans (h₄.trans hY))) bar wait _ B.valid,
    H₂ Y (h₃.trans (h₄.trans hY)) bar wait _ B.valid,dome.1,dome.2,H₄ Y hY⟩

theorem joined (simple:G.Simple) (u:G.ColorIndex) (V:MSbar.Heath.Voice G)
    (clear:MSbar.Heath.Clear G V) (other:Prediction G) (fund:WilsonFundedWindowMenu.AllPrices (@other)):
    WilsonFundedWindowMenu.AllPrices (@WilsonWindowJointPurchase.Together G (@other) (@Terms G u V)):=by
  intro s T
  exact WilsonWindowJointPurchase.joint (fund s T) (prepaid simple u V clear s (ThroughLaunch.raging s T))

theorem filed (R:Run G) (simple:G.Simple) (u:G.ColorIndex) (V:MSbar.Heath.Voice G)
    (money:Terms u V R.kit) (p:ℕ):
    ∃ (k₀:ℕ) (a:ℕ→ℕ→ℕ→ℝ),(∀N per,k₀≤N→∃S:Scene R.family.path.levels per (p+2),
      Realized R.alloy.B.kin N per k₀ (p+2) (MSbar.Lis.sun G u) S ∧
        ∀j,a N per j=MSbar.Bakery.taste (p+2) (S.action j) (regulatorRun R.family N per j)) ∧
      InversePrice R p (fun N per j=>(a N per j)⁻¹):=by
  obtain ⟨reports,load,hats,width,hoard⟩:=money
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2
    intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hi
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hi).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have hh:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  apply WilsonReportingAbsoluteInletForecastIssued.selected R simple p
    (fun N per k S=>Realized R.alloy.B.kin N per k (p+2) (MSbar.Lis.sun G u) S)
    (fun N per S j=>MSbar.Bakery.taste (p+2) (S.action j) (regulatorRun R.family N per j))
  filter_upwards [sceneP R.b R.Q R.T R.t R.stories R.doors ch V (p+4) simple hoard u (p+2) 6 reports
    load hats width growth (by omega) (by decide) (by omega)] with k receive N per kN
  exact ⟨MSbar.Alto.chosen R.alloy.B simple reports hh N u (p+2) per kN,
    fun S law j kj jn=>(receive N per S law).2 j kj jn⟩

end YM.Integration.WilsonReportingAbsoluteInletForecastMarket
