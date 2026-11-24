import YM.Integration.WilsonMarkedIndependentRegisteredFoldedIntegral
import YM.Integration.WilsonOriginalChargedQSalary


/-! The folded integral for the original rank-lowered physical page on its own
forest and receiving date. The bill is the funded bill of its original stencil. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentChargedFoldedIntegral
open Function Filter Finset Lattice Wilson RG Precision Laurent Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily Work.F03 Work.F05 Work.F08
open Next.Foundations PhysicalNext.Repeat.Legato Next.Free Stationary
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Wine Gorge Lotus Mesa PowerSeries
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
variable {ι:Type}[Fintype ι][DecidableEq ι]{D k:ι→ℕ}{I:ι→Type}[∀i,Fintype (I i)]
variable (u:G.ColorIndex)(tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
variable {N j e m d c q t:ℕ}

open WilsonMarkedIndependentRegisteredFoldedIntegral (Read evaluated)

theorem original {p L l:ℕ}{hh:l≤L}{B:MS.Local.Physical.Deck G}
    (M:MS.Land.Prescription B)(data:ActualRunQlocalNativeTuple.Datum R p L l hh ι)
    (labels:ι→MS.Rake.Label B)(μ:ℝ)(orders:ι→ℕ)(weights:ι→ℂ)(re:ι→Bool)
    (s:ι)(k:ι→ℕ)(i r:ℕ)(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)
    (draws:Q.draws=V)(paid:Q.paid=R.metals.O)
    {w σ:Gear G→ℝ}(hw:∀T,0<w T)
    (stamped:FundedMarkedWindingWindow.ReceiptOn R {s} {s} s (FundedOriginalMarkedInput.OrbitD data)
      (fun a=>max (k a) (WilsonOriginalChargedQSalary.grade data labels a)) e i r d c q t w σ m Q hm)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (live:m<N)(cells:(ι → Cover)→ι→Site (loose Q.draws m).L):
    let X:=WilsonOriginalChargedQSalary.lowered M data labels μ orders weights re
    let ranks:=fun a=>max (k a) (WilsonOriginalChargedQSalary.grade data labels a)
    let n:=R.family.side m p
    WilsonMarkedIndependentRegisteredFoldedSeam.Bill R Q hm N p s i r d c q t ranks X cells w σ ∧
      (∀ cap width, IndependentSourcePathFamily.bill X ranks cap width =
        IndependentSourcePathFamily.bill (FundedOriginalMarkedInput.chosen M data labels μ orders weights re) ranks cap width) ∧
      ∀(root:ι → Cover)(test:Case (FundedOriginalMarkedInput.OrbitD data)),
        Read R N m n s ranks X (chartIn (loose Q.draws m) root (cells root)) test
          (ratioHigh Q.draws Q.paid N m) u tags ∧
        ratioHigh Q.draws Q.paid N m=ratioHigh V R.metals.O N m:=by
  intro X ranks n
  have lawful(a row₀):(X a row₀).rank≤ranks a+(X a row₀).head:=by
    have charged:=WilsonOriginalChargedQSalary.degree M data labels μ orders weights re a row₀
    have active:WilsonOriginalChargedQSalary.pole data labels a row₀≤ranks a:=
      (Finset.le_sup (f:=WilsonOriginalChargedQSalary.pole data labels a) (Finset.mem_univ row₀)).trans (le_max_right _ _)
    change (FundedOriginalMarkedInput.chosen M data labels μ orders weights re a row₀).rank ≤ ranks a+
      ((FundedOriginalMarkedInput.chosen M data labels μ orders weights re a row₀).rank-WilsonOriginalChargedQSalary.pole data labels a row₀)
    omega
  refine ⟨WilsonMarkedIndependentRegisteredFoldedSeam.receipt R Q hm s hw stamped p live X lawful cells,
    fun cap width=>WilsonOriginalChargedQSalary.loan M data labels μ orders weights re ranks cap width,?_⟩
  exact fun root test=>⟨evaluated R u tags simple v funded live n s X lawful _ test _,by rw [draws,paid]⟩

end YM.Integration.WilsonMarkedIndependentChargedFoldedIntegral
end
