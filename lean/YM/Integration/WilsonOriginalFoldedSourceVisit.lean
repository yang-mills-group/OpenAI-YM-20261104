import YM.Integration.WilsonOriginalFoldedSourceTicket

/-! Fund the certified original leaf at its actual lifted site, using its exact share of the previous before-test tariff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonOriginalFoldedSourceVisit
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


open WilsonOriginalFoldedSourceTicket
open WilsonMarkedIndependentRegisteredFoldedSeam (Bill)
variable [Subsingleton ι]
omit [∀i,Fintype (I i)] in
theorem ticket (p:ℕ)(s:ι)(X:∀i,I i→Seed G (D i))(a:I s)(law:(X s a).rank ≤ k s+(X s a).head)
    (rooting:ι → Cover)(i r:ℕ)(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)
    {w σ:Gear G→ℝ}(hw:∀T,0<w T)
    (stamped:FundedMarkedWindingWindow.ReceiptOn R {s} {s} s D k e i r d c q t w σ m Q hm)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (live:m<N)(C:Cost):
    let P:=loose Q.draws m
    let Y:=picked X s a
    let sites:=WilsonOriginalFoldedSourceTicket.root P rooting
    let cells:=(fun _ : ι → Cover => cell P rooting)
    let width:=4*max (w (Q.mint m hm).gear) (Q.mint (m+1) (by omega)).σ
    (chartIn P sites (cells sites)=rooting) ∧
    OriginalIssuedMarkedRows.fee (k:=k) Y Q hm w=charge X k e width s a ∧
    Bill R Q hm N p s i r d c q t k Y cells w σ ∧
    ∀test:Case D,Read R N m (R.family.side m p) s k Y rooting test C u tags:=by
  intro P Y sites cells width
  have good:=WilsonOriginalFoldedSourceTicket.legal X s a law
  refine ⟨funext (WilsonOriginalFoldedSourceTicket.placed P rooting),
    WilsonOriginalFoldedSourceTicket.ledger X s a e width,
    WilsonMarkedIndependentRegisteredFoldedSeam.receipt R Q hm s hw stamped p live Y good cells,?_⟩
  intro test
  exact evaluated R u tags simple v funded live _ s Y good rooting test C

end YM.Integration.WilsonOriginalFoldedSourceVisit
end
