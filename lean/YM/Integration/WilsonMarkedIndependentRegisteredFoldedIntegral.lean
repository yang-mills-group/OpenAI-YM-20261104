import YM.Integration.WilsonMarkedIndependentRegisteredFoldedSeam

/-! The registered Wilson page, the genuine folded affine Wick integral and
the funded covered address estimate on one nonbare date. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentRegisteredFoldedIntegral
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

def Read (N j:ℕ)(n:Side)(s:ι)(k:ι→ℕ)(X:∀i,I i→Seed G (D i))(p:ι → Cover)(test:Case D)
    (C:Cost)(u:G.ColorIndex)(tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices):Prop:=
  let P:=destination V N j
  let E:=independent X p
  let W:=Dove.model V wood b R.metals.O u N (j+1)
  let T:=tuftV (touch test {s}) (E {s})
  let H:=WilsonMarkedIndependentFoldedIntegral.folded R N j (mass k {s}) T.1 n
  pPly test {s} (coilH V R.metals.O j N n E k C {s})=Blue.mix C H ∧
    Blue.flash H=Reef.tossed P R.metals.O (b j) (wood j) n (tags j n)
      (Mesa.stone W (n*P.L)) (Blue.flash (T.1 (n*P.L)))

theorem evaluated (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (live:j<N)(n:Side)(s:ι)(X:∀i,I i→Seed G (D i))(h:∀i a,(X i a).rank≤k i+(X i a).head)
    (p:ι → Cover)(test:Case D)(C:Cost):Read R N j n s k X p test C u tags:=by
  let E:=independent X p
  let T:=tuftV (touch test {s}) (E {s})
  have auth:Auth (mass k {s}) T:=
    ((IndependentSourcePathFamily.preblock X (k:=k) p {s} 0 zero_lt_one h).2.1 {s}).tuft (touch test {s})
  refine ⟨?_,WilsonMarkedIndependentFoldedIntegral.finite R u tags simple v funded live _ T auth n⟩
  rw [WilsonMarkedIndependentFoldedBirth.original V R.metals.O j N n s X h p C]
  unfold pPly
  rw [ply_mixX]
  apply congr_arg _
  exact reed_maps _ _ _ _ (mass k {s}) (touch test {s}).toLinearMap

/-- The source is the chosen original Wilson microscopic page, with its signed
per-token dressing and positions; the funded Gazette estimate and its complete
independent normalized readout both concern this very input. -/
theorem original {p L l:ℕ}{hh:l≤L}{B:MS.Local.Physical.Deck G}
    (M:MS.Land.Prescription B)(data:ActualRunQlocalNativeTuple.Datum R p L l hh ι)
    (labels:ι→MS.Rake.Label B)(μ:ℝ)(orders:ι→ℕ)(weights:ι→ℂ)(re:ι→Bool)
    (s:ι)(k:ι→ℕ)(i r:ℕ)(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)
    (draws:Q.draws=V)(paid:Q.paid=R.metals.O)
    {w σ:Gear G→ℝ}(hw:∀T,0<w T)
    (stamped:FundedMarkedWindingWindow.ReceiptOn R {s} {s} s (FundedOriginalMarkedInput.OrbitD data)
      k e i r d c q t w σ m Q hm)
    (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (live:m<N)(cells:(ι → Cover)→ι→Site (loose Q.draws m).L):
    let X:=FundedOriginalMarkedInput.chosen M data labels μ orders weights re
    let n:=R.family.side m p
    WilsonMarkedIndependentRegisteredFoldedSeam.Bill R Q hm N p s i r d c q t k X cells w σ ∧
      ∀(root:ι → Cover)(test:Case (FundedOriginalMarkedInput.OrbitD data)),
        Read R N m n s k X (chartIn (loose Q.draws m) root (cells root)) test
          (ratioHigh Q.draws Q.paid N m) u tags ∧
        ratioHigh Q.draws Q.paid N m=ratioHigh V R.metals.O N m:=by
  intro X n
  have rank:∀h a,(X h a).rank≤k h+(X h a).head:=fun h _=>Nat.le_add_left _ _
  exact ⟨WilsonMarkedIndependentRegisteredFoldedSeam.receipt R Q hm s hw stamped p live X rank cells,
    fun root test=>⟨evaluated R u tags simple v funded live n s X rank _ test _,by rw [draws,paid]⟩⟩

end YM.Integration.WilsonMarkedIndependentRegisteredFoldedIntegral
end
