import YM.LocalTaylorR2.Strange.Teak
/-! # MAIN ledger and its two new Taylor debits after inheriting E. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Strange
open Exponent
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical

/-! # Lens core E-error post the actual regroup, with inherited error as input. -/
open Reel Strand Rain Roost Mallow Capstone

variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}
   (Ξ:Engine G)(R:Factor A){m n N:ℕ}{l k:ℝ}{Q:In A.B.a m n}(H:Spring R N m n l k Q) (x:ℝ)(hx:x∈Set.Icc l k)
   (w: Reel.Scroll G (A.B.a.S.side (m+1) n))(p:ℕ)
local notation "z"=> A.B.a.clock.hatBeta m
local notation "z'"=> A.B.a.clock.hatBeta (m+1)
local notation "Ω"=> A.B.a.clock.J (m+1)
local notation "B"=> A.B.a.budget m
local notation "K"=> A.B.a.params m
local notation "b"=> A.B.a.S.side m n
local notation "τ"=> (H.H.latch x)
local notation "d"=> H.ordinal
local notation "I"=> H.H.base
local notation "a!"=> H.V' x
local notation "O"=> H.X'
local notation "r"=> (H.result x)
local notation "xH"=> (Q x)
local notation "Y"=> (H.H.houses (H.H.latch x))
local notation "γ"=> A.B.kin.alpha N m
local notation "T"=> (A.B.kin.path N m)
local notation "X"=> (H.H.sister (H.H.latch x))
local notation "k₀"=> Rain.lint R.target A m
local notation "a"=> Trio.base k₀ (radiusB z)
local notation "Φ"=> A.B.a.clock.allowance m
local notation "Φ'"=> A.B.a.clock.allowance (m+1)
set_option quotPrecheck false
local notation "w'"=> ((Q (τ)).activities.E)
variable (hE:Mallow.RG12.Earned (ticketD G) R.shape A.delay)(he:Mallow.RG12.Earned (wheelD G) R.shape A.delay)(hm:m<N)
   (hΞ:Mallow.RG12.Earned (Exponent.reckon Ξ.toObservatory) R.shape A.delay) (hV:p ≤ A.B.a.clock.J (m+1)) (h₀: 3 ≤ p)
local notation "fc"=> Time.forecastE A.B.a m
local notation "Ks"=>Time.forecastK A.B.a m R.scout (Q x).beta

include hΞ hE he hV h₀ hx hm
variable {v:ℝ}(hA:Affords (Q x) A.B.a (m+1) w v)
include hA
local notation "L" => CalendarStep.loss Ω
local notation "e" => (Capstone.fare k₀ (A.B.a.params m) z +2)* (z' ^ requested (p+1) (L))
local notation "q"=> (2*v/Φ')
local notation "v'!"=> (q*fc)
local notation "p'" => Capstone.sketch R H x p true

local notation "P₀"=> (Rain.beacons H.H H.knows H.W (d) x)
local notation "g"=> Time.forecastE A.B.a m
local notation "p₀"=> (z'^requested (p+1) L)
local notation "w₀"=> ordersDue Ξ R H x w p
lemma rentU : Collection.Local O B (w₀) (e + v'!) Ks:=by
  obtain ⟨hR,h₁⟩:= arrangement Ξ R H x w p; refine scoop I _ _ _ (H.core hm x hx) rfl (active_sub I h₁ hR) ?_
  let u:= Rain.uptick H.H d x; let W:= raiment Ξ R H x w p; let S:={u with logRead:=u.logRead-W}; let g':={u with logRead:=W}; let f':=Strange.pillar Ξ.toObservatory R H x p
  let y:= Reel.allotE R H x w p; let f:=Capstone.rigging R H x p
  have hr:= Reel.royalty R H x hx w p hE he hm hV h₀ hA; have hu:= Strange.kings Ξ R H x hx w p hE hm hΞ hV hA
  obtain ⟨hx',hx1⟩:= Capstone.songs R H x p hE hV hm
  have hf: Meadow.Budget B H.H.doors.reg S.logRead (p₀+v'!+2*p₀):= by
     have hl : S.logRead=(f false).logRead-(y-(f true).logRead)+(y-W):=by change u.logRead-W=_; change u.logRead=(f true).logRead+(f false).logRead at hx1; rw [hx1]; abel
     rw [hl]; exact gauges_add (gauges_sub hx' hr) hu
  obtain ⟨hk,hV⟩:= Strange.pinnacles Ξ.toObservatory R H x p hΞ hV hm
  have hh : (w₀).logRead=(bison S (f' false) 0).regular:= by
     have hy:= layout_add («X»:=u) («Y»:=S) (Z:=g') (P₀) (f' false) (f' true) (0:Trio.Offer G b) (hk.trans (add_comm (f' true) (f' false))) (show u.logRead=u.logRead - W + W by abel)
     change (bison u P₀ (Rain.lights H.H H.knows H.W d x)).regular-(bison g' (f' true) 0).regular=_; rw [show (bison u P₀ (Rain.lights H.H H.knows H.W d x)).regular=(bison u P₀ 0).regular from rfl,hy,add_sub_cancel_right]
  rw [hh]
  let T':= Marlin.reg_bison H.H.doors (a) (2*a) S (f' false) 0 hf hV
  convert! T' using 1
  rw [add_mul,← Capstone.tariff k₀ (A.B.a.params m) z p₀ B ⟨rfl,rfl,rfl⟩]; abel
end YM.LocalTaylorR2.Strange
