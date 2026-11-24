import YM.Juniper.Voucher.Fleet
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Voucher
open UVExtension
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
open Oriel Charted Dales Tour
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    {N m n : ℕ}{Q ε θ b C W u:ℝ}
local notation "B" => A.B.a
local notation "Y" => A.B.a.clock.hatBeta (m+1)
variable (T:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T'"=> (A.B.a.params m)
local notation "P₀"=> Dales.mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
local notation "K" => Guild.Market R H.atTopH
local notation "σ"=> Time.forecastE A.B.a m
open Refrain Push.AbsoluteSums
variable {x y:Valve (m+1) n A.B.a d}(hx: Reality A.B.a (m+1) n d x C)(hy: Reality A.B.a (m+1) n d y C)
local notation "u₀" => H.oracle R d hx 0
local notation "U"=> (u₀).atH
local notation "h!"=> H.atTopH
local notation "o"=> (u₀).links R h!
local notation "x₁"=> H.cu R d hx
local notation "s"=> (A.B.a.budget m)
local notation "φ"=> A.B.kin.alpha N m
local notation "V"=> A.B.kin.path N m
local notation "B'"=> A.B.a.clock.hatBeta m
local notation "Z"=> Song.posting s H.atTopH
local notation "O"=> Chi.canonical
local notation "F"=> Song.plusone h! o O φ
local notation "c"=> A.B.a.S.side m n
local notation "κ"=> Trio.base (Rain.lint R.target A m) (radiusB (B'))
local notation "z"=>2*κ
local notation "ν"=> Rain.tempe (A:=A) («Z»:=R.expense) (m:=m)
local notation "Ω"=> D.L (J)
local notation "i₀"=> A.B.a.clock.J m
local notation "L"=> Cash.armK (R.target J i₀) Ω (R.shape.μ J i₀) B' 0 (R.expense J i₀).degrees
local notation "R!"=> (A.B.a.clock.op m n)
local notation "S!"=> (A.B.a.S.oneStep m n).exact_size
local notation "t"=> archives R H d hx
-- Registry alignment. Shared perms real across strolls even in noncanonical representative. Here at &(pre-Filled). Derived not assumed; also quote minorant calculus fees.
variable (ζ:Signed) (v:Site (A.B.a.S.side m n))
local notation "S₀"=> A.B.a.clock.allowance m

def carry : ((K).read (x₁)).Moves ζ v:= by
    let a:= Whirl.tips h! s O o ζ v (d.maps _ x ζ ((R!).ratio.embed v)) H.k φ
    exact Whirl.pellet (hak _) s (Whirl.gales _ κ z _ (Guild.GleamV R H.W H.k (u₀).aisle) (t) ζ v a)
lemma carriedP : (carry R H d hx ζ v).ep=(carry R H d hy ζ v).ep:= by
    let π:=d.maps _ x ζ ((R!).ratio.embed v); let φ':=d.maps _ y ζ ((R!).ratio.embed v); let h := Whirl.tips_twin h! s O o ((H.oracle R d hy 0).links R h!) π φ' ⟨rfl,rfl,rfl,rfl,rfl⟩ (show Twins π φ' from ⟨(d.choice _ x ζ _).1.trans (d.choice _ y ζ _).1.symm, (d.choice _ x ζ _).2.trans (d.choice _ y ζ _).2.symm⟩) rfl H.k φ φ;
    unfold Voucher.carry;
    exact (Whirl.fuseTwins _ _ _ _ (Whirl.rotation _ _ _ _ _ _ _ _ _ _ _ _ _ h)).1 
include T
-- Absolute reach budget & stronger margin. Allow ε obtained earlier.
lemma earned (he:ε≤1/32): Meadow.Budget s (K).reg (x₁).logRead ((1/8:ℝ)*σ):= by
   let u':= u₀; obtain ⟨f,hf,hδ⟩:= fleetFund R H.hm T H.atTopH H.W (hp_width R H.hm P₀).1 H.hr _ o u'.related rfl u'.aisle u'.price
   have hσ:0 ≤ σ:=by unfold forecastE; exact mul_nonneg (credit_pos ..).le ((fundedP m B).1.le)
   exact ⟨f,fun i=>budget_loosen (hf i) (by linarith only [mul_le_mul_of_nonneg_right he hσ]),hδ⟩
-- export contraction into AFTER ANALYSIS PRICE (real post rep Ψ override will earn this)
omit T
variable (W': Paperwork R.shape ε u A.delay)
include W' H
lemma contractor {v':ℝ}(hv:0 ≤ v'):
    regularNeed G s (T').clip (T').width (T').paths 0 (Guild.tentPole A m ε*v') ≤ u/4 * (S₀) * v':= by
    have hf:=Rain.jersey (A:=A) (m:=m); have hz:= params_eq A.B.valid m; let K':= (X.p.profile i₀); let u':=Guild.tentPole A m ε; let i:= step_paid A.B.a m
    have h: (s).threshold ≤ 2*Pressure.fiery G B' Ω:= by rw [← H.atTopH.laws.data.funds.length_eq]; exact H.atTopH.laws.data.room.temperatures
    have ht: Time.Same (X.p.profile i₀) s:= ⟨hf.2.1,hf.1,hf.2.2.1⟩
    obtain ⟨hy,hk,hM⟩:= (W'.chord _ _ i _ (A.B.valid.pays m)|>.2.2).lifts s ht rfl rfl h
    have hu:= (hM _ (show _ from Boulevard.coupling A N m H.hm)).2 -- α
    have hu': Yard.priceE u' φ K'.width K'.paths K'.clip s G≤ u*S₀:= hu
    unfold K' Yard.priceE at hu'
    rw [Time.table G _ ht, Time.table G _ ht] at hu'; rw [hz,Time.table G _ ht]; simp only [abs_zero, mul_zero, zero_mul, add_zero, mul_one] at hu' ⊢
    have hV:= Time.base_nonneg G K'
    have hr:0≤ Time.top G K'*(|φ| *(s).threshold^3):= mul_nonneg hV.2 (mul_nonneg (abs_nonneg _) (pow_nonneg (s).threshold_pos.le _))
    unfold K' at hr; unfold u' at hu'; linarith only [mul_le_mul_of_nonneg_right hu' hv, mul_nonneg hr hv]
end YM.Juniper.Voucher
