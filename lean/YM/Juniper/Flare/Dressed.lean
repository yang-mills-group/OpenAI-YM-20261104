import YM.Juniper.Flare.Lumen
import YM.Juniper.Voucher.Story
/-!
 # Construction linkage. Pays all arm/prior-profile/pre-normalization costs
 on the core-proposed iteration, using the unified UV Finals/extensions.
 LOCAL obligations are on this one Family as displayed and survive emission.
 Later work generalize to full iteration over such supplies and discharge prerequisites.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
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
open Voucher Gauze Bright Spire Camp
variable {G:Gauge} {hG:G.Simple} {r:ℕ}
variable (P: Snip G) (E:Extras G) (U:Nursery G hG)
noncomputable def agenda : Extras G:= { Voucher.expertise P E with booster:=(Voucher.expertise P E|>.booster).and (rebateWind G) }
variable (h:Stock (Flare.agenda P E) U)
include h
lemma boarded : Stock (expertise P E) U ∧ Vent U.X.target U.P U.X.expense U.A.delay:= by obtain ⟨he,hv⟩:=h.boosted; exact ⟨{ h with boosted:=he},hv⟩
omit h

local notation "A"=> U.A
local notation "R"=> U.X
local notation "S"=> U.S
local notation "B!"=> U.A.B.a
variable {m N n:ℕ} (hm:m<N)
local notation "J"=> U.A.B.a.clock.J (m+1)
local notation "Y*"=> U.A.B.a.clock.hatBeta m
local notation "B"=> (U.A.B.a.budget m)
local notation "F*"=> U.family
local notation "F"=> (F*).path.rep N n m
local notation "F+"=> (F*).path.rep N n (m+1)
local notation "X!"=> (U.A.B.a.clock.op m n)
local notation "c*"=> U.A.B.a.S.side m n
local notation "D"=> U.X.shape
local notation "ε"=> U.S.grove.witness
-- notation defined before declaring m N? with quotPrecheck false OK?
local notation "H"=> (U.S.fits N n).charts m hm
local notation "W"=> (U.S.fits N n)
local notation "θ"=> (F+).beta
local notation "Ω"=> (F|>.beta)-(θ+ U.A.B.kin.alpha N m)
local notation "Vc"=> (U.A.B.a.S.side m n)
variable (hx:Cinch.wraps (U.A.B.a.clock.hatBeta m) (U.A.B.a.S.side m n))
-- on any x physical witness in reclosure covering evaluate plus predecessor costs

def Ready (m n N r: ℕ) (hm:m<N):= 2*Bright.home R m < (U.A.B.a.S.side m n).val ∧
    ∀ (d:Cham B! (m+1) n) (y:Valve (m+1) n B! d) (_hy: ‖place B! (m+1) n d y‖<rim),
     ∃ he: Reality B! (m+1) n d y ((F*).path.rep N n (m+1)|>.beta),
    -- certification local. no extra ∃ transport obligation.
      ∀ (T:Curtain G (U.A.B.a.S.side m n)) (T':∀ i:Stars,Curtain G (caves R m i)), Flare.Layout (n:=n) (m:=m) R T T' →
      ∀ ticket:TicketFor (m:=m) (n:=n) R y.val ((F*).path.rep N n (m+1)|>.beta) N, ∀ V₀:Pages R N m ((F*).path.rep N n (m+1)|>.beta),
        (∀ hc: 2*Bright.home R m < (U.A.B.a.S.side m n).val, CertificateP R ((U.S.fits N n).charts m hm) d he ticket V₀ hc) →
        Flare.Fixed R V₀ T' (powerUp r) → ∀ x:Valve (m+1) n B! d,∀ a:ℝ, ‖place B! (m+1) n d x‖<rim → (Dales.mount R N (m+1) n x.val ((F*).path.rep N n (m+1)|>.beta) a).eval=((F*).path.rep N n (m+1)).eval →
         Outlook R d (x:=x) (y:=y) (N:=N) («ε»:=ε) (C:=((F*).path.rep N n (m+1)|>.beta)) («Ω»:=((F*).path.rep N n m|>.beta) - (((F*).path.rep N n (m+1)|>.beta)+ U.A.B.kin.alpha N m)) (Ξ:=a) (r:=r) T
include hG h hm hx
lemma reached (hr:powerUp r≤J) : Flare.Ready U m n N r hm:= by
   obtain ⟨hB,h'⟩:= boarded P E U h; obtain ⟨hs,-,hg,hv,hχ,hH,hF,hW⟩:= Voucher.rotation P E U hB; have hc:=Bright.highEnough (m:=m) R hg n; refine ⟨hc, fun d y hy=>?_⟩
   have hxB:(↑(0:ℝ):ℂ)∈ Camp.Broad U.A.B.a:=by simp only [Complex.ofReal_zero]; exact Metric.mem_ball_self (Camp.flat_pos _)
   obtain ⟨he,hT⟩:= (W).acts (U.S.cart N n) (U.S.token N n) U.S.grove.coins hxB
   obtain ⟨hK,hP,hQ⟩:= Cinch.pristine R hG hm S 0 hxB (n:=n)
   let β:=θ; have hs (x:Valve (m+1) n B! d) (hx:‖place B! (m+1) n d x‖ < rim): Reality B! (m+1) n d x θ:=⟨hK,hx.le.trans (by norm_num [rim])⟩; refine ⟨hs y hy,?_⟩
   intro T T' ha tk f hf hφ x b hΘ hΩ
   have hP': Cinch.Pristine A N m (Time.forecastE B! m) θ Ω (X!|>.push θ (Dales.mount R N (m+1) n x.val θ b).eval):= by rw [hΩ]; exact hP
   exact Flare.lumen R H d (hs x hΘ) (hs y hy) tk f T T' (hf hc) ha U.S.grove.pledge U.S.grove.enabled hχ hg h' h.may_use h.highest hG hF hv hx ((W).rootc he hxB hT _ hm) P hH hr hφ hΘ hy hP'
omit hm hx
lemma paid (r:ℕ): ∀ᶠ m in atTop, ∀ N n (hm:m<N), Flare.Ready U m n N r hm:=by
   have he:= Cinch.kettle U.family hG; filter_upwards [he, (B!).fits.deep.eventually_ge_atTop (powerUp r)] with m hv hx N n hm; exact reached P E U h hm (hv n) (hx.trans ((B!).fits.mono (Nat.le_succ _)))
end YM.Juniper.Flare
