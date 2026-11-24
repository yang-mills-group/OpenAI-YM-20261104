import YM.Juniper.Voucher.Tokens
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
local notation "y'"=> (H.cu R d hy)
local notation "h₁"=> Time.forecastK A.B.a m R.scout C
-- New assembly funded by predicting REAL pure & mixed E, never replacing incurred K. This is on fully unrelated footprint at the SAME pre inoculation. Chosen is the sounded Craft of that MODEL; not hypothesizing transformation works on actual or composable approximations. Require FRAME panel geometry (not existential size tail outside stage). Can in particular use high Glow.
variable {p:ℕ} (v : Collection.Source G (A.B.a.S.side m n)) (P: Listing G (A.B.a.S.side m n))(f: Trio.Offer G (A.B.a.S.side m n))
structure Panel : Prop where
   posting : Meadow.Budget s P.reg v.logRead ((1/4:ℝ)*σ)
   slides : ∀ a i, ∃ a', EPerm P v a i a'
   projection (i:Config G (A.B.a.S.side m n)) : ((K).read y').additive s i=(P.read v).additive s i+θ*Fintype.card (Site (c))-tax f i
   worth : LightTax s p f W
-- consists of Maker.NLO E estim relative window, not occupying any position in original actual-H. Manufacture Space data across fees; Shape Authority (involvement of old family projection trusted exponential bridge).
local notation "A₁"=> package Z K P
local notation "q!"=> t+f
local notation "a'"=> stack F (x₁-y') v
local notation "A₂"=> lodge A₁ 0 p -- 0 soft
abbrev areaHull (p:ℕ) := Marlin.pluck s (lodge (package Z K P) 0 p)
abbrev plan (v' : ℕ):= poursP s (lodge A₁ 0 v') (bison a' 0 q!)
local notation "φ₀"=> areaHull R H P p
local notation "Π"=> plan R H d hx hy v P f p
variable {P v f}
include hx hy
set_option maxHeartbeats 700000 in
lemma moved (w:Panel R H d hy v P f (θ:=θ) (W:=W) (p:=p))(a:Signed) (i:Site (c)): Nonempty ((A₁).read (a') |>.Moves a i):=by
   let P':= Voucher.carry R H d hx a i; let p':= P'.ep; let X₀:= Voucher.carry R H d hy a i; obtain ⟨q,hq⟩:= w.slides a i
   have he:(Voucher.carry R H d hx a i).ep=(Voucher.carry R H d hy a i).ep := carriedP R H d hx hy a i
   let g:= carryPack p' q
   refine ⟨Voucher.underPack (X:=K) (x:=x₁-y') («Y»:=P) (y:=v) (p:= hazard R H d hx) Z ((Voucher.standing R H d hx).moves a i|>.some) (u:=g) ?_⟩
   refine stackP Z (π:=p') («φ»:=q) ?_ hq; refine EPerm.subtract (X:=K) (x:=x₁) («z»:=y') («s»:=a) (π:=p') (EPerm.fromM P') ?_; change EPerm K y' a i (Voucher.carry R H d hx a i).ep; rw [he]; exact EPerm.fromM X₀
omit hx
structure Windy (R:Factor A)(m:ℕ)(C b:ℝ)(p:ℕ)(n:ℕ) : Prop where
   ability : ∃ k δ:ℝ, Payments.Rates (A.B.a.budget m).B (Time.forecastK A.B.a m R.scout C) (Cash.armK (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) 0 (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).degrees) (Marlin.tithe p (Rain.tempe (A:=A) («Z»:=R.expense) (m:=m)+b) (A.B.a.budget m) δ) k ∧ ∀ i: Site (A.B.a.S.side m n),(coverNumber (A.B.a.budget m).B (neighbors p i):ℝ) ≤ δ
   mature : 2 * figure R m ≤ p
include T hx
set_option maxHeartbeats 700000 in
lemma shown (he:ε ≤1/32)(w:Panel R H d hy v P f (θ:=θ) (W:=W) (p:=p)) (ht:Windy R m C W p n) : Collection.Local φ₀ s Π ((1/2:ℝ)*σ) h₁ ∧
    ∀ b:ℝ, ∃ τ:ℝ, planting (A:=A) (N:=N) (C:=C) (φ₀) Π τ=(R!).push C (mount R N (m+1) n x.val C b).eval:= by
   let K':= a'; let Ω':=A₁
   obtain ⟨d',hp,hδ⟩:=ht.ability -- wrong shape
   have hT:=standing R H d hx; have hx':=earned R T H d hx he; have hy':=earned R T H d hy he
   have hs:= (LightTax.more (g:= t) («t»:=f) (LightTax.reaches hT.wear ht.mature) w.worth).1
   have hw:=hT.ordinary
   obtain ⟨g,hg,hV⟩:=hT.invested
   have hk (a i):Nonempty (((A₁).read a').Moves a i):= moved R H d hx hy w a i
   have hc:= stakes s A₁ 0 p K' 0 (t+f) (show ((A₁).read K').ForcedFamily s from ⟨hw.sym,hw.symtest,hw.meas,hw.meas_test,hw.reads,hw.reads_test,hw.permit⟩) hk hδ.1 hg hV hs.tidy (fun i Vx h hS=> h (hs.failed i Vx hS)) hs.bills hδ.2 (le_refl _)
   have hz: Meadow.Budget s (A₁).reg (a').logRead ((1/2:ℝ)*σ):= by
     have ht:= toll_sub hx' hy'; rw [show (1/2:ℝ)*σ=((1/8:ℝ)*σ+1/8*σ)+(1/4:ℝ)*σ by ring]; exact payroll_pack Z ht w.posting
   refine ⟨Marlin.sous hc ?_ (fun a i=> Marlin.reeds _ _ _ _ _ _ _ _ (hk a i|>.some)),?_⟩
   · have hv: Meadow.Budget s (leap («c»:=c) 0) (0:Offer G c) 0:= by
        refine ⟨fun _=>0,fun i=>?_,fun i=> ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩⟩; simp [SumBudget]
     simpa only [mul_zero,add_zero] using! Marlin.reg_bison A₁ 0 p a' 0 (t+f) hz hv
   intro b; obtain ⟨a,ha⟩:=hT.present b; rw [← ha]; refine ⟨a-(dates R H d hx+θ),funext fun i=> Eq.symm (finality _ Ω' 0 p K' (t+f) i _ a _ (dates R H d hx+θ) (V) (T').clip Z F rfl rfl hz hc ?_)⟩
   rw [Voucher.taxes f i t|>.1] -- args check
   have hq:= additive_pack Z i (p:=F) («x»:=x₁-y') (toll_sub hx' hy') w.posting
   rw [hT.visible i, show (Ω'.read K').additive s i=_ from hq, additive_sub i («B»:=s) hx' hy']
   rw [w.projection]; ring
end YM.Juniper.Voucher
