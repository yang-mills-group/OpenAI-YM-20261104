import YM.Juniper.Voucher.Inbreed
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
open Bright
variable {k:ℕ}(hg: Moat D (E:=R.expense) A.delay) (hd : ∀ i j:ℕ,(R.expense i j).wanting= -(7/16:ℝ)) (hh β:ℝ)
local notation "t₀"=> A.B.a.clock.hatBeta m
local notation "H₀"=> Bright.miner R m
local notation "V₁"=> A.B.a.S.side (m+1) n
variable (Z' : Guidebook R N m C) (h : Gems D R.shape A.post A.delay) (hc:2*Bright.home R m < (A.B.a.S.side m n).val)
local notation "x₃"=> Bright.home R m
local notation "x₄"=> Trio.lossFee G Ω (R.expense J i₀).wanting H₀ (X.p.profile i₀) t₀
local notation "f"=> Bright.lamps R (S!) Z' U k
local notation "Z₀"=> Bright.scaledP R (S!) U
local notation "b₀"=> Bright.score R (S!) Z' U k
include hc
lemma glowing : LightTax s (2*x₃) f x₄:= by
   let v:= U; let F':=u₀; let P':= F'.price; let u:= Bright.paragon R k Z' («c»:=c)
   let q:= x₃; let w i := stones R Z' i k; let T₀:= Meadow.studio H₀ (radiusB t₀); let d:= (X.p.profile i₀)
   obtain ⟨hj,hp,hδ,hE,hh,hv,hV⟩ := Bright.climb (b:=Rain.lint R.target A m) (n:=mast J) (j:=radiusB t₀) (s).B_pos; have hi : 4*T₀+16 ≤ (c).val:= by unfold T₀; have hz:= (hV c hc).1; unfold Bright.home Bright.miner Rain.lint at *; omega -- possible cycles huge
   let π:= lighted R m; let F₁:= (Classical.choice (Tree.select (R!).ratio (R!).patch.odd_side)); obtain ⟨hg',hv⟩:= Bright.roomy R S! H.hm U P' F₁
   have hk:= Bright.mirrorWarp R S! H.hm (show C∈ Rain.lands A m from hx.1) Z' U rfl rfl rfl P' hc k
   refine ⟨Bright.trimmedCost q rfl hδ hp hE hh le_rfl hg' (fun i j=> Bright.sudden R H.hm Z' i j k),fun a g hv=> Bright.scrub q hj hi rfl hδ hp hE hh le_rfl hk hv, ?_⟩
   intro i U'; rw [Trio.lossFee]; refine le_trans (Bright.bought q rfl hδ hp hh hg' (fun i X' hh j=> (Bright.mainDoor R H.hm (sews R m i) (Z'.pages i) (Z'.sells i) k j).2 X' hh) i U') ?_; unfold Trio.heat Bright.breach; rw [← PriceCompiler.beta_eq A.B.valid, ←(Rain.jersey (A:=A) (m:=m)).2.2.2] -- B? rfl?
omit hc
local notation "D'"=> turnFee s * ((Y^deep J+Y^deep J)+(Y^deep J))
include hg h hd in
lemma scoop' : D' + turnFee s*FareG R m ≤(1/4:ℝ)*σ:=by
  apply le_trans (add_le_add (Bright.tollK R h hd (m:=m)) le_rfl); dsimp only [FareG, forecastE]; have ht:= Rain.jersey (A:=A) (m:=m); rw [params_eq A.B.valid,ht.2.2.2,show preExponent s= Trio.stout (X.p.profile i₀) from by unfold stout preExponent; rw [ht.2.2.1] ]; exact (hg.veil _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) (hd ..)).2
local notation "v₀"=> Bright.living O U (mast J) (flora U k) (radiusB B') k φ
local notation "K'"=> (v₀ 0 1)
variable (hp: Bright.CloseG R (A.B.a.S.oneStep m n).exact_size Z' (H.oracle R d hx 0).atH k)  -- hp Yap
include hp
local notation "θ₁"=> K'-dates R H d hx
private lemma caption (u: Config G (A.B.a.S.side m n)): ((Z).read F).additive s u=((Z₀).read b₀).additive s u+K'*Fintype.card (Site c)-Voucher.tax f u:= by
   refine Eq.trans (inCommon R H d hx u) ?_; let f₀:= Bright.chest R (S!) U (mast J) k; let S':= Song.posting s U; let x₁':= Bright.paragon R k Z' («c»:=c)
   obtain ⟨F₀,hA,hB⟩:= hp.shaved.cheap
   let b:= Song.plusone U (Bright.blank U) O φ
   obtain ⟨hf,_⟩:=Bright.roomy R (S!) H.hm U (u₀).price (Classical.choice (Tree.select (R!).ratio (R!).patch.odd_side))
   have hk := Marlin.cruiseV s S' x₃ (2*x₃) f₀ x₁' f u (R:=S') b V (T').clip C 0 K' (show Meadow.Budget s S'.reg f₀.logRead D' from ⟨F₀,hB,fun i=>⟨hp.shaved.smooth i,hA i⟩⟩) (fun v=> Bright.arranged x₃ (lighted R m) _ hf («V»:=v)) hf.transforms hp.shaved.transforms
   unfold RG.Rep.exponent at hk; dsimp only [Collection.frozen] at hk; rw [Voucher.exactTax] at hk; change 0*Fintype.card (Site (c)) - _ - (S'.read b).additive s u=(0-K')*Fintype.card (Site c) - _ - ((Z₀).read b₀).additive s u+tax f u at hk; change (S'.read b).additive s u=_; linarith only [hk]
include hg h hc hd in
lemma allocate : Panel R H d hx b₀ Z₀ (f-t) (θ:=θ₁) (W:=Need J i₀ t₀ D R.expense) (p:=2*x₃):= by
   refine ⟨?_,fun a i=> ⟨(hp.bought.transforms a i).some.ep,EPerm.fromM (X:=Z₀) (x:=b₀) (hp.bought.transforms a i).some⟩,fun i=> ?_, (LightTax.more («t»:= t) (glowing R H d hx Z' hc) (LightTax.reaches (standing R H d hx|>.wear) (mul_le_mul_right (bigger R) _))).2⟩
   · obtain ⟨g,hg',hG⟩:= hp.shaved.cheap; let v:= Bright.chest R S! U (mast J) k
     exact Bright.pays_less (scoop' R hg hd h) (Marlin.reg_bison (posting s U) x₃ (2*x₃) v (Bright.paragon R k Z') f (show Meadow.Budget s (posting s U).reg v.logRead D' from ⟨g,hG,fun i=>⟨hp.shaved.smooth i,hg' i⟩⟩) hp.portion)
   have hh:= (standing R H d hx).visible i; have he:= caption R H d hx Z' hp i; rw [Voucher.taxes t i f|>.2]; linarith only [hh,he]
end YM.Juniper.Voucher
