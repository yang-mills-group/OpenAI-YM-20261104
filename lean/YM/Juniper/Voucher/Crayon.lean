import YM.Juniper.Voucher.Paint
import YM.Juniper.Voucher.Strike
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
variable {r:ℕ} (P:Gauze.Snip G) (S:Gauze.Lustrous R N m)
open Gauze Averaging
local notation "Q'"=> (betaK G Ω (powerUp r) J t₀)
local notation "P'"=> painting R P S C (powerUp r) («c»:=c)
local notation "p₀"=> typed P'
local notation "b"=> (t₀^r)⁻¹ -- b macro shadows previous b
-- Margin after announcing `powerUp r` inputs; ANY Purchaser; not requiring ε or specific operator, applies cp7 with this rank. So contraction cost of step on pure E reference earned with small normal magnitude entering next step with SAME actual K.
variable (hp:Extol D R.target A.delay) (hr:powerUp r≤A.B.a.clock.J (m+1))
include hp
lemma striking : PricedForce t₀ D R.target J i₀:= hp.paid _ _ (step_paid _ _) _ (A.B.valid.pays m)
include hr
lemma tapP : Q' ≤ (rim*b)*σ ∧ σ/(4*t₀^J) ≤ (rim*b)*σ:= by
    have he:0<σ:= mul_pos (Time.credit_pos ..) (fundedP m B).1
    obtain ⟨ht,hΘ⟩:= (striking R (m:=m) hp).2 r hr
    refine ⟨?_,?_⟩
    · unfold forecastE; rw [params_eq A.B.valid]; exact ht
    rw [div_eq_mul_inv,mul_comm]; exact mul_le_mul_of_nonneg_right hΘ he.le
local notation "D'"=> turnFee s * ((Y^deep J+Y^deep J)+(Y^deep J))
omit hr
include hx h hd
lemma brightBudget (hs:Fidelity R P S! S Z' U k r) : Meadow.Budget s (Z₀).reg (b₀).logRead (rim*σ):= by
    have hy: D' + turnFee s * FareG R m ≤ rim*σ := by
       have he:= (striking R hp (m:=m)).1; refine le_trans (add_le_add (Bright.tollK R h hd (m:=m)) le_rfl) ?_; dsimp only [FareG,forecastE]; have ht:=Rain.jersey (A:=A) (m:=m); rw [params_eq A.B.valid,ht.2.2.2,show preExponent s= Trio.stout (X.p.profile i₀) from (by unfold preExponent Trio.stout; rw [ht.2.2.1])]; exact he
    let p' := Bright.chest R S! U (mast J) k; obtain ⟨g,hG,hg⟩:= hs.shone.shaved.cheap; exact Bright.pays_less hy (Marlin.reg_bison (posting s U) x₃ (2*x₃) p' _ f (show Meadow.Budget s (posting s U).reg p'.logRead D' from ⟨g,hg,fun i=>⟨hs.shone.shaved.smooth i,hG i⟩⟩) hs.shone.portion)
omit hd hp h hx in
lemma noble : 0< b ∧ b ≤ 1:=by have he:= A.B.a.fits.delayed m; exact ⟨by positivity,inv_le_one_of_one_le₀ (one_le_pow₀ he.le)⟩
include hr
lemma minted (hs:Fidelity R P S! S Z' U k (powerUp r)): Meadow.Budget s (Z₀).reg (p₀).logRead ((2*rim)*σ):= by
   have ht : b ≤ 1:= (noble (A:=A) (m:=m) (r:=r)).2; have ha : 0≤ σ:= mul_nonneg (Time.credit_pos ..|>.le) (fundedP m B|>.1.le); have he:= Voucher.toll_sub (Voucher.brightBudget R H d hx hd Z' h P S hp hs) hs.earlyE; rw [sub_sub_cancel] at he; refine Bright.pays_less ?_ he; have hT: Q' ≤ rim*σ:= le_trans ((tapP R hp hr).1) (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by norm_num [rim]) ht) ha); exact le_trans (add_le_add le_rfl hT) (le_of_eq (by ring))
end YM.Juniper.Voucher
