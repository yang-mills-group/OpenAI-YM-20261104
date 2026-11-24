import YM.Juniper.Voucher.Pole
import YM.Juniper.Voucher.Bundle
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
-- Turnout. Same-H derivation output tags/projection binding. For ANY mount at one epoch. May use arbitrary scalar; representation true with mild shifts. Cost on REAL Hard BEFORE final folding +2.
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

abbrev hazard: Collection.Source G (A.B.a.S.side m n):= F
abbrev marquis : Listing G (A.B.a.S.side m n):= Z
abbrev dates := Meadow.barony U O H.k φ 0 1
abbrev archives := Guild.SightV R H.atTopH H.W H.k U o (u₀).aisle
abbrev figure (R:Factor A) (m:ℕ):=Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))
local notation "t"=> archives R H d hx
abbrev planting (P' : Listing G (A.B.a.S.side m n))(f:Collection.Source G (A.B.a.S.side m n))(τ:ℝ):= Collection.earlyValue P' V (T').clip s f C τ φ
structure Standing : Prop where
  sufficient : ∃ θ:ℝ,Meadow.Budget s (Z).reg (F).logRead θ -- naming clash notation binder use different
  moves : ∀ a i, Nonempty (((Z).read (F)).Moves a i)
  ordinary : ((Z).read (F)).ForcedFamily s
  invested : ∃ f:ℕ→ℝ, (∀ i,0≤ f i ∧ ∀ u, ‖(F).hardRead i u‖≤ f i) ∧ Ac.Hit (fun i=>((Z).hard i).support) (s).B f ((s).supportExponent+1+1) L
  wear : LightTax s z (t) ν
  visible (Xg:Config G (A.B.a.S.side m n)): ((Z).read F).additive s Xg=((K).read x₁).additive s Xg+ dates R H d hx*Fintype.card (Site (c))-tax t Xg
  present (a:ℝ) : ∃ τ:ℝ, planting (A:=A) (N:=N) (C:=C) Z F τ=(R!).push C (Dales.mount R N (m+1) n x.val C a).eval
-- `variable...{u}`. different P Log depending scalar; use Guild.Lat via proof exact WRAP identity? For scalar arbitrary, RAW PlusOne may depend via Price Guide choice. relation plusone(H±): prove scalar multiplies constant independent kernel using mount.eval push.
include hx H
set_option maxHeartbeats 400000 in
lemma standing : Voucher.Standing R H d hx:= by
    let F':=u₀; let X₀:=H.atTopH; let Y':=Z; let p:=o
    let YD:= Classical.choice (Tree.select (R!).ratio (R!).patch.odd_side)
    have hv:= R.pledging; have he:= hv.agenda _ _ (step_paid B m)|>.1; have ht:= hp_width R H.hm P₀
    obtain ⟨hV,hK⟩:= Boulevard.lays R.shape A (S!) p R.inn.chip H.hm hv.jewels hv.conducts.full he ht.1 F'.price YD
    obtain ⟨f,ha,hb⟩:= hV.cheap
    let P':=raiser s
    have hh': (raiser s).supportExponent+1 ≤ (R.expense (J) i₀).earn:= by change (s).supportExponent+1+1≤ _; rw [(Rain.jersey (A:=A) (m:=m)).2.2.1]; linarith
    refine ⟨⟨_,f,hb,fun i=> ⟨hV.smooth i,ha i⟩⟩,hV.transforms,hV.family,chargesOut (raiser s) X₀ p O F'.price rfl hh',?_,?_,?_⟩
    · have hp(i):=Guild.knighthood R H.hm h! H.W H.k F'.atH p rfl F'.related F'.price F'.aisle rfl i
      exact ⟨fun i=> (hp i).1,fun i u hh=> by_contra (fun he=>(hp i).2.1 _ he hh),fun i u=> (hp i).2.2 u⟩
    · intro X'; let k:=H.k; let f':= Guild.GleamV R H.W k F'.aisle; let y:=Guild.Tips R X₀ k F'.atH p; let s':=dates R H d hx; let W₀:=bison y f' t
      have hT := H.hr.helm _ _ p F'.related rfl F'.aisle F'.price
      have hp:= Marlin.cruiseV s (Beam.marquee X₀ (s)) κ z y f' (t) X' (R:=Z) F (A.B.kin.path N m) (T').clip C 0 s' hT (fun x=> Trio.levy s p φ k (Rain.screens R.target A m) (κ) (H.W.offers k ⟨C,hx.1⟩) x _ _ hV) hV.transforms (fun a i=> Beam.moves _ _ O _ a i _) -- args?
      unfold RG.Rep.exponent at hp; dsimp only [Collection.frozen] at hp
      rw [Voucher.exactTax] at hp; change _-_-_ = _ -_ - ((K).read (x₁)).additive s _ + tax (t) X' at hp; linarith only [hp]
    intro a; let w:= (Dales.mount R N (m+1) n x.val C 0); let u:= weighty F'.atH O YD
    -- change vacuum on both sides
    let x' := a*(Fintype.card (Site (A.B.a.S.side (m+1) n)):ℝ)
    have hX (i) : (Dales.mount R N (m+1) n x.val C a).eval i = Real.exp x'*w.eval i:= by
       have hp: (Dales.mount R N (m+1) n x.val C a).exponent i=x'+w.exponent i:= by unfold Rep.exponent w x'; dsimp only [Dales.mount]; ring
       rw [Rep.eval,Rep.eval, hp, Real.exp_add, mul_assoc]; rfl
    have ha : (R!).push C ((Dales.mount R N (m+1) n x.val C a).eval)= Real.exp x' • (R!).push C w.eval:= by
       funext i; simp only [StepData.push,hX,Pi.smul_apply,smul_eq_mul,mul_left_comm (StepData.density ..) (Real.exp x'), integral_const_mul]
    let v:= (Fintype.card (Site c):ℝ); refine ⟨u+x'/v,?_⟩; rw [ha]
    have hh: (R!).push C w.eval= planting (A:=A) (N:=N) (C:=C) Z F u:= funext hK
    rw [hh]
    funext i; unfold planting Collection.earlyValue Rep.eval; dsimp only [Pi.smul_apply,smul_eq_mul];
    have hx : (Collection.frozen Z V (T').clip s F C (u+x'/v)).exponent i=x'+(Collection.frozen Z V (T').clip s F C u).exponent i:= by
       have hv:0 < v:= by unfold v; positivity
       unfold Rep.exponent; dsimp only [Collection.frozen]; rw [add_mul, show x'/v * Fintype.card (Site c) = _ from div_mul_cancel₀ x' hv.ne']; ring

    rw [hx,Real.exp_add]; unfold Collection.frozen; ring
end YM.Juniper.Voucher
