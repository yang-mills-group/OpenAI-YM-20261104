import YM.Juniper.Bright.Cohort
/-! # Alignment of all arities; interpolation Ledger -> ANY TWO physical periods
 Requires exact Glyph input-absence lift for all Shelf residents (applies ANY
 R in `Light`), large finite volume admission given; too big for cost analysis
 applied AFTER. stamping budgets later.
 This upgrades `Slide.Echo.parses` beyond power3 preserving Atlas device through
 large support exponent bought. Authenticates practice receipts, not assuming
 any PT analytic localization.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open Further.PhysicalPeriodLimitF933 Macrame Shelf Stellar Meadow
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f c' f' L : Side} {P:Teller G}
      {W μ x C C' s:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W}
      {j n k w l:ℕ}
section lift
variable {g:Patch}{K:KernelChoices} {M:ℕ}{c f C₀ F:Side} {hs : f.val=c.val*g.L.val} {hh : F.val=C₀.val*g.L.val}
local notation "S"=> stepped K hs
local notation "Y"=> stepped K hh
variable {T:Tube G (stepped K hs)} {T': Tube G (stepped K hh)} {R: Rep G f} {R': Rep G F}
variable (hC:C₀.val=c.val*M) (he:2≤c.val)
local notation "V"=> Lace.project (h:=hs) (H:=hh) hC he
local notation "π"=> (V).low.cut
variable (I':Cash W x μ L Q o C' T' R') (I:Cash W x μ L Q o C T R) (hp:R'.path=R.path) (n k:ℕ)
local notation "B"=> Mint.width Q.halo (radiusB x) (radiusB x)
local notation "ζ"=> terrace B k

variable (h: T'= Deck.re T)(ha:R'.p=R.p)(hx:R'.beta=R.beta)
   {C₁ C₂ d d' z z' t t' A A' u u' r r' v v' q q':ℝ}{b ℓ i j:ℕ}
   (N : Captain I b C₁ d z t A u r v q ℓ χ) (N' : Captain I' j C₂ d' z' t' A' u' r' v' q' i χ)
include N N' hC he hp h ha hx
lemma culture (hc : 2*(2*(ζ+B)) < c.val) (γ:ℝ)(p:ℕ)(z:Config G c)(hz:RG.flags (Pressure.temp x) z=∅) (a: Site C₀) : -- shadow bad; replace
    Bright.living χ I' k (Bright.flora I' n) p n γ a ((V).low.links z)= Bright.living χ I k (Bright.flora I n) p n γ (π a) z:= by
   let θ (θ:Seat c):= Bright.Ledger k (Bright.flora I n) χ ((spin θ).symm (π a)) (θ.view z) + Meadow.garner T.down T.low R.beta γ p n ((spin θ).symm (π a)) (θ.view z)
   unfold Bright.living Meadow.atlas; change likely _= likely θ; rw [← revolving hC θ]; apply congrArg (fun g:Seat C₀→ℝ=> likely g); funext e
   have ht:e.view ((V).low.links z)=(V).low.links ((pinch hC e).view z):= estuary hC z e
   dsimp only [θ,Pi.add_apply]; rw [ht,← show π ((spin e).symm a)=(spin (pinch hC e)).symm (π a) from inverts hC e a]
   apply congr_arg₂ HAdd.hAdd; swap; · rw [hx]; subst T'; exact garner_pack hC ..
   exact Bright.vogue hC he I' I hp _ n k h ha hx N N' ((pinch hC e).view z) (Meadow.covers_field (pinch hC e) z hz) hc
end lift
section pair
variable {X:Metals G} {D:Rolls X.p} {c f C' F:Side} {z j m n N:ℕ}
variable {C : Targets X.p X.K} {Z : Expenses C} {p : Return.Wages} {v : ℕ→ℝ} (R : PhysicalNext.Repeat.Register D Z p v) (A : Alloy X D)
local notation "α" => A.B.a
local notation "J" => A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "x" => A.B.a.clock.hatBeta m
local notation "θ" => Pressure.temp (A.B.a.clock.hatBeta m)
local notation "𝒯" => Pane.orchestra A N
local notation "B" => (A.B.a.budget m)
local notation "e" => (Z J I)
local notation "P'" => (C J I)
local notation "β" => (A.B.a.budget (m+1))
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
local notation "U_" => Mint.width (C J I|>.halo) (radiusB x) (radiusB x)
local notation "Z₀" => terrace U_ k
variable (H : f.val=c.val*(A.B.a.S.block m).val) (H' : F.val=C'.val*(A.B.a.S.block m).val)
    {u : RG.Rep G f} {w : RG.Rep G F}
   (Y : Chartlet R A N m H u) (K: Chartlet R A N m H' w)
    (h : w.path=u.path) (hb:w.p=u.p) (hw: w.path=A.B.kin.path N (m+1)) (hu:w.p=A.B.a.budget (m+1))
   (het : u.beta∈ RG.Shoot.band A.B.a (m+1)) (hβ:w.beta=u.beta)
    (ht : Pollened D R A.delay) (hq : v≤ A.delay.betaEntry)
    (hm: m < N) (hT:Tenement R A.delay) (hr : ∀ N m n,m≤N→ Bid.Sworn (A.B.M.H N m) n G)
   (hG : (X.p.profile (A.B.a.clock.J m)).supportExponent+3≤ (Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).earn)
    (hp: WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
include h hb hw hu het hβ ht hq hm hT hr hG hp
lemma aligned (k:ℕ) (hl : Shelf.terrace (Mint.width (C J I|>.halo) (radiusB x) (radiusB x)) k ≤ j)(hC0:2*radiusB x ≤ j) (hc : 4*(j+ U_)+16≤ c.val) (hC : 4*(j+U_)+16≤ C'.val) (n:ℕ) : Trio.Compatible (Bright.living O Y k (Bright.flora Y n) (radiusB x) n γ) (Bright.living O K k (Bright.flora K n) (radiusB x) n γ) B j:=by
   intro i i' U V hU hV hY
   let E:=c*C'; let F:= E*((α).S.block m)
   have hM:F.val=E.val*(A.B.a.S.block m).val:= rfl; have hN:E.val=c.val*C'.val:=rfl; have hN' : E.val=C'.val*c.val:=mul_comm ..
   have h':c.val≤ E.val:= Nat.le_mul_of_pos_right _ C'.pos
   let u1:=Lattice.translate i U; let u2:=Lattice.translate i' V; let c1:=Pane.virgin (𝒯 hM) (β) u.beta
   obtain ⟨I₁,h₁⟩:= Pane.affords A N hM hm (Y.laws.data.room.buys.trans h') R hq hr het
   have hv := hT J x (A.B.valid.pays m) I (step_paid _ m); let Χ:=Bright.flora I₁ n
   obtain ⟨F₀⟩:= Tree.select (panel A m hM).ratio (panel A m hM).patch.odd_side
   have hp' := (lays R A hM (Bright.blank _) ht hm hT hr hG hp h₁ F₀).1; have hK:= Bright.seen (B) rfl Χ hl hC0 (0:Site E) hp' (m:=n) -- order checks
   obtain ⟨C₁,t,r,b,L0,B0,s,v,u',z,b',⟨N₀,hF⟩,hp,hX⟩:= hv.2 _ _ _ _ (Y.laws.data.funds) (Pane.ovation A N H hm hr) _ Y
   obtain ⟨C₂,t,r,b,L0,B0,s,v,u',z,b',⟨N₁,hF⟩,hp,hX⟩:= hv.2 _ _ _ _ (I₁.laws.data.funds) (Pane.ovation A N hM hm hr) _ I₁
   obtain ⟨C₃,t,r,b,L0,B0,s,v,u',z,b',⟨N₂,hF⟩,hp,hX⟩:= hv.2 _ _ _ _ (K.laws.data.funds) (Pane.ovation A N H' hm hr) _ K
   let V1:= (Macrame.normal (divides hN) hN).links u1; let V2:= (Macrame.normal (divides hN') hN').links u2
   have hN1 := Bright.culture (T:= (𝒯 H)) (T':= (𝒯 hM)) hN (show 2≤c.val from by omega) I₁ Y (hw.symm.trans h) n k rfl (hu.symm.trans hb) rfl N₀ N₁ (show _ from by omega) γ ((B).B) u1 (by unfold u1; rw [←pull_one]; exact Pane.tranquility U hU ..) 0 -- notation
   have hN2:=Bright.culture (T:= (𝒯 H')) (T':= (𝒯 hM)) hN' (show 2≤C'.val from by omega) I₁ K hw.symm n k rfl hu.symm hβ.symm N₂ N₁ (show _ from by omega) γ ((B).B) u2 (by unfold u2; rw [←pull_one]; exact Pane.tranquility V hV ..) 0
   have hh  : Bright.living O I₁ k Χ ((B).B) n γ 0 V1=Bright.living O I₁ k Χ ((B).B) n γ 0 V2:= by
      apply hK.sites _ _ (readNear 0 (show 2*(j+1) < E.val from by omega) ?_)
      unfold V1 V2 u1 u2; rw [Slide.rolls,Slide.rolls,map_zero,map_zero,increases,increases]; exact hY
   let q:=Bright.living O Y k (Bright.flora Y n) (radiusB x) n γ; let q':= Bright.living O K k (Bright.flora K n) (radiusB x) n γ
   change Bright.living O I₁ k Χ ((B).B) n γ 0 V1=q ((splitter (divides hN)) 0) u1 at hN1
   change Bright.living O I₁ k Χ ((B).B) n γ 0 V2=q' ((splitter (divides hN')) 0) u2 at hN2
   rw [map_zero] at hN1 hN2; refine (Eq.trans ?_ hN1.symm).trans (((hh).trans hN2).trans ?_)
   · unfold u1; rw [← pull_one]; have hh := ((mirrors γ O _ B (Bright.flora Y n) k n) 0 1 i U).symm; simp only [Lattice.affine,Signed.act_zero, zero_add] at hh; exact hh
   unfold u2; rw [← pull_one]; have hh := ((mirrors γ O _ B (Bright.flora K n) k n) 0 1 i' V); simp only [Lattice.affine,Signed.act_zero, zero_add] at hh; exact hh
end pair
end YM.Juniper.Bright
