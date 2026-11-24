import YM.Juniper.Flare.Candles
import YM.Juniper.Bright.Banner
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open Further.PhysicalPeriodLimitF933 Macrame Stellar Meadow
open Bright Shelf
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f c' f' L : Side} {P:Teller G}
      {W μ x C C' s:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W}
      {j n k w l:ℕ}
section lift
variable {g:Patch}{K:KernelChoices} {M:ℕ}{C₀ F:Side} {hs : f.val=c.val*g.L.val} {hh : F.val=C₀.val*g.L.val}
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
   {U:Tape (decreed hs) R (radiusB x) Q.halo}{U':Tape (decreed hh) R' (radiusB x) Q.halo}
include N N' hC he hp h ha hx
-- apply to pair of laps. Generalizes Bright.culture for MIXED Era. No bcov in orientation choices assumed.
lemma combine (u : Volume (V) U' U n) (hc : 2*(2*(ζ+B)) < c.val) (γ:ℝ)(p:ℕ)(z:Config G c)(hz:RG.flags (Pressure.temp x) z=∅) (a: Site C₀) :
    Bright.living χ I' k (portal I' U' n) p n γ a ((V).low.links z)= Bright.living χ I k (portal I U n) p n γ (π a) z:= by
   let θ (θ:Seat c):= Bright.Ledger k (portal I U n) χ ((spin θ).symm (π a)) (θ.view z) + Meadow.garner T.down T.low R.beta γ p n ((spin θ).symm (π a)) (θ.view z)
   unfold Bright.living Meadow.atlas; change likely _= likely θ; rw [← revolving hC θ]; apply congrArg (fun g:Seat C₀→ℝ=> likely g); funext e
   have ht:e.view ((V).low.links z)=(V).low.links ((pinch hC e).view z):= estuary hC z e
   dsimp only [θ,Pi.add_apply]; rw [ht,← show π ((spin e).symm a)=(spin (pinch hC e)).symm (π a) from inverts hC e a]
   apply congr_arg₂ HAdd.hAdd; swap; · rw [hx]; subst T'; exact garner_pack hC ..
   exact illuminated I I' u hp k _ N N' hc h ha hx ((pinch hC e).view z) (Meadow.covers_field (pinch hC e) z hz)
end lift
section pair
variable {X:Metals G} {D:Rolls X.p} {c f c' f':Side} {z j m n N:ℕ}
-- local-lens analysis can consume any implementation for the common covering orbit. Determine from model templates; no estimate on regulator is lifted to them.
variable {A : Alloy X D} (R: Roost.Factor A) (hp:f.val=c.val*(A.B.a.S.block m).val)
   {β:ℝ}
local notation "B"=> (A.B.a.budget m)
local notation "B₀"=> (A.B.a.budget (m+1))
local notation "x"=> A.B.a.clock.hatBeta m
local notation "y"=> A.B.a.clock.hatBeta (m+1)
local notation "U"=> orchestra A N hp
local notation "J"=> A.B.a.clock.J (m+1)
local notation "B'"=> A.B.a.clock.J m
local notation "α"=> A.B.kin.alpha N m
local notation "Z"=> A.B.kin.path N (m+1)
local notation "O"=> Chi.canonical
local notation "k"=> mast J
local notation "Ψ"=> R.target J B'
local notation "W"=> Mint.width (Ψ).halo (radiusB x) (radiusB x)
local notation "r"=> Meadow.studio (Bright.miner R m) (radiusB x) -- miner in Banner
local notation "λ'"=> (X.p.profile B')
-- Lens consists of INPUT (addresses plus valid Works) not any estimated data. Affordability is required of the lifts
abbrev tapeFor (u:RG.Rep G f):= Tape (Pane.panel A m hp).ratio u (radiusB x) (Ψ).halo
structure Lens (N:ℕ) (u: RG.Rep G f)(β: ℝ) where
   snap : u.path=A.B.kin.path N (m+1)
   thresh : u.p=A.B.a.budget (m+1)
   drift : u.beta=β
   snapClip : u.clip=(A.B.a.params (m+1)).clip
   tape : Flare.tapeFor R hp u
   chart : Chartlet R.shape A N m hp u
   stamp : SeekR R.shape A N m hp chart
variable {u:RG.Rep G f}(L₀:Lens R hp N u β)
def stage (n:ℕ):= living O L₀.chart k (portal L₀.chart L₀.tape n) (radiusB x) n α
noncomputable def chest (n:ℕ):= leftOver (Bright.selection (portal L₀.chart L₀.tape n) k (radiusB x) n) α O
local notation "F"=> Flare.stage R hp L₀
local notation "Ξ"=> turnFee B * ( y^ (R.expense J B').wanting + y^ (-(7/16):ℝ))

-- Compat vars
variable (hp': f'.val=c'.val*(A.B.a.S.block m).val) {u':RG.Rep G f'} (L₁:Lens R hp' N u' β)
-- require both ability to lift pair & instantiate common product cover lens. No OUTput estimates at those volumes. They SHOULD follow from small primitive models from Input `E.Canister`. Producer soon.
local notation "τ"=> Flare.stage R hp' L₁
abbrev Chairs (R':Roost.Factor A)(m:ℕ)(c:Side) :=
    let w:= (R'.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo; let Bk:= radiusB (A.B.a.clock.hatBeta m)
    4*(Meadow.studio (Bright.miner R' m) Bk + Mint.width w Bk Bk)+16≤ c.val
lemma enoughC (h:Chairs R m c) : 2 ≤ c.val:= by dsimp only [Chairs] at h; omega
-- no assertion the E chart tape is natural over EVERY cover. require only at these. Later producer with pristine ≤ on tape.
def Aligned (hc : Chairs R m c) (hc' : Chairs R m c') (n:ℕ):Prop :=
    let I:=c*c'; let f:= I * (A.B.a.S.block m)
    let H:f.val=I.val * (A.B.a.S.block m).val:= rfl
    let h:I.val=c.val*c'.val:=rfl; let h':I.val=c'.val*c.val:= Nat.mul_comm ..
    let L := (Pane.panel A m hp).patch; let H₁: f.val=I.val*L.L.val:=rfl
    ∃ (w:RG.Rep G f) (v:Lens R H N w β), Nonempty (Volume (Lace.project (P:=L) (h:=hp) (H:=H₁) h (enoughC R hc)) v.tape L₀.tape n) ∧
      Nonempty (Volume (Lace.project (P:=L) (h:=hp') (H:=H₁) h' (enoughC R hc')) v.tape L₁.tape n)
variable (hm : m<N)
include hm
lemma score (n:ℕ)(i:Site c) : (B).Regular (Animals.neighbors r i) (F n i) ∧ ∀ V: Config G c, flags (B).threshold V=∅ → ‖F n i V‖ ≤ Trio.heat G (D.L J) (R.expense J B').wanting (Bright.miner R m) λ' x:= by
   obtain ⟨-,hh,hv,-⟩:= Bright.climb (b:=(R.target J B'|>.halo)) (n:=mast J) (j:=radiusB x) (A.B.a.budget m|>.B_pos)
   obtain ⟨w⟩:= Tree.select (panel A m hp).ratio (panel A m hp).patch.odd_side
   have ht:= (roomy R hp hm L₀.chart L₀.stamp w).1
   refine ⟨seen B rfl (portal ..) hv hh i ht, fun X hx=>?_⟩
   have hK:= Bright.revenue rfl hv hh ht X i hx (portal _ L₀.tape n) n
   rw [PriceCompiler.beta_eq A.B.valid, (Rain.jersey (A:=A) (m:=m)).2.2.2] at hK; exact hK

-- combine price Cover rotations, estimate from funding without an ad hoc lens at ANY distinct kernel! After below Ready; don't use hu affinity assuming continuity.
lemma aligned_wrap (n:ℕ)(hc:Chairs R m c)(hc':Chairs R m c')(he:Aligned R hp L₀ hp' L₁ hc hc' n) : Trio.Compatible (F n) (τ n) (B) r:=by
   intro i i' V V' hV hV' hQ
   obtain ⟨u₃,L₂,⟨hL⟩,⟨hL'⟩⟩:=he
   let X₀:=c*c'; let f₀:=X₀ * (A.B.a.S.block m); have h₀:f₀.val=X₀.val * (A.B.a.S.block m).val:= rfl
   have h:X₀.val=c.val*c'.val:=rfl; have h':X₀.val=c'.val*c.val:=Nat.mul_comm ..
   let v₁:= Lattice.translate i V; let v₂:= Lattice.translate i' V'; let z₁:=(Macrame.normal (Deck.divides h) h).links v₁; let z₂:=(Macrame.normal (Deck.divides h') h').links v₂
   let u₄:=Flare.stage R h₀ L₂
   have hv := R.pledging.jewels J x (A.B.valid.pays m) B' (step_paid _ m)
   let K₀:=L₀.chart; let K₁:=L₁.chart; let K₂:=L₂.chart
   obtain ⟨C₁,t,d,b,P₀,I,s,v,u',z,b',⟨N₀,H⟩,H₀,H₁⟩:= hv.2 _ _ _ _ (K₀.laws.data.funds) (Pane.ovation A N hp hm R.pledging.conducts.full) _ K₀
   obtain ⟨C₂,t,d,b,P₀,I,s,v,Q',z,b',⟨N₁,H⟩,H₀,H₁⟩:= hv.2 _ _ _ _ (K₁.laws.data.funds) (Pane.ovation A N hp' hm R.pledging.conducts.full) _ K₁
   obtain ⟨C₃,t,d,b,P₀,I,s,v,Q',z,b',⟨N₂,H⟩,H₀,H₁⟩:= hv.2 _ _ _ _ (K₂.laws.data.funds) (Pane.ovation A N h₀ hm R.pledging.conducts.full) _ K₂
   have hk : Shelf.terrace W (mast J) ≤ r := Bright.climb (b:=(Ψ).halo) (n:=mast J) (j:=radiusB x) (B).B_pos |>.2.2.1
   have hx : 4*(r+W)+16 ≤ c.val:=hc; have hx' : 4*(r+W)+16 ≤ c'.val:=hc'
   have hN : u₄ n 0 z₁ = F n ((splitter (divides h)) 0) v₁:=
       Flare.combine h (enoughC R hc) (hs:=hp) (hh:=h₀) (K:=A.B.a.clock.kernel) K₂ K₀ (L₂.snap.trans L₀.snap.symm) n (mast J) rfl (L₂.thresh.trans L₀.thresh.symm) (L₂.drift.trans L₀.drift.symm) N₀ N₂ hL (by omega) α ((B).B) v₁ (by unfold v₁; rw [←pull_one]; exact Pane.tranquility V hV ..) 0 -- order
   have hN' : u₄ n 0 z₂ = τ n ((splitter (divides h')) 0) v₂:=
       Flare.combine h' (enoughC R hc') (hs:=hp') (hh:=h₀) (K:=A.B.a.clock.kernel) K₂ K₁ (L₂.snap.trans L₁.snap.symm) n (mast J) rfl (L₂.thresh.trans L₁.thresh.symm) (L₂.drift.trans L₁.drift.symm) N₁ N₂ hL' (by omega) α ((B).B) v₂ (by unfold v₂; rw [←pull_one]; exact Pane.tranquility V' hV' ..) 0
   have hh : u₄ n 0 z₁=u₄ n 0 z₂:= by
      have hL:(2*(r+1) < X₀.val):= by have hf:c.val ≤ X₀.val:= Nat.le_mul_of_pos_right _ c'.pos; omega
      apply (Flare.score R h₀ L₂ hm n 0).1.sites _ _ (readNear 0 hL ?_); unfold z₁ z₂ v₁ v₂; rw [Slide.rolls,Slide.rolls,map_zero,map_zero,increases,increases]; exact hQ
   rw [map_zero] at hN hN'; refine (Eq.trans ?_ hN.symm).trans ((hh.trans hN').trans ?_)
   · unfold v₁; rw [←pull_one]; have h:= ((Bright.mirrors α O _ B (portal L₀.chart L₀.tape n) k n) 0 1 i V).symm; simp only [Lattice.affine,Signed.act_zero, zero_add] at h; exact h
   unfold v₂; rw [←pull_one]; have h:= ((Bright.mirrors α O _ B (portal L₁.chart L₁.tape n) k n) 0 1 i' V'); simp only [Lattice.affine,Signed.act_zero,zero_add] at h; exact h
end pair
end YM.Juniper.Flare
