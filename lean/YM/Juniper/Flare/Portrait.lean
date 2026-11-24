import YM.Juniper.Flare.PeriodCost
import YM.Juniper.Flare.Curtail
/-!
 # From true lens comparison to budgeted reclosure with *independent
 output stencil*. Effective section on any period not from the Stamp's
 hardRead choices. Addresses books & forced terms retained each place.
 Sign and marker genealogy account explicitly.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain Bright
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {c f:Side} {i j N m n r:ℕ}
section aid
-- generalizer of Marlin.cruiseV. projection-FULL support not fee, needed raw identity even before pairing with hard/thin bills. Moment on E sums after Q and Ψ interpolation.
variable {X Y: Listing G c}(P: Listing G c) {F: Collection.Source G c}(v : Collection.Source G c)
      {f : Config G c→ ℝ} {a b :Offer G c} {S:BudgetPoint}{m q:ℕ}{A D :ℝ}
lemma sailing (h : Meadow.Budget S P.reg v.logRead A) (he : ∀ g o,Nonempty ((P.read v).Moves g o))
      (hg : ∀ i:Seat c, ∀ V: Config G c,f (i.view V)=f V) (k:Offer G c)
      (hx : ∀ V: Config G c,f V=(P.read v).additive S V+(Fintype.card (Site c):ℝ)*D+(∑ i, masked S.threshold (neighbors q i) (a i) V)+∑ i:Site c,b i V) (V : Config G c):
      f V= ((pluck S (lodge P q m)).read { (Voucher.void G c) with logRead:= (bison v a k).regular } |>.additive S V) + D*Fintype.card (Site c) -Voucher.tax b V:= by
   let y:= leanU c; let θ:= P.read v; let u:= bison v a k
   let g (i:Marlin.Door c):= masked S.threshold (sea q i).support (choir a i) V; let t (i:Marlin.Door c):= choir (-b) i V
   let Z:= pluck S (lodge P q m); let X1:= Z.read { (Voucher.void G c) with logRead:=u.regular }; have hM : X1.additive S V= θ.additive S V+∑ i,g i:= by
      let f'(i:Civ c):=Sum.elim (fun i=> θ.regularOccurrence S i V) g i; have hh i:X1.regularOccurrence S (y.symm i) V=f' i:= by change masked _ (Sum.elim P.reg (sea q) (y (y.symm i))|>.support) (Sum.elim _ _ (y _)) _= _; rw [Equiv.apply_symm_apply]; cases i<;> rfl
      have hb : X1.additive S V=∑' i,f' i:= by rw [← y.tsum_eq f']; unfold Activities.additive; refine tsum_congr fun i=>?_ ; rw [← hh,Equiv.symm_apply_apply]
      rw [hb]; exact Summable.tsum_sum (f:=f') (stashes S P v V h) Summable.of_finite|>.trans (congr_arg (θ.additive S V + ·) (tsum_fintype g))
   let c':=(Fintype.card (Site c):ℝ); have hh(e:Seat c): (∑ i:Site c,g (e,i)) -∑ i: Site c,t (e,i)= Rim c*(f V-θ.additive S V-c'*D):=by
      have hr:= hx (e.view V); have he':θ.additive S (e.view V)=θ.additive S V:= streams S V v 0 _ _ P (he e.1 e.2|>.some)
      rw [hg, show (P.read v).additive S (e.view V)=_ from he'] at hr
      have hb i:t (e,i)=Rim c * (-(b i (e.view V))):=rfl
      have hF i:g (e,i)=_:= Song.tune (Marlin.leap q) a e i V S -- ns check
      simp_rw [hF,hb, ← mul_sum,Finset.sum_neg_distrib]; rw [hr]; ring
   change f V= X1.additive S V+D*c'-∑ i,t i
   rw [hM]
   have he : (∑ i,g i)-∑ i,t i=f V-θ.additive S V-c'*D:= by rw [Fintype.sum_prod_type (f:=g), Fintype.sum_prod_type (f:=t),← sum_sub_distrib]; simp_rw [hh]; rw [sum_const,card_univ,nsmul_eq_mul, ← mul_assoc,Song.balance,one_mul]
   linarith only [he]
end aid

section frame
private lemma push_mask_sub (t:ℝ)(p:Support c)(f g:Config G c→ℝ)(x:Config G c) : masked t p (f-g) x=masked t p f x-masked t p g x:= by unfold masked Set.indicator; split; exact rfl; ring
variable {D: Rolls X.p} {A:Alloy X D} (R : Factor A)
variable {β:ℝ}
local notation "J"=> A.B.a.clock.J (m+1)
local notation "B"=> (A.B.a.budget m)
local notation "B₀"=> (A.B.a.budget (m+1))
local notation "x"=> A.B.a.clock.hatBeta m
local notation "z"=> A.B.a.clock.hatBeta (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "L"=> D.L J
local notation "H"=> mast J
local notation "α"=> A.B.kin.alpha N m
local notation "u!"=> Bright.home R m
local notation "u₁"=> unboxed R m
local notation "O"=> Chi.canonical
local notation "Y"=> caves R m
local notation "V"=> miner R m
local notation "ℒ"=> Meadow.studio V (radiusB x)
local notation "W"=> Mint.width (R.target J I).halo (radiusB x) (radiusB x)
local notation "t!"=> (R.expense J I)
variable (hm:m<N) (hp: f.val=c.val*(A.B.a.S.block m).val) {u:RG.Rep G f}
local notation "k"=> (((z)^deep J+(z)^deep J)+(z)^deep J)
local notation "ζ"=> Cash.armK (R.target J I) L (R.shape.μ J I) x 0 (R.expense J I).degrees
variable (P : Lens R hp N u β) (P': Pages R N m β)
local notation "F"=> plusone P.chart (Bright.blank P.chart) O α
variable {δ γ b b' : ℝ} (T₀:Curtain G c)(Q:∀ i:Stars, Curtain G (caves R m i))
    (hV:T₀.TidyC (A.B.a.budget m) (Meadow.studio (Bright.miner R m) (radiusB (A.B.a.clock.hatBeta m))) b)(he:∀ i:Stars,(Q i).TidyC (A.B.a.budget m) (Meadow.studio (Bright.miner R m) (radiusB (A.B.a.clock.hatBeta m))) b)
local notation "q"=> T₀.stamp
local notation "Ai"=> T₀.book.read q
local notation "K!"=> (X.p.profile I)
local notation "χ"=> Trio.heat G L (t!).wanting V K! x
local notation "Π"=> portal P.chart P.tape n
local notation "t"=> Flare.chest R hp P n
local notation "Υ"=> Song.posting B P.chart
local notation "Lp"=> Bright.lighted R m
local notation "f₀"=> fun i:Stars=> Flare.stage R (Bright.sews R m i) (P'.books i) n
local notation "g₀"=> Flare.stage R hp P n
local notation "ν"=> ornament (c:=c) Lp f₀
local notation "K"=>tapeFor R hp u
local notation "g!"=> Trio.ornament (c:=c) Lp (fun i=>(Q i).root)
abbrev portraits (n:ℕ):Offer G c:= ornament (Bright.lighted R m) (fun i:Stars=> Flare.stage R (Bright.sews R m i) (P'.books i) n) - ornament (Bright.lighted R m) (fun i=>(Q i).root)
local notation "u₀"=> portraits R P' Q (c:=c) n
abbrev disgrace (n:ℕ):= failure R hp P P' n - Curtain.faint B T₀ Q Lp u!
local notation "f"=> disgrace R hp P P' T₀ Q n
abbrev lensLit := Marlin.pluck B (lodge Υ (Bright.home R m) (2*u!))
local notation "Z!"=> lensLit R hp P
-- choose hard stub.Y rather than new assumptions: a Listing parameter. Pack’s hard & seam payments rerouted from pulse (actual Hart).
def shelved (n:ℕ): Collection.Source G c:= ⟨(bison (Flare.chest R hp P n) (portraits R P' Q n) (disgrace R hp P P' T₀ Q n)).regular,0⟩
abbrev inst := Voucher.package T₀.book (lensLit R hp P) T₀.book
abbrev route (n:ℕ): Collection.Source G c:= Voucher.stack (Voucher.void G c) (shelved R hp P P' T₀ Q n) q
abbrev wait := Voucher.stack (Voucher.void G c) (Voucher.void G c) T₀.stamp
abbrev frameValue (n:ℕ):= Flare.stage R hp P n 0 1-T₀.root 0 1
local notation "f#"=> shelved R hp P P' T₀ Q n
local notation "A₁"=> inst R hp P T₀
local notation "y!"=> route R hp P P' T₀ Q n
local notation "T"=> wait T₀
local notation "v!"=> Flare.ScheduleCost R m
local notation "ξ"=> v! +turnFee B*γ
variable (ht: Collection.Local (Song.posting (A.B.a.budget m) P.chart) (A.B.a.budget m) (Flare.chest R hp P n) (Flare.ScheduleCost R m) (Cash.armK (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) 0 (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).degrees))
-- code cost at output before render, via auxiliary lifts
include ht T₀
lemma moored : Meadow.Budget B (Marlin.leap (u!)) (portraits R P' Q (c:=c) n) γ →
     Meadow.Budget B (Z!).reg (shelved R hp P P' T₀ Q n).logRead ξ:= by
     intro h; obtain ⟨i,hp,hL⟩:=ht.cheap; exact Marlin.reg_bison Υ u! (2*u!) (t) (u₀) (f) (show Meadow.Budget B (Υ).reg (t).logRead v! from ⟨i,hL, fun j=>⟨ht.smooth _,hp _⟩⟩) h

include hm hV
lemma runway (T' : Meadow.Budget B (Marlin.leap u!) u₀ γ) (i : Config G c) : let δ:= frameValue R hp P T₀ n
     ((Υ).read F).additive B i = ((A₁).read y!).additive B i + δ* Fintype.card (Site c) - Voucher.tax f i:= by
    intro d
    obtain ⟨s,hf,hh⟩:=ht.cheap; have hE : Meadow.Budget B (Υ).reg (t).logRead v!:=⟨s,hh,fun i=> ⟨ht.smooth _,hf _⟩⟩
    let U:=(Υ).read F; let Z(X:Config G c):= U.additive B X-(Ai).additive B X; let η:= Fintype.card (Site c)
    let S:=Classical.choice (Tree.select (panel A m hp).ratio (panel A m hp).patch.odd_side); have hs:= (roomy R hp hm _ P.stamp S).1
    have hF (i: Seat c) (X':Config G c): Z (i.view X')=Z X' := congr_arg₂ (·-·) (Marlin.streams B X' (F) 0 i.1 i.2 (Υ) (hs.transforms i.1 i.2|>.some)) (Curtain.additive_auth hV i X')
    have he' (X':Config G c): Z X' = (((Υ).read t).additive B X') + η*d+(∑ i:Site c, masked (B).threshold (neighbors u! i) ((u₀) i) X') + ∑ i:Site c,f i X':= by
       have hh:= total_words R hm hp P P' X' n; have hx' := Curtain.sits Lp (D:=u!) hV (Q:=Q) X'; unfold Z disgrace portraits; rw [show U.additive B X'= _ from hh,hx']; simp_rw [Pi.sub_apply, push_mask_sub, Finset.sum_sub_distrib]; unfold η d frameValue; ring
    have h₁ : Z i= ((Z!|>.read f#).additive B i)+ d*η-Voucher.tax f i:= Flare.sailing Υ (t) hE ht.transforms hF f he' i
    have h₂:= Voucher.additive_pack T₀.book i (p:=Voucher.void G c) (moored R hp P P' T₀ Q ht T') hV.income; unfold Z U η at h₁; rw [show ((A₁).read (y!)).additive B i= _ from h₂]; linarith only [h₁]
end frame
end YM.Juniper.Flare
