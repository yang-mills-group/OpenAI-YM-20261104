import YM.Juniper.Orrery.Chrome
import YM.Juniper.OrbitPrice.Consumer
/-!
 # Calendar tariffs for handing this to Core comparison

 One inevitable regulator dependence EVEN on ideal Fk side at WilsonX
 before iter/feed/mesh comparison: native coupling distortion. We don't
 suppose Ruby or read from Shelf χ; expose costs in true-coupling units.
 The result here is iterative unmarked compares through *arbitrary* length
 once each local real Twig billed. Rather than formal arms on all stamps,
 this is paid using Culmin on the local aurora real E symbols. Still need
 pay Twigs, and much more incl Fk conventions, count marks & connect capture.
 (It is NOT itself a power series truncation statement, just a remainder
 receipt vs symbols in the rendered Epoch, and at true β.)
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Further.PhysicalPeriodLimitF933 Macrame Deck Flare
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost Input Supply Org Pane Slide
open Progress.DirectedRecipe UVExtension Oriel Dales Tour Height Averaging
open Whirl Ovens Ovens.Pipes Rack Voucher Rain Time Bright Charted Lamppost Guild Tabernacle Spire
open Poll Pond Blaze Gauze Metric
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {N m n r:ℕ}
variable (U: Nursery G hG)
local notation "S"=> U.S
local notation "A"=> U.A
local notation "H"=> U.A.B.a
local notation "F₀"=> U.family
local notation "F"=> U.family.path.rep N n
local notation "L"=> U.A.B.a.clock
local notation "T"=> ((U.S).fits N n)
local notation "R"=> U.X
local notation "K"=> (F (m+1)|>.beta)
local notation "G*"=> (F m|>.beta)
local notation "V"=> U.A.B.a.S.side m n
local notation "V₀"=> U.A.B.a.S.side (m+1) n
local notation "Z"=> (L).hatBeta m
local notation "Z₀"=> (L).hatBeta (m+1)
local notation "Y"=> (L).allowance m
local notation "P"=> U.A.B.a.params m
local notation "S₀"=> (L).op m n
local notation "Ψ"=> U.A.B.a.budget m
local notation "B"=> U.A.B.a.budget (m+1)
local notation "Δ"=> (U.A.B.kin.alpha N m)
local notation "J"=> (L).J (m+1)
local notation "I"=> (L).J m
local notation "ε"=> U.S.grove.witness
local notation "w"=> (warmth H r m)
local notation "w!"=> (warmth H r (m+1))
local notation "W"=> mount U.X N m n
local notation "K*"=> Year H r
local notation "β!"=> U.A.B.a.S.side N n
local notation "Z*"=> (F N|>.beta)
lemma native_band (hm:m≤ N) : G*∈ RG.Shoot.band H m:= ((S).ticking N n (Spire.Uses.centerP H)).prices _ (Nat.zero_le _) hm|>.2
noncomputable def mine (N n r:ℕ) :Year H r N := prologue (U.S.grove.rise N) (native_band U (N:=N) (m:=N) (n:=n) le_rfl) (erasureK H r N) ((glow H N r).2)
-- pinned to the physical beta stencil still an expansion rendering choice, not a PT radial coefficient. Not choose its E from any in-scale density, explicit Start stencil only, Carved to primary.
include hG
lemma embark : let T':= mine U N n r; ∃ d:Cham H N n, ∃ x:Valve N n H d,∃ v:ℝ, Standing U N N n r T' d x x v ∧ U.family.path.rep N n N= mount U.X N N n x.val Z* v:= by
   let D:=T; let u:= Native.genes U.X hG U.S N n 0; have hq:= Spire.Uses.centerP (H)
   obtain ⟨he,hb⟩:= (T).acts (U.S.cart N n) (U.S.token N n) U.S.grove.coins hq; let v:=u N; let e:=(F N).v
   have hf: F N= mount U.X N N n v.val (F N|>.beta) e := rfl; have hh:= (T).plates U.S.grove.enabled U.S.grove.climbed he hq hb N le_rfl|>.1; intro T'
   refine ⟨_,v,e,⟨hh.trans (by norm_num [Camp.soft,rim]),hh.trans (by norm_num [Camp.soft,rim]),?_,rfl,?_,?_⟩,hf⟩
   · have hz := (T).top_mom he; let f:= β!; let g:=WilsonStartup.Start.dictionary G f; let p:=WilsonStartup.Start.payload ((H).params N).clip (H|>.budget N) G f (F N|>.beta); have hP :v.val.1=(Rack.widen g p).regular:= congr_arg (fun x: (T).Home N=> x.val.1) hz
     rw [hP]; exact ⟨Flare.printable g p⟩
   · rw [sub_self,norm_zero]; exact mul_nonneg (by norm_num [rim]) (glow H N r|>.1.le)
   intro p'; refine ⟨rfl,⟨U.A.B.support.cap N N le_rfl,?_⟩,by intro hi; omega⟩; apply (Dales.tapT N n H ((T).W N) v).1; exact hh.trans (by norm_num [Camp.soft,rim]) -- D.W'
section iterate
variable {v: Year U.A.B.a r m} {V':Snip G} {E: Extras G} (h:Stock (Orrery.agenda V' E) U)
                (M:∀ i:ℕ,Specs U.A i)
-- irrespective of demanded m geometry at each step, handing forward this local roster. Handle m-level view only on good plateau (not all low i; allow default below). Need wrapper `Chronology`. top always valid.
local notation "h!"=> (Orrery.attaches h).2
local notation "Y₁"=> fun j : ℕ=> (U.S.fits N n|>.charts j)
noncomputable def trove (i:ℕ): Year H r i:=
    if hk:i<N then if hv: powerUp r≤(L).J (i+1) then Orrery.after U.X ((Y₁ i) hk) U.S.grove.enabled h! hG (M i) hv else mine U i n r
    else mine U i n r -- `n` period only for top, nonanalytic roster beyond request pad. `θ₁` Own
local notation "P'"=>trove U (N:=N) (r:=r) (n:=n) h M
include h
lemma dawn : P' N = mine U N n r:= dif_neg (by omega)
lemma falls (hm:m<N)(hv:powerUp r ≤ J): P' m = Orrery.after U.X (Y₁ m hm) U.S.grove.enabled h! hG (M m) hv:= by unfold trove; rw [dif_pos hm,dif_pos hv]
-- Binder Purchaser, IF eventually asks.
def Bank (M:∀ i:ℕ,Specs U.A i) (r m N n:ℕ): Prop :=
    ∀ i:ℕ,m≤ i → i < N → Orrery.Receipt U.X N i (powerUp r) (trove U (N:=N) (n:=n) (r:=r) h M (i+1)) (M i) (U.family.path.rep N n (i+1)|>.beta)
-- attend only genuine Steps.
local notation "C"=> (M m).frames V

def detects (m: ℕ):ℝ:= let v:= (M m).frames (U.A.B.a.S.side m n); U.A.B.kin.alpha N m + Averaging.delta (v.book.read v.stamp)
def Rumbling (r m:ℕ): Prop := ∀ i:ℕ,m ≤ i → Cinch.wraps (U.A.B.a.clock.hatBeta i) (U.A.B.a.S.side i n) ∧ powerUp r ≤ (L).J (i+1)
-- rumbling maybe omit h.
variable (hr:Rumbling U (n:=n) r m)(hB:Bank U h M r m N n)
include hB hr
-- guarantee simultaneous choice SPEC, not asserting supports of marks compatible; equality of evaluation and addresses via Standing and Step.Epoch.point for x.
lemma integrate (i:ℕ)(hi:m≤ i)(hN:i≤ N) : (i < N → |(F i).beta - (F (i+1)).beta - detects U (N:=N) (n:=n) M i| ≤ Pluto U*warmth H r i) ∧ ∃ d:Cham H i n,∃ x y:Valve i n H d, ∃ v:ℝ, Standing U N i n r (P' i) d x y v:= by
    induction hN using Nat.decreasingInduction with
    | self => obtain ⟨d',x,u,hh,-⟩:= embark U (N:=N) (n:=n) (r:=r); exact ⟨fun hx=> (lt_irrefl _ hx).elim,d',x,x,u,(dawn U h M) ▸ hh⟩
    | of_succ i hn ih =>
      obtain ⟨d',z,x,u,hv⟩:= (ih (hi.trans (Nat.le_succ _))).2
      obtain ⟨hP,hφ⟩:= hr i hi; obtain ⟨hz,d,v,p,v',ht⟩:= major (U:=U) V' E h hn hφ hP (M i) (P' (i+1)) (hB i hi hn) hv
      refine ⟨fun _=>?_,d,v,p,v',(falls U h M hn hφ) ▸ ht⟩; unfold detects; rw [← sub_sub]; exact hz
end iterate
-- ensure report can be read in REAL beta without taking N fixed, not loosing q loss. Mark dependent estimates to follow. Carry exponent w ~ ghat^(2r)+ancillary affine. Additive including scalar overhead at capture needs separate payment. 
open Pert.Asymptotics
local notation "t"=> regulatorRun F₀ N n m
include U
lemma heat_to (hm:m≤ N): w ≤ (2:ℝ)^r * (t)^(2*r):=by
   have hp:= native_band U (n:=n) hm; have ht :1<Z:= H|>.fits.delayed m; have hz:0< Z:= zero_lt_one.trans ht; let x:=t; let a:= G*; have hL : Z/2 ≤ a:= hp.1; have h : a≤2*Z:= hp.2; have he:0<a:= (half_pos hz).trans_le hL; have hx:0<x:= inv_pos.mpr (Real.sqrt_pos.mpr he)
   unfold warmth; rw [← inv_pow,pow_mul,← mul_pow]; apply pow_le_pow_left₀ (inv_nonneg.mpr hz.le) ?_; have hf : t^ (2:ℕ)= a⁻¹:= by change (Real.sqrt a)⁻¹ ^ (2:ℕ)=_; rw [inv_pow, Real.sq_sqrt he.le]
   rw [hf]; apply le_trans (b:=2*((2*Z)⁻¹)) ?_ (mul_le_mul_of_nonneg_left (inv_anti₀ he h) (by norm_num)); apply le_of_eq; field_simp
-- often interpret relative normalized currency. EBound unnormalized buys ≲ real^
variable {k:Year U.A.B.a r m}{d: Cham U.A.B.a m n}{x y:Valve m n U.A.B.a d}{b:ℝ}
lemma budgetPrice (hm:m≤ N)(he:Standing U N m n r k d x y b): (Tabernacle.floor (U.A.B.a.budget m) (x-y).val).EBound (U.A.B.a.budget m) (((rim/4)*((2:ℝ)^r) * t^(2*r))*Y):= by
    refine (VerifiedReset.Time.E_rises (?_ : (Tabernacle.floor (U.A.B.a.budget m) (x-y).val).EBound (U.A.B.a.budget m) (rim/4*w * Y)) ?_); swap
    · refine mul_le_mul_of_nonneg_right ?_ (fundedP m H|>.1.le); exact le_trans (mul_le_mul_of_nonneg_left (heat_to (m:=m) (r:=r) (n:=n) U hm) (by norm_num [rim] : 0 ≤ rim/4)) (le_of_eq (by ring))
    have hu:=he.near; rw [← map_sub] at hu; exact ((Native.pay_total _ _).1 hu).boundE
end YM.Juniper.Orrery
