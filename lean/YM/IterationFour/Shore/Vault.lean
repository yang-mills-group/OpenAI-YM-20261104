import YM.IterationFour.Shore.Shoal
import YM.IterationFour.Vacuum.HistoryTest

/-!
# Ledger certified on real stamps, including strong hard charges

Exploit the ACTUAL broader numeric legality of stamp's Γport, not
varying any parameter outside physical calibration. All capitals
funded once at +1 merger; top is a separate call (can arrange forceEarly
padded trivially).
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Shore
open Function Filter RG Wilson Lattice
open AnalyticBridge VerifiedReset Collection
open Progress.DirectedRecipe Next.Scheduling
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{a : Levels G}{t W V A κ : ℝ}{n i : ℕ}
lemma probe_le {κ'}(h : Payments.Rates n A W t κ'): W ≤ A:= by
   have h':= Real.add_one_le_exp (Payments.inflation W t κ'); have hh:=Real.exp_nonneg (-κ'); have he:= mul_le_mul_of_nonneg_left (show Payments.inflation W t κ' ≤ Real.exp (Payments.inflation W t κ')-1 by linarith) hh
   refine le_trans (b:=Bid.quote κ' _) ?_ h.returns
   refine le_trans ?_ he; unfold Payments.inflation; rw [mul_add,← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]; exact le_add_of_nonneg_right (mul_nonneg hh (mul_nonneg zero_le_two h.soft))

lemma halfPrice (hx:0<W) : (V / Next.Scheduling.Clock.gap W)^ (2:ℕ)= 2*(V / Next.Scheduling.Clock.gap (W/2))^(2:ℕ):=by
    have hk:0<W/2:= half_pos hx; simp only [Next.Scheduling.Clock.gap,div_inv_eq_mul,mul_pow,Real.sq_sqrt hx.le,Real.sq_sqrt hk.le]; ring
lemma coupon (g : Postage) (f : Time.Forecast g) {β b w :ℝ}(h:0<β)
    (hp:Real.exp (-Payments.Pairing.kGoal g b (β/2)) ≤ w)
    (hK:f.pair.strong b (β/2) ≤ w): Real.exp (-Payments.Pairing.kGoal g b β) ≤ w^2 ∧ f.pair.strong b β ≤ w^2:= by
    unfold Payments.Pairing.strong Payments.Pairing.kGoal at *; rw [halfPrice (V:=Instrument.plain.t b) h] -- rewrite both
    constructor
    · refine le_trans (le_of_eq ?_) (pow_le_pow_left₀ (Real.exp_nonneg _) hp 2); rw [sq (Real.exp _),← Real.exp_add]; ring_nf
    let t :ℝ:= (Instrument.plain.t b / Next.Scheduling.Clock.gap (β/2))^ (2:ℕ)
    let r:= -f.pair.r*t; let C:= f.pair.C; have ht : 1 ≤ C:= le_max_left ..
    have hh : 0 ≤ C:= zero_le_one.trans ht
    calc
       _ = C*Real.exp r^ (2:ℕ) := by unfold C r t; rw [sq (Real.exp _),← Real.exp_add]; ring_nf
       _ ≤ (C*Real.exp r) ^ (2:ℕ) := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
       _ ≤ _ :=pow_le_pow_left₀ (mul_nonneg hh (Real.exp_nonneg _)) hK 2

end YM.IterationFour.Shore

namespace YM.UVExtension.Spire.IterationFour
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
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
open Orchard Mast
open YM.IterationFour.Shore
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} {hG:G.Simple}
lemma perks {β:ℝ}{i:ℕ} (_s:Uses R hG) (hp: β ∈ band A.B.a (i+1)) :
   let a:=A.B.a; 0 ≤ forecastK a i R.scout β ∧ forecastK a i R.scout β ≤ (A.B.a.clock.forcedAllowance i)^ (2:ℕ) ∧ quoteHard a i R.book β ≤ (A.B.a.clock.forcedAllowance i)^ (2:ℕ):= by
   intro a
   let b0:=a.budget i; let j:=a.clock.J (i+1); let j':=a.clock.J i; let Q:=R.book j j'; let f:=R.scout j j'; let k:=β/2; let u:=a.clock.hatBeta i; let d:=a.clock.hatBeta (i+1)
   have h:= R.machine.shops _ _ (A.B.valid.pays i) _ (step_paid a i)
   have hz: d=u+G.slopeConstant*Real.log (D.L j).val :=by rw [← PriceCompiler.block_eq A.B.valid]; exact (Deployment.hat i).symm
   unfold Time.shop at h; dsimp only at h
   rw [← hz,← params_eq A.B.valid] at h
   have hh := R.machine.coverage j j' (step_paid a i)
   obtain ⟨ho,hB,hV,hE,hW,hP,hT⟩:= Deployment.clock_eqns a.clock i
   have hY:1<d:=a.fits.delayed _
   have ht: k∈Set.Icc (d/4) (4*d):=by unfold k; have he:d/2≤β:=hp.1; have hq:β≤ 2*d:=hp.2; constructor <;> linarith only [he,hq,hY]
   obtain ⟨_,_,hv,hZ⟩:= (h b0 (show Same (A.B.a.params i) b0 from ⟨rfl,rfl,rfl⟩) rfl hT).2.2 (R.exchange j j') (A.B.kin.alpha (i+1) i) 1 k (UVNext.CouplingReset.within_alpha (Nat.lt_succ_self _)) ht
   obtain ⟨m,κ,hν,he⟩:= hv.hard
   let s:=a.clock.forcedAllowance i; have hg:Real.exp (-Payments.Pairing.kGoal Q d k) ≤ s:= by rw [show s= Next.Scheduling.Instrument.plain.w u from hW]; exact (hZ hh.1).2
   have hp0 : f.pair.strong d k ≤ s:= (probe_le he).trans hg
   have hx := YM.IterationFour.Shore.coupon Q f (b:=d)  (show 0<β from ?_) hg hp0
   swap; · have he:d/2≤β:=hp.1; linarith only [he,hY]
   exact ⟨mul_nonneg (f.pair.C_nonneg) (Real.exp_nonneg _),hx.2,hx.1⟩

variable (S: Uses R hG) {t K w} {B:PhysicalNext.Repeat.Legato.Bandage R K w} (L:Mast.Cellar S t B)
local notation "C#"=> Cellar.yard (Mast.roseA S) L
lemma invoices {N q i:ℕ} (h:i<N):∃ T:Bank G (C#.side i q), T.Holds (C#.path.rep N q i) ∧
    T.β= C#.path.β N q (i+1) ∧ T.alpha = A.B.kin.alpha N i ∧ T.H=Time.forecastE A.B.a i ∧ T.w=Time.forecastK A.B.a i R.scout (C#.path.β N q (i+1)) ∧ T.γ= quoteHard A.B.a i R.book (C#.path.β N q (i+1)):=by
  let H:=S.fits N q; let x:= H.Rest (S.cart N q) S.grove.coins 0
  let y:= H.Third (S.cart N q) S.grove.coins 0; let z:=H.Sail (S.cart N q) S.grove.coins 0
  let T:= H.race x y z; let J:= H.charts i h; let a:= A.B.a
  have ht : H.Shot x y z:= (H.acts _ (S.token N q) _ (Uses.centerP a)).1
  let W:= Market R J.atTopH; let V:= J.oracle R _ (ht.alive _ h) (z (i+1)); let P:= T (i+1)
  let s:= Item.song R J.atTopH J.W J.k V
  have he:T i= Item.issue R J.atTopH J.W J.k V:= ht.passes i h
  let D0:= a.budget i; let cStage:=(a.params i).clip; let α:= A.B.kin.alpha N i; let B₀:= A.B.kin.path N i
  have hv:= Guild.ready R h J.atTopH J.W J.k V.atH (V.links R J.atTopH) rfl V.related V.price V.aisle rfl S.grove.pledge J.hr
  have hp:= (Guild.standing R h J.atTopH J.W J.k V.atH (V.links R J.atTopH) rfl V.related V.price V.aisle rfl S.grove.pledge J.hr hG).1
  let Z':= flatRate a i q P
  let τ:= Z' + (∑' i,s.logRead i 1)/ (UVNext.CouplingReset.sites (a.S.side i q))
  have hs: Collection.vac s τ= Z' := by unfold Collection.vac τ; ring
  let d : ℝ:= P.beta+α+ Averaging.delta (W.read s)
  let Y:= Collection.branch W B₀ cStage D0 s α
  have hh : T i=finish B₀ cStage D0 (Collection.shelves W B₀ D0) Y d (Collection.vac s τ):=by rw [he,hs]; rfl
  exact ⟨⟨W,s,α,τ,P.beta,forecastE a i,forecastK a i R.scout P.beta,_,quoteHard a i R.book P.beta⟩,⟨hv,hp,hh⟩,rfl,rfl,rfl,rfl,rfl⟩

def extra (N q i:ℕ): Bank G (C#.side i q) := by
  let p:= (C#.path.rep N q i)
  exact ⟨⟨p.activities.reg,p.activities.forced⟩,⟨p.activities.E,p.activities.K⟩,0,0,p.beta,0,0,0,0⟩
def vales (N q i:ℕ): Bank G (C#.side i q):= if h:i<N then (invoices S L h).choose else extra S L N q i
def settled (N q:ℕ) : Ledger C# N q:= ⟨vales S L N q,fun i hi=>by rw [vales,dif_pos hi]; exact (invoices S L hi).choose_spec.1,fun i hi=>by rw [vales,dif_pos hi]; exact (invoices S L hi).choose_spec.2.1⟩
lemma invoiceKeep {N q i:ℕ} (h:i<N) :let Z:= (settled S L N q).stamps i
    Z.alpha = A.B.kin.alpha N i ∧ Z.H=Time.forecastE A.B.a i ∧ Z.w=Time.forecastK A.B.a i R.scout (C#.path.β N q (i+1)) ∧ Z.γ= quoteHard A.B.a i R.book (C#.path.β N q (i+1)):=by unfold settled; dsimp only; rw [vales,dif_pos h]; exact (invoices S L h).choose_spec.2.2
end YM.UVExtension.Spire.IterationFour
namespace YM.IterationFour.Shore
open Lattice Wilson RG Function MeasureTheory Filter Vacuum AnalyticBridge VerifiedReset Collection Ovens
open Progress.DirectedRecipe Averaging Extra.Iteration Currency
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C : Family G}{r N q m i : ℕ}
local notation "a#"=> C.path.levels
local notation "T#"=> C.path.rep N q
-- strict rates EVEN WITHOUT deepening postL papers, direct from physical cost on that stamp, including retained Book
variable (L : (N q:ℕ)→Ledger C N q)
structure Treasure : Prop where
    sells : ∀ N q i:ℕ,i<N → let V:=(L N q).stamps i; let w:= a#.clock.forcedAllowance i
       V.H=Time.forecastE a# i ∧ |V.alpha + G.slopeConstant*Real.log (a#.S.block i).val|+1≤ (a#.params (i+1)).drift ∧ V.γ ≤ w^ (2:ℕ)∧ V.w ≤ w^ (2:ℕ)∧ 0 ≤ V.w
variable {hG : G.Simple}
lemma treasuring (hm:C.Makes)(hp:UVExtension.Oasis.Floral (hG:=hG) C) : ∃ L:(N q:ℕ)→Ledger C N q, Treasure L:= by
   obtain ⟨M,P,Y,R,S,T,t,k,W,Q,L,H,hx,_⟩:=hp; subst C
   refine ⟨UVExtension.Spire.IterationFour.settled S L, ⟨fun N q i hi=>?_⟩⟩; intro V w
   obtain ⟨hz,hH,hF,hK⟩:= UVExtension.Spire.IterationFour.invoiceKeep S L (q:=q) hi
   have hB:= UVExtension.Spire.IterationFour.perks S (i:=i) ((hm.wilson.represents _ q _ hi).band)
   exact ⟨hH,hz.symm ▸ Y.B.support.kinetic N i hi, hK.symm ▸ hB.2.2,hF.symm ▸ hB.2.1,hF.symm ▸ hB.1⟩
end YM.IterationFour.Shore
