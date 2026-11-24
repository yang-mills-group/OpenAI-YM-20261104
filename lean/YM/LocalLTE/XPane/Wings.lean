import YM.LocalLTE.XPane.Swell
import YM.LocalLTE.Rendezvous.Wings
import YM.LocalLTE.Sapphire.Rose
import YM.LocalLTE.Vinyl.Prospects
import YM.LocalLTE.Album.Stores

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}

open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe
open YM.LocalLTE LocalLTE.Fan Pastel Marlin Animals
-- events buying uniform all-mark customer contracts. T stage pair stage.Vw, entire sup/support costs paid. general to multiple τ demands. z' FIX via τ.Wants.Adv.N.Dense
variable (R : Register D p u l)
variable (f:ℕ→ℕ→ℕ)(ψ:ℕ→ℕ→ℝ)
local notation "t'"=> s.profile
local notation "W₀"=> X
namespace ConcertZ
section upfront
variable (T:Targets s K) {Γ:ℝ}{Q:ℕ}
-- choose Watts & proves ∀l k.Width.Early Φ.dim; α and K predictable before floors; can be supplied reverse order i stage.Fe.Cu
variable (d:ℕ→ℕ→ℕ)(e:ℕ→ℕ→ℝ)(hE:∀ j i, Γ ≤ e j i ∧ 0<e j i ∧ e j i< Q/100) -- nat division annotation?
variable (p:Expenses T)
def ForecastX (d:ℕ→ℕ→ℕ)(p':Expenses T)(H:ConcertZ T Q Γ)(κ:ℝ)(W:ℕ→ℕ):Prop:=
    ∀ j i,StepStages j i→∀ L:Side,W j ≤ L.val→∀ α:ℝ,∀ o: Target.Order G α,∀ μ:ℝ,0<α→0<μ→∀ᶠ x in atTop,Fan.ManifestX (T j i) L o (p' j i) Chi.canonical (s.profile i).order (s.profile i).power Q (H.amp j i) (H.bbase j i) (d j i) (H.azi j i) (H.kap j i) κ (H.strength j i) Mallow.aust x μ
-- Explicit.H Contains Work.A.Lengths.ManifestX mesh no upper limit. put parameters later allocation.
variable (hr:∀ j i,3/8+(T j i).rate < Mallow.aust) {κ v:ℝ} (hk:Reliable G κ v)
include hr hk hE
lemma springX : ∃ H:ConcertZ T Q Γ,H.strength=e ∧ ∃ W, ForecastX T d p H κ W :=by
    have hp(j i:ℕ):∃ q:ℕ,e j i< (3/8:ℝ)*q:=by obtain ⟨m,h⟩:= exists_nat_gt (8*(e j i)); exact ⟨m,by linarith only [hE j i|>.2.1,h]⟩
    choose y h using hp; let b j i:= East.stagnate (y j i) (T j i).halo +1
    have hα(j i:ℕ):= Fan.EarnStepX (T j i) (p j i) Mallow.aust (hr j i) (by norm_num [Mallow.aust]); choose w hZ using hα
    have ha(j i:ℕ):= hZ j i (s.profile i).order (s.profile i).power Q (y j i) (b j i) (d j i) (e j i) κ v hk ((hE j i).2.1) (hE j i|>.2.2) (h j i) (show _ <b j i from Nat.lt_succ_self _)
    choose v k hV using ha
    exact ⟨⟨v,k,b,y,e,fun j i _=> ⟨(hE j i).1,(hE j i).2.1,(hE j i).2.2,h _ _,Nat.lt_succ_self _⟩⟩,rfl,fromMax w,fun j i hh L h W o μ hW hu=> hV _ _ L ((le_fromMax w hh).trans h) W o μ hW hu Chi.canonical⟩
end upfront
variable {Γ κ:ℝ}{Q:ℕ}
variable (d:ℕ→ℕ→ℕ)(T: ConcertZ X Q Γ)
local notation "α'"=> T.azi
local notation "A'"=> T.kap
local notation "K'"=>T.strength
-- Λ.Physical taus stored calendar! preserving χ
variable (κ:ℝ)
-- Structured budget for all required purchases including forced.
-- scaling applied only in the Towed proof; no scaled K in the actual step.
variable (g:ℕ→ℕ→ℕ)
-- v base =Y^aust common budget for attachment. no assumption volume small.
def sortX (j i:ℕ)(x:ℝ):Prop:=let m:= s.profile i; let α:= T.azi j i; let K:= T.kap j i
    let L:= D.L j; let μ:= R.μ j i; let Y:= betaF G x L; let e:= T.strength j i; let b:=T.bbase j i
    let k:= Blush.glyph x; let κ':=k*Y^(-e)/3; let B:=radiusB x; let a:=straw μ L G x; let c:= ((g j i:ℕ):ℝ)*Extra.Multi.siteFactor B *Y^aust+ (Fan.phaseP (p j i|>.earn) b (b* B)* Y^aust+Y^aust)
    0<κ' ∧ κ' ≤ 1 ∧ 0≤Y^aust∧ (((B+B+1:ℕ):ℝ)^4*(a/κ'+c) ≤ 1 ∧ κ'*(Real.exp (a/κ'+c)-1) ≤ (Y^(-e))*k) ∧ (Fan.ManifestX (X j i) L (R.o j i) (p j i) Chi.canonical m.order m.power Q (T.amp j i) b (d j i) α K κ e aust x μ)
structure CalendarX (V:Delays Θ):Prop where
   shells j i : StepStages j i → 32*(1+T.bbase j i) ≤ V.shells j
   growth j i : StepStages j i → 1≤ V.growth j
   stamp j i : StepStages j i→∀ x:ℝ,V.betaEntry j≤x→ sortX R d T κ g j i x
variable {m:ℕ→ℕ}(hF:T.ForecastX X d p κ m)(ht:∀ j,m j≤(D.L j).val)
include hF ht
set_option maxHeartbeats 400000 in
lemma eventsX (j i:ℕ)(hi:StepStages j i):∀ᶠ x:ℝ in atTop, sortX R d T κ g j i x:=by
    let t:= T; let a:=u j i; let μ:=R.μ j i; let e:= T.strength j i; let L:=D.L j; let X':= fun x=>betaF G x L
    have hp:0<a:= (R.consumes _ _ hi).1; have hU:0<μ:= (R.consumes _ _ hi).2.1
    have hx:=hF _ _ hi L (ht _) a (R.o j i) μ hp hU
    let b:=T.bbase j i; let μ₀(x):= Fan.phaseP (p j i|>.earn) b (b*radiusB x)
    have hk:Rate G L 0 μ₀:=by
       have hu:Rate G L 0 (fun x=>(ballCost (b*radiusB x):ℝ)):= by simpa only [Nat.add_zero] using Census.width_rate G L b 0
       exact (Rate.const 1).add (hu.mul_right _)
    let f x:= X' x^aust; let k(x):= Blush.glyph x*X' x^(-e)/3; let S(x):=(↑(g j i):ℝ)*Extra.Multi.siteFactor (radiusB x)* f x +(μ₀ x*f x+f x); let Z(x):= straw μ L G x/k x + S x; let u x:=(radiusB x+radiusB x+1:ℕ)
    let B x:=( (u x:ℕ):ℝ)^4; have hK x:1≤ B x:=one_le_pow₀ (show (1:ℝ)≤(u x:ℝ) from (by unfold u; norm_cast;omega))
    have hz': Mallow.aust<0:=by norm_num [Mallow.aust]
    have hₑ:0 <e:= T.bill j i hi|>.2.1
    have hZ:Rate G L Mallow.aust (fun x=> B x* Z x):=by
       have hv: Rate G L 0 B:=by unfold B u; push_cast; simpa only [zero_mul] using! ( ((Rate.radius_price (G:=G) (L:=L)).add Rate.radius_price).add (Rate.const 1)).pow 4
       have hf:Rate G L 0 (fun x=> Extra.Multi.siteFactor (radiusB x)):= by unfold Extra.Multi.siteFactor; simpa only [zero_mul] using! ((((((Rate.radius_price (G:=G) (L:=L)).mul_left 16).add (Rate.const 9)).mul_left 2).pow 4).mul_left (Real.exp 1))
       have hr:Rate G L aust S:=by unfold S; have hR:Rate G L aust f:= Rate.power; simpa only [zero_add] using! ((((hf.mul_left ((g j i:ℕ):ℝ)).mul hR)).add ((hk.mul hR).add (show Rate G L (0 + aust) f by simpa using hR)))
       have he : Rate G L aust (fun x=> straw μ L G x/k x):=by
           have hh:=(Blush.efferv (G:=G) (L:=L) hU (aust-e)).mul (Rate.power (G:=G) (L:=L) (a:=e))
           rw [sub_add_cancel] at hh; refine Rate.congr (hh.mul_right (3:ℝ)) ((Delay.shift_pos G L).mono fun x hx=>?_)
           dsimp only [k,X']; rw [Real.rpow_neg hx.le, div_eq_mul_inv]; field_simp -- edit
       simpa only [zero_add] using! hv.mul (he.add hr)
    filter_upwards [hx,hZ.below hz' 1 zero_lt_one,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx hv hX
    let Y:= X' x; have hh:0< X' x:=zero_lt_one.trans_le hX
    have hK': k x*3=Blush.glyph x*(Y^(-e)):=div_mul_cancel₀ _ (by norm_num)
    have hz: 0< k x:= by unfold k; exact div_pos (mul_pos (Blush.glyphpos x) (Real.rpow_pos_of_pos hh _)) (by norm_num)
    have he:k x ≤1:= by
       have h₁: (Blush.glyph x)≤ 1:= Real.sqrt_le_one.mpr (Real.exp_le_one_iff.mpr (by exact neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))) -- sqrt lemma edit
       have h :0≤Y^(-e) := Real.rpow_nonneg hh.le _; have h' : Y^(-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (neg_nonpos.mpr hₑ.le)
       have hp:= mul_le_mul h₁ h' h (zero_le_one); rw [← hK',one_mul] at hp; linarith
    have ht(x): 0≤ Extra.Multi.siteFactor (radiusB x):=by unfold Extra.Multi.siteFactor; positivity
    have h : 0 ≤ f x := Real.rpow_nonneg hh.le _
    have ha x:0≤ μ₀ x:=by unfold μ₀ Fan.phaseP; positivity
    have hh :0 ≤ Z x:= add_nonneg (div_nonneg (mul_nonneg zero_le_two (Real.exp_nonneg _)) hz.le) (add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ht x)) h) (add_nonneg (mul_nonneg (ha x) h) h))
    have hv: B x* Z x≤1:= (le_abs_self _).trans hv
    refine ⟨hz,he,h,⟨hv,?_⟩,hx⟩
    have hu : Z x ≤1:= (le_mul_of_one_le_left hh (hK x)).trans hv
    have he:= (Real.abs_exp_sub_one_le (show |Z x| ≤ 1 from (abs_of_nonneg hh).trans_le hu)); rw [abs_of_nonneg hh] at he
    refine le_trans (b:= k x*3) (mul_le_mul_of_nonneg_left (le_trans (le_abs_self (Real.exp (Z x)-1)) (he.trans ?_)) hz.le) ((hK'.trans (mul_comm ..)).le); linarith only [hu]
-- Delays.Roll.
lemma treasuryX (V:Delays Θ): ∃ W:Delays Θ,DelayLe V W∧ ∀ Y:Delays Θ,DelayLe W Y→ T.CalendarX R d κ g Y:=by
    obtain ⟨x,-,hx,hQ⟩:=collect_upper V.betaEntry _ fun j=>eventually_transitions j _ _ (eventsX R d T κ g hF ht j)
    let y j i:=32*(1+T.bbase j i); let W:Delays Θ:={V with betaEntry:=x,shells:=fromMax y ⊔ V.shells,growth:= (fun _=>1)⊔V.growth}; refine ⟨W,⟨hx,le_rfl,le_sup_right,le_sup_right⟩,fun Y hy=>?_⟩
    refine ⟨fun j i hi=> ((le_fromMax y hi).trans (show fromMax y j ≤ W.shells j from (le_sup_left : fromMax y ≤ fromMax y ⊔ V.shells) _)).trans (hy.shells j),fun j i hi=>?_,fun j i h x he=> hQ j x ((hy.beta j).trans he) i h⟩
    exact le_trans (show 1≤ W.growth j from le_sup_left) (hy.growth j)
end ConcertZ
end YM.PhysicalNext.Repeat.Mallow
