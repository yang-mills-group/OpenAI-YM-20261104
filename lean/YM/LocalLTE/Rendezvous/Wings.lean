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
abbrev sumJ (G:Gauge)(v:ℝ)(L:Side) := straw (v/2) L G
abbrev aust :ℝ:= -(1:ℝ)/32
structure ConcertZ (T:Targets s K)(p:ℕ)(δ:ℝ) where -- uniform.Beacon nℓ(T τ); room needed at future.Pulse.Constant.
    azi :ℕ→ℕ→ℕ
    kap:ℕ→ℕ→ℕ
    bbase :ℕ→ℕ→ℕ
    amp :ℕ→ℕ→ℕ
    strength :ℕ→ℕ→ℝ -- e(
    bill j i : StepStages j i →δ ≤ strength j i ∧ 0 < strength j i ∧ strength j i < (p:ℝ)/100∧ strength j i< (3/8:ℝ)*amp j i∧ East.stagnate (amp j i) (T j i).halo < bbase j i

namespace ConcertZ
section upfront
variable (T:Targets s K) {Γ:ℝ}{Q:ℕ}
-- choose Watts & proves ∀l k.Width.Early Φ.dim; α and K predictable before floors; can be supplied reverse order i stage.Fe.Cu
variable (d:ℕ→ℕ→ℕ)(e:ℕ→ℕ→ℝ)(hE:∀ j i, Γ ≤ e j i ∧ 0<e j i ∧ e j i< Q/100) -- nat division annotation?
variable (p:Expenses T)
def Forecast (d:ℕ→ℕ→ℕ)(p':Expenses T)(H:ConcertZ T Q Γ)(κ:ℝ)(W:ℕ→ℕ):Prop:=
    ∀ j i,StepStages j i→∀ L:Side,W j ≤ L.val→∀ α:ℝ,∀ o: Target.Order G α,∀ μ:ℝ,0<α→0<μ→∀ᶠ x in atTop,Fan.Manifest (T j i) L o (p' j i) Chi.canonical (s.profile i).order (s.profile i).power Q (H.amp j i) (H.bbase j i) (d j i) (H.azi j i) (H.kap j i) κ (H.strength j i) Mallow.aust x μ
-- Explicit.H Contains Work.A.Lengths.Manifest mesh no upper limit. put parameters later allocation.
variable (hr:∀ j i,3/8+(T j i).rate < Mallow.aust) {κ v:ℝ} (hk:Reliable G κ v)
include hr hk hE
lemma springL : ∃ H:ConcertZ T Q Γ,H.strength=e ∧ ∃ W, Forecast T d p H κ W :=by
    have hp(j i:ℕ):∃ q:ℕ,e j i< (3/8:ℝ)*q:=by obtain ⟨m,h⟩:= exists_nat_gt (8*(e j i)); exact ⟨m,by linarith only [hE j i|>.2.1,h]⟩
    choose y h using hp; let b j i:= East.stagnate (y j i) (T j i).halo +1
    have hα(j i:ℕ):= Fan.EarnStep (T j i) (p j i) Mallow.aust (hr j i) (by norm_num [Mallow.aust]); choose w hZ using hα
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
def titles (j i:ℕ)(x:ℝ) : Prop:=let m:= (s.profile i); let α:= T.azi j i; let K:= T.kap j i
    let L:= D.L j; let μ:= R.μ j i; let Y:= betaF G x L; let e:= T.strength j i; let b:=T.bbase j i
    (∃ g,Payments.Rates (radiusB x) (sumJ G μ L x) (straw μ L G x) (Fan.phaseP (p j i|>.earn) b (b*radiusB x)*Y^aust+Y^aust) g)∧ (sumJ G μ L x≤ Blush.glyph x* Y^(-e))∧ (Fan.Manifest (X j i) L (R.o j i) (p j i) Chi.canonical m.order m.power Q (T.amp j i) b (d j i) α K κ e aust x μ)
    -- crop remap Glow.Burn new.V.Also baselining p^ν. Unit ratios later when sparsity/cutoffs booked.
structure CalendarQ (V:Delays Θ):Prop where
   shells j i : StepStages j i → 32*(1+T.bbase j i) ≤ V.shells j
   growth j i : StepStages j i → 1≤ V.growth j
   stamp j i : StepStages j i→∀ x:ℝ,V.betaEntry j≤x→ titles R d T κ j i x
variable {m:ℕ→ℕ}(hF:T.Forecast X d p κ m)(ht:∀ j,m j≤(D.L j).val)
include hF ht
lemma eventsQ (j i:ℕ)(hi:StepStages j i):∀ᶠ x:ℝ in atTop, titles R d T κ j i x:=by
    let t:=T; let a:=u j i; let μ:=R.μ j i; let e:= T.strength j i; let L:=D.L j; let X':= fun x=>betaF G x L
    have hz:T=T:=rfl; have hp:0<a:= (R.consumes _ _ hi).1; have hU:0<μ:= (R.consumes _ _ hi).2.1
    have hc:=hF _ _ hi L (ht _) a (R.o j i) μ hp hU
    have he(x:ℝ): straw μ L G x=2*lauge L (μ/16) x 1 G:= by unfold straw lauge; ring_nf
    have hh(x:ℝ): sumJ G μ L x=2*lauge L (μ/16) x (1/2) G:=by unfold sumJ straw lauge; ring_nf
    let b:=T.bbase j i; let μ₀(x):= Fan.phaseP (p j i|>.earn) b (b*radiusB x)
    have hk:Rate G L 0 μ₀:=by
       have hu:Rate G L 0 (fun x=>(ballCost (b*radiusB x):ℝ)):= by simpa only [Nat.add_zero] using Census.width_rate G L b 0 -- ambiguity.
       exact (Rate.const 1).add (hu.mul_right _)
    let F x:= μ₀ x*(X' x)^aust+(X' x)^aust; have hA:Rate G L aust F:=by unfold F; exact Rate.add (show Rate _ _ aust _ from (by simpa only [zero_add] using! (hk.mul (Rate.power (a:=aust))))) Rate.power
    filter_upwards [hc,mingle (G:=G) L F (show 0<μ/16 by positivity) zero_lt_two (by norm_num [aust]: Mallow.aust <0) hA,Blush.efferv (G:=G) (L:=L) (half_pos hU) (-e-1) (-e) (by linarith only), Delay.shift_pos G L] with x hc hx ht hp
    have hX:0 ≤ F x:=by unfold F μ₀ Fan.phaseP; have hp:0 < X' x:= hp; positivity -- Aust
    let e':=sumJ G μ L x
    obtain ⟨β,hβ⟩:=hx (straw μ L G x) (F x) (mul_nonneg zero_le_two (Real.exp_pos _).le) hX le_rfl (he x).le
    refine ⟨⟨β,(hh x).symm ▸ hβ⟩,?_,hc⟩
    let b:=Blush.glyph x; have hx: b⁻¹*e' ≤ X' x^(-e):= (le_abs_self _).trans ht
    change e' ≤ b*(X' x ^ (-(K' j i))); rw [mul_comm]; exact (div_le_iff₀ (Blush.glyphpos x)).1 ((show e'/b=_ from div_eq_inv_mul ..).trans_le hx) -- κ rewrite issue
-- Delays.Roll.H.Forecasts.Price.W.Width.
lemma treasuryQ (V:Delays Θ): ∃ W:Delays Θ,DelayLe V W∧ ∀ Y:Delays Θ,DelayLe W Y→ T.CalendarQ R d κ Y:=by
    obtain ⟨x,-,hx,hQ⟩:=collect_upper V.betaEntry _ fun j=>eventually_transitions j _ _ (eventsQ R d T κ hF ht j)
    let y j i:=32*(1+T.bbase j i); let W:Delays Θ:={V with betaEntry:=x,shells:=fromMax y ⊔ V.shells,growth:= (fun _=>1)⊔V.growth}; refine ⟨W,⟨hx,le_rfl,le_sup_right,le_sup_right⟩,fun Y hy=>?_⟩
    refine ⟨fun j i hi=> ((le_fromMax y hi).trans (show fromMax y j ≤ W.shells j from (le_sup_left : fromMax y ≤ fromMax y ⊔ V.shells) _)).trans (hy.shells j),fun j i hi=>?_,fun j i h x he=> hQ j x ((hy.beta j).trans he) i h⟩ -- DelayLe fields
    exact le_trans (show 1≤ W.growth j from le_sup_left) (hy.growth j) -- order
end ConcertZ
end YM.PhysicalNext.Repeat.Mallow
