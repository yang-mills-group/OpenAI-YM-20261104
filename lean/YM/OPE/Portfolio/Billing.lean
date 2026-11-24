import YM.OPE.Portfolio.Solemn
import YM.OPE.Height
/-!
# Meter store through a Capture (possibly much further than a parent geometry)

Two variants: debit selection with signed UNIT, and no untouched growth at grade zero.
Support cohorts independent at this stage. Later permit Compass operations only
using the SAME family of slots / meters; important for not paying off-geometry halo.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Extra.Histories.Relay
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{H:History G}{N p i j b k d :ℕ}{F:Labels.Frame G d}
local notation "T"=> H.rep N p
set_option quotPrecheck false
variable {W:Worth}{L:Hol G}{D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
variable (B:SectionData F){X:Coefficient F (H.S.side i p)}{Y:Cup (H.rep N p i)}
    {E:Extra.Histories.Music F H N p}{v:F.Coeff}{ζ ψ w:ℕ→ℝ}{A R t:ℝ}{x:Site (H.S.side i p)}
local notation "w!"=> (H.levels.params i).columns
local notation "s"=> kappa H i
-- persisted Time footprint data
structure Sessions (E: Music F H N p)(b:ℕ)(L:Hol G)(W:Worth)(ψ:ℕ→ℝ)(D:∀ N p i:ℕ,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i)) : Prop where
   sung: Sung B H N p L W b E
   songs i: b ≤ i →∀ hn:i<N, Carol B H N p i (D N p i hn) (E.tone (i+1)) (E.tone i) (ψ i)
   stamps i: b ≤ i →∀ hn:i<N, ∃ η:ℝ, Tones B H N p L (ψ i) i η (D N p i hn)
   credit:roomCost H.levels W
   brine: Bank W H.levels

private lemma rootPrice (r:Levels G)(i:ℕ): 0 ≤ (r.params i).columns:= zero_le_one.trans (r.params i).columns_ge
-- get buy origin postage *both* with EXACT pair, and receipts along family at fixed b for any z where purchase possible
variable (h:H.Selected)(Hc:Sessions B E b L W ψ D)(hb:b ≤ i) (hi:i≤N) (hr:X.Format 0 L (H.rep N p i))(hv:X.remBound 0 (H.rep N p i) (kappa H i) t) (hx:F.coeffSize X.x+t ≤ A)
    (hp:4*(1+(H.levels.params i).columns)*A ≤ R)
include h Hc hb hi hr hv hx hp
local notation "Δ"=> (E.tone i)
lemma commit : ∃ Q:∀ i:ℕ,Relay.Solo F H p i,
    Q i=Relay.pair H N p E X t ∧ Challenge B H N p L W E b i Q ∧ (∀ j:ℕ,b ≤ j→∀ hm:j < i, Accord B H N p E (ψ j) j (D N p j (hm.trans_le hi)) (Q (j+1)) (Q j)) ∧
    let v:= -(Q b).a; F.coeffSize ((E.tone i).index v)≤ 2*R ∧
     ∀ j,b≤ j→ j ≤ i→ (Q j).cost E v+F.coeffSize ((Q j).bar E v).x ≤ R:=by
    obtain ⟨Q,hQ,hS,hE,hσ,-,hF,hL⟩:= antilles B H N p L W E (D N p) ψ le_rfl hb hi h Hc.sung (fun j he hm=>⟨Hc.stamps j he _,Hc.songs j he _⟩) X hr hv hx Hc.credit Hc.brine
    let v:= -(Q b).a; have ha : ∀ j,b ≤ j→ j ≤ i→ (Q j).cost E v+F.coeffSize ((Q j).bar E v).x ≤ R:=by
       intro j hj he; have hV := (hL j hj he).trans hp; let y:=F.coeffSize ((Q j).bar E v).x; let z:=(Q j).cost E v; have hk:0 ≤ z:= rem_nonneg ((keys B H N p L E v (hS.chairs j hj he) (Hc.sung.earned j hj (he.trans hi))).2.2); exact (le_mul_of_one_le_left (add_nonneg hk (Work.G08.size_nonneg ..)) (Real.one_le_exp (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/8) (sub_nonneg.mpr ((OPE.scale_mono H.S).monotone he))))).trans hV
    refine ⟨Q,hQ,hS,hE, ?_⟩; refine ⟨?_,ha⟩
    let x:=((Q i).bar E v).x; have hp_:0 ≤ t:= rem_nonneg hv; have he : F.coeffSize X.x ≤ R:= by
       have hv: 1 ≤ (H.levels.params i).columns:= (H.levels.params i).columns_ge; have ht : F.coeffSize X.x ≤ A:= le_trans (le_add_of_nonneg_right hp_) hx; have hα:0≤A:=(Work.G08.size_nonneg ..).trans ht; exact ht.trans ((le_mul_of_one_le_left hα (by linarith only [hv])).trans hp)
    have hg: F.coeffSize x ≤ R:= (le_add_of_nonneg_left (show 0 ≤ (Q i).cost E v from rem_nonneg ((keys B H N p L E v (hS.chairs i hb le_rfl) (Hc.sung.earned i hb hi)).2.2))).trans (ha i hb le_rfl)
    change F.coeffSize ((Δ).index v) ≤ _; rw [show (Δ).index v=x + -X.x from by rw [show x=_ from (hσ v).1]; abel]; apply (Size.add ..).trans; rw [show F.coeffSize (-X.x)=F.coeffSize X.x by simp [Labels.Frame.coeffSize]]; linarith only [he,hg] -- syntax local Δ.index

omit h Hc hb hi hr hv hx hp
-- imprint at beginning in one dictionary
namespace Sessions
variable (w':Motion)
include Hc hb hi
lemma reissue {Q:∀ i:ℕ,Relay.Solo F H p i} {v:F.Coeff}{t':ℕ→ℝ} {k:ℕ} (hj:b ≤ k) (he:k ≤ i) (hQ: Challenge B H N p L W E b i Q) (hq:∀ j,b ≤ j→∀ hm:j < i, Accord B H N p E (ψ j) j (D N p j (hm.trans_le hi)) (Q (j+1)) (Q j)) (hκ:∀ j,k ≤ j→ j ≤ i→ (Q j).cost E v+F.coeffSize ((Q j).bar E v).x ≤ t' j) (hT:∀ j,k ≤ j→ j ≤ i→ w j*‖alto H j d‖*t' j ≤ ζ j) (hw:∀ j,k ≤ j→ j ≤ i→ 0 ≤ w j) : let Z:= dualize H N p E b i Q v; Club H L B ζ ψ k i N p w D Z.voice Z.cost hi:=by
    intro Z; refine ⟨fun j hk he=> (keys B H N p L E v (hQ.chairs _ (hj.trans hk) he) (Hc.sung.earned _ (hj.trans hk) (he.trans hi))).2, fun j hx hh=> (mul_le_mul_of_nonneg_left (hκ j hx hh) (mul_nonneg (hw _ hx hh) (norm_nonneg _))).trans (hT _ hx hh), ?_⟩
    intro j hk he; obtain ⟨u,hU,hp⟩:= (hq _ (hj.trans hk) he).plays
    exact ⟨(hQ.ships j (hj.trans hk) he).debt v,u,hU,hp v⟩

-- horizontal header at joined mark
include hr hv
lemma pastel (a : F.Coeff):
    let V:= (Relay.pair H N p E X t).bar E a; let Q := ((E.tone i).plays a)
    V.exponentialEntry 0 B (T i)= X.exponentialEntry 0 B (T i)+Q.exponentialEntry 0 B (T i) ∧
    profile (T i).activities V.forced=profile (T i).activities X.forced+profile (T i).activities Q.forced:=by
    let b:= (Relay.pair H N p E X t); let g:=b.a; let Δ':=(E.tone i); intro V Q; let u':=Δ'.plays; have he:= Hc.sung.earned i hb hi; have hz:= presentation hr hv (he.earns (-g)).1 (he.earns (-g)).2
    constructor
    · let f (x:F.Coeff):= (u' x).exponentialEntry 0 B (T i); have hp:IsLinearMap ℂ f:=expoLinear _ _ he.book fun x=> (he.earns x).2
      have ht:=duo_exp B hz.2 (he.earns (g+a)|>.2); rw [duo_exp B hv (he.earns (-g)|>.2)] at ht; apply ht.trans; change _+f (-g)+f (g+a)=_+f a; rw [hp.map_add,(show f (-g)= -f g from (IsLinearMap.mk' f hp).map_neg _)]; abel
    let f (x:F.Coeff):=profile (T i|>.activities) (u' x).forced; have hp:IsLinearMap ℂ f:=inkL _ _ he.book fun x=> (he.earns x).2
    have ht:=duo_profile hz.2 (he.earns (g+a)|>.2); rw [duo_profile hv (he.earns (-g)|>.2)] at ht; apply ht.trans; change _+f (-g)+f (g+a)=_+f a; rw [hp.map_add,(show f (-g)= -f g from (IsLinearMap.mk' f hp).map_neg _)]; abel
lemma paidPastel {V:Cup (H.rep N p i)}(hh:Mantle H N p i B w' x X Y)(hV:Mantle H N p i B w' x ((E.tone i).plays v) V):
    Mantle H N p i B w' x ((Relay.pair H N p E X t).bar E v) (Y+V):=by
    have hx := pastel B Hc hb hi hr hv v; constructor
    · rw [Cup.home_add,hx.1,hh.prose,hV.prose]; unfold radiant; rw [show ∀ Pq q:Config G (H.S.side i p)→ℂ, stepUp w' x (Pq+q)=stepUp w' x Pq+ stepUp w' x q from fun p q=>funext fun U=> Motion.scalar_add ..,smul_add] -- need use scalar_add
    rw [Cup.leaves_add,hh.key,hV.key]; unfold sunny; rw [hx.2, show ∀ a b:Res G (H.S.side i p), floatUp w' x (a+b)=floatUp w' x a+floatUp w' x b from fun a b=>funext fun _=>funext fun _=> Motion.scalar_add .., smul_add]
end Sessions
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio
