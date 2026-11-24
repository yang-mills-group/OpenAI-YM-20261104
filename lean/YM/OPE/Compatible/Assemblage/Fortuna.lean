import YM.OPE.Compatible.Assemblage.Palette
import YM.OPE.Height
/-!
# Consistent per-insertion comparison. Keep Ward phase copy independent, full
meter estimate, with the calibrated compensator on the actual path
through all stamps. Upgrades the bound retained in M/South/Commune.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Relay
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {N p k j d:ℕ}{V:Type}[Fintype V][DecidableEq V]{P:Ensemble V}
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
variable (h:Scrim C W u ψ φ δ ζ r D)(H:C.Makes)
variable (M: Extra.Histories.Music (C.labels.level d) C.path N p) (hL:Sung (C.localSection d) C.path N p C.params W (C.ref d) M)
    (hp:∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol (C.localSection d) C.path N p i (D N p i hi) (M.tone (i+1)) (M.tone i) (ψ i))
variable (y:Coefficient (C.labels.level d) (C.side k p))
set_option quotPrecheck false
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "R"=> C.path.rep N p
-- Retreat data independent w, remembers bias. sibling unreplaced can use its untranslated gross.
structure Fortune (C:Family G)(V: Bid.Worth)(ψ:ℕ→ℝ)
    (N p k d:ℕ)(y:Coefficient (C.labels.level d) (C.side k p))(c₀ Q E:ℝ)(X:Extra.Histories.Music (C.labels.level d) C.path N p)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) (A :∀ i:ℕ, Solo (C.labels.level d) C.path p i): Prop where
   oldest : C.ref d≤k
   limit : k≤N
   ready:A k= pair C.path N p X y c₀
   fit : Challenge (C.localSection d) C.path N p C.params V X (C.ref d) k A
   tracks : ∀ i,C.ref d≤ i →∀ h:i<k, Accord (C.localSection d) C.path N p X (ψ i) i (D N p i (h.trans_le limit)) (A (i+1)) (A i)
   basis b : ((A k).bar X b).x=y.x+(X.tone k).index b
   bank i : C.ref d≤ i → i≤ k→ let b:=-(A (C.ref d)).a; let v:= A i; Bid.gainChart C.path k i*(v.cost X b+(C.labels.level d).coeffSize (v.bar X b).x) ≤ E
   risen : 0<Q
   credit : (C.labels.level d).coeffSize y.x+c₀ ≤ Q ∧ Q≤ E
include h H hL hp
lemma fortuned {c₀ Q E:ℝ}(hk:C.ref d≤ k)(hN:k≤N)(ht:y.Format 0 C.params (R k))(hh:y.remBound 0 (R k) (Real.sqrt ((T).levels.clock.forcedAllowance k)) c₀)(ha: 0<Q)(hv:(F).coeffSize y.x+c₀≤ Q)(he:4*(1+(C.path.levels.params k).columns)*Q ≤ E): ∃ A, Fortune C W ψ N p k d y c₀ Q E M D A:=by
   have H0 : Q ≤ E:= by refine le_trans (le_mul_of_one_le_left ha.le ?_) he; linarith only [(C.path.levels.params k).columns_ge]
   obtain ⟨A,hA,hx',hb,hc',hq',hp',h''⟩:= antilles Y! T N p C.params W M (D N p) ψ le_rfl hk hN H.wilson hL
      (fun i hu hx=> ⟨h.listens d N p i hu (hx.trans_le hN),hp i hu (hx.trans_le hN)⟩) (y) ht hh hv h.costs.cost h.costs.back
   exact ⟨A,hk,hN,hA,hx',hb,fun i=> (hc' i).1,fun i hi hv=>le_trans (h'' i hi hv) he,ha,hv,H0⟩
omit h H hp
section
variable {c₀ Q E:ℝ} {A :∀ i:ℕ,Solo (C.labels.level d) C.path p i}
    (hF:Fortune C W ψ N p k d y c₀ Q E M D A)
local notation "b"=> (A ℓ).a
-- general permit geometry after launch from aligned m. (Z Guide instance)
include hF
lemma travels {w:ℕ→ℝ} (X:(C.labels.level d).Coeff)(χ:ℕ→ℝ)(hW:∀ i,ℓ ≤ i→i ≤ k→w i*‖alto C.path i d‖*((A i).cost M X+(F).coeffSize ((A i).bar M X).x) ≤ χ i):Club T C.params Y! χ ψ ℓ k N p w D (fun i=> (A i).bar M X) (fun i=>(A i).cost M X) hF.limit :=by
   refine ⟨fun i hi ht=>?_,hW,fun i hi ht=> ?_⟩
   · exact (keys Y! T N p C.params M X (hF.fit.chairs i hi ht) (hL.earned i hi (ht.trans hF.limit))).2
   obtain ⟨v,hv,hy⟩:= (hF.tracks i hi ht).plays; exact ⟨(hF.fit.ships i hi ht).debt X, v,hv, hy X⟩
lemma produces {i:ℕ} (hi:ℓ ≤ i) (hk:i≤k) : (A i).cost M (- b)+(F).coeffSize ((A i).bar M (- b)).x ≤ E:=by
   have he:= hF.bank i hi hk; have hv: 1 ≤ Bid.gainChart C.path k i:= Real.one_le_exp (mul_nonneg (by norm_num) (sub_nonneg.mpr ((YM.OPE.scale_mono _).monotone hk)))
   exact le_trans (le_mul_of_one_le_left (add_nonneg (rem_nonneg (((keys Y! T N p C.params M (- b) (hF.fit.chairs i hi hk) (hL.earned i hi (hk.trans hF.limit))).2).2)) (Work.G08.size_nonneg ..)) hv) he -- right.left notation
lemma bias_price (hh:y.remBound 0 (R k) (Real.sqrt ((T).levels.clock.forcedAllowance k)) c₀) : (F).coeffSize ((M.tone k).index b) ≤ 2*E:=by
    let j:= (A k).bar M (- b); have hx:j.x=y.x+(M.tone k).index (- b):= hF.basis (- b)
    have hu: (F).coeffSize j.x ≤ E:=by
       have hs:= produces M hL y hF hF.oldest le_rfl; have hj:= rem_nonneg ((keys Y! T N p C.params M (- b) (hF.fit.chairs _ hF.oldest le_rfl) (hL.earned _ hF.oldest hF.limit)).2.2)
       linarith only [hs,hj]
    have hb : (F).coeffSize y.x ≤ E:= (le_add_of_nonneg_right (rem_nonneg hh)).trans (hF.credit.1.trans hF.credit.2)
    rw [map_neg] at hx; have hg:(M.tone k).index b=y.x+(-j.x):=by rw [hx]; abel
    rw [hg]; apply (Size.add ..).trans; rw [show (F).coeffSize (-j.x)= (F).coeffSize j.x from by simp [Labels.Frame.coeffSize]]; linarith only [hu,hb]
lemma expo_on (X:(C.labels.level d).Coeff)(ht:y.Format 0 C.params (R k))(hφ:y.remBound 0 (R k) (Real.sqrt ((T).levels.clock.forcedAllowance k)) c₀):
    let P:= (A k).bar M X; let v:=(M.tone k).plays X
    P.exponentialEntry 0 Y! (R k)=y.exponentialEntry 0 Y! (R k)+v.exponentialEntry 0 Y! (R k)∧ profile (C.path.rep N p k).activities P.forced=profile (C.path.rep N p k).activities y.forced + profile (C.path.rep N p k).activities v.forced:=by
    -- from baseline commune; not re-selecting P
    let X':=M; let T':= T; let I:=M.tone k; let v:= (A k).bar M X; rw [hF.ready]
    let t':= pair T' N p M y c₀; let b':= t'.a; let Q':= t'.sil; have he:=hL.earned k hF.oldest hF.limit; have hz(w):=(he.earns w).2; let q w:=(I.plays w).exponentialEntry 0 Y! (R k); have hQ:IsLinearMap ℂ q:=expoLinear I.plays I.charge he.book hz
    let r w:=profile (C.path.rep N p k).activities (I.plays w).forced; have hq:IsLinearMap ℂ r:=inkL I.plays I.charge he.book hz
    dsimp only
    constructor
    · change (beside Q' (I.plays (b'+X))).exponentialEntry 0 Y! (R k)=_
      rw [show (beside Q' (I.plays (b'+X))).exponentialEntry 0 Y! (R k)=_ from duo_exp Y! ((presentation ht hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+X)), show Q'.exponentialEntry 0 Y! (R k)=_ from duo_exp Y! hφ (hz (-b'))]; change _+q (-b')+q (b'+X)=_+q X
      rw [hQ.map_add, show q (-b')= -q b' from (IsLinearMap.mk' q hQ).map_neg b']; abel
    change profile _ (beside Q' (I.plays (b'+X))).forced= _
    rw [show profile (C.path.rep N p k).activities (beside Q' (I.plays (b'+X))).forced=_ from duo_profile ((presentation ht hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+X)), show profile (C.path.rep N p k).activities Q'.forced= _ from duo_profile hφ (hz (-b'))]; change _+r (-b')+r (b'+X)=_+r X -- `r` shadow
    rw [hq.map_add,show r (-b')= -r b' from (IsLinearMap.mk' r hq).map_neg b']; abel
end
end YM.MergeProof.Ribbons.ManyCopies.Stem
