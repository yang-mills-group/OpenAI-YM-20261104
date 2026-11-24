import YM.MergeProof.South.Merman
import YM.OPE.Script.Celeri
import YM.OPE.Script.Legend
/-!
# Record reusable matching witnesses on the single physical core

Return in terms of lattice labels here; quota bound transfers to every
fixed finite rank using `Origins`. Adapted from South/Merman. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{N k m p d:ℕ}
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
open Relay GridApprox
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
structure Album (C:Family G)(N k p d:ℕ) where
   song : Extra.Histories.Music (C.labels.level d) C.path N p
   mark_ : C.label d
   pillar (i:ℕ): Coefficient (C.labels.level d) (C.side i p)
   cost : ℕ→ℝ
   ear : (C.labels.level d).Index→ C.label d
   bill : (C.labels.level d).Index→ℕ→ℝ
   wing (j:(C.labels.level d).Index)(i:ℕ): Coefficient (C.labels.level d) (C.side i p)
   blend : (C.labels.level d).Index→ℂ
structure Asked (Q:Coefficient (C.labels.level d) (C.side k p))(E w:ℝ)(B:Album C N k p d) (e:k≤N) : Prop where
   passage : Club T C.params Y! (ζ d) ψ m k N p (stair φ (2*w) m) D B.pillar B.cost e
   joints : profile (R k).activities (B.pillar k).forced=profile (R k).activities Q.forced+profile (R k).activities ((B.song.tone k).plays (-B.mark_)).forced
   pitch : (B.pillar k).exponentialEntry 0 (C.localSection d) (R k)= Q.exponentialEntry 0 (C.localSection d) (R k) + ((B.song.tone k).plays (-B.mark_)).exponentialEntry 0 (C.localSection d) (R k)
   cost : (F).coeffSize ((B.song.tone k).index B.mark_) ≤ 2*E
   desks j: Embrace (ζ:=ζ) (φ:=φ) (ψ:=ψ) (D:=D) C N k m p d (Size.axis F j) B.song 1 (8*E*w) (B.wing j) (B.bill j) (B.ear j) e
structure Lyrics (X:Extra.Histories.Music (C.labels.level d) C.path N p)(W:Worth)(ψ:ℕ→ℝ)(D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)):Prop where
    entries : (s!).entries=(X.draft T).inits
    sung : Sung Y! T N p C.params W ℓ X
    bells : ∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol Y! T N p i (D N p i hi) (X.tone (i+1)) (X.tone i) (ψ i)
    coins : ∀ b',profile (R N).activities ((X.tone N).plays b').forced=hook (R N).activities (R N).p.threshold (booster Y! (R N) 0 b')
structure Chant (W:Worth) (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))(ζ : ℕ→ℕ→ℝ)(ψ φ:ℕ→ℝ)(Q:Coefficient (C.labels.level d) (C.side k p))(E:ℝ)(B:Album C N k p d) (e:k≤N) : Prop where
    lyrics : Lyrics B.song W ψ D
    window (w:ℝ)(m:ℕ) (ht:C.ref d ≤ m)(hk:m ≤ k)(hw:0<w)(hp:32*(1+(T|>.levels.params k).columns)*w * ‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2): Asked (C:=C) (ζ:=ζ) (ψ:=ψ) (D:=D) (φ:=φ) (m:=m) Q E w B e
    blended : B.mark_=∑ i,B.blend i • B.ear i
    worth : (∑ i,‖B.blend i‖) ≤ 4*E
variable (H:C.Makes)(h: Scrim C W u ψ φ δ ζ r D)
local notation "q"=> (Size.axis (C.labels.level d))
include H h
lemma chant (Q:Coefficient (C.labels.level d) (C.side k p)){c t E w:ℝ} (ht:C.ref d ≤ m)(hk:m ≤ k)(hN:k ≤ N)(hr:Q.Format 0 C.params (R k))(hb: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) t) (ht' : (F).coeffSize Q.x+t ≤ c)(hc: 0 < c)(hE:4*(1+(T|>.levels.params k).columns)*c ≤ E)
    (hw: 0 < w)(hP:32*(1+(T|>.levels.params k).columns)*w * ‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2): ∃ B:Album C N k p d, Chant W D ζ ψ φ Q E B hN:=by
    obtain ⟨X,hX,hL,hY,hθ⟩:= (h.costs.aim d N p (ht.trans (hk.trans hN))).lyrics
    let Q':=(T|>.levels.params k).columns; have hQ: 1 ≤ Q':= (C.path.levels.params k).columns_ge; let E':=4*(1+Q'); have hp:0 < E:= lt_of_lt_of_le (show 0 < 4*(1+Q')*c by positivity) hE
    obtain ⟨P,x,b,hK⟩:= commune3 C N k p d H X h Q t c E (ht.trans hk) hN hL hY hr hb ht' hE hc
    choose Z g e hΨ using fun i=> embrace3 C N k p d H (q i) X h 1 E' (ht.trans hk) hN hL hY (Size.size_axis F i).le (le_of_eq (mul_one _)) zero_lt_one
    let A (s:(F).Index→ℂ):Album C N k p d:=⟨X,b,P,x,e,g,Z,s⟩
    have hv(s t' i)(he:C.ref d ≤ i)(ht:i ≤ k)(hw:0<t')(hc:32*(1+Q')* t'*‖alto T i d‖*(E/gainChart T k i) ≤ ζ d i/2): Asked (C:=C) (ζ:=ζ) (ψ:=ψ) (D:=D) (φ:=φ) (m:=i) Q E t' (A s) hN:=by
       obtain ⟨hm,hh,ho,hU⟩:=hK i (2*t') he ht (mul_pos zero_lt_two hw) (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 32*(1+Q') from by linarith only [hQ]) hw.le) (norm_nonneg _)) (div_nonneg hp.le (Real.exp_pos _).le)) hc)
       exact ⟨hm,hU,ho,hh,fun j=> hΨ j i _ he ht (by positivity) (le_trans (le_of_eq (b:=32*(1+Q')*t' * ‖alto T i d‖*(E/gainChart T k i)) (by unfold E';ring)) hc)⟩
    have ht'(j):= (hv 0 w m ht hk hw hP).desks j; obtain ⟨s,hs,hy⟩:= modems C N k p d b X e (fun i=>(ht' i).bias)
    refine ⟨A s,⟨⟨hX,hL,hY,hθ⟩,fun w m=>hv s w m,hs,?_⟩⟩
    have hz:= (hv s w m ht hk hw hP).cost
    change (F).coeffSize ((X.tone k).index b) ≤ 2*E at hz; change (F).coeffSize s ≤ _; linarith only [hy,hz]
namespace Album
variable {H h}
def legacy (A:Album C N k p d): C.label d:= (C.factory d N p).terminal A.mark_
def aids (A:Album C N k p d) (i:(F).Index) : C.label d:= (C.factory d N p).terminal (A.ear i)
def body (A:Album C N k p d): Config G (C.S.side k p) → ℂ:= ∑ i, (-A.blend i) • Accent.lens C N k p d (Size.axis (C.labels.level d) i)
omit H h in
lemma literal {B: Album C N k p d} {Q:Coefficient (C.labels.level d) (C.side k p)}{E:ℝ}{hz:k≤N}(hB: Chant W D ζ ψ φ Q E B hz): B.legacy=∑ i,B.blend i • B.aids i:=by unfold legacy aids; rw [hB.blended,map_sum]; simp_rw [map_smul]
end Album
namespace Chant
variable {Q:Coefficient (C.labels.level d) (C.side k p)} {B:Album C N k p d}{t c E w : ℝ}
variable (J:ℕ) (hV : Stock.Tabs.opens C.path.levels 1 J m) {hk:m≤k}{hN:k<N}
local notation "o"=> fun i=> Mix.camp C p J i
local notation "V"=> Site (C.side J p)
local notation "Bt"=> Stock.census V
local notation "u'"=> hands C p J
local notation "α'"=> march (fun _ : V=> w) φ m k
local notation "h!"=> center C.S p (hV.1.trans (hk.trans hN.le)) 0
variable (f:Config G (C.side N p)→ℂ) (f₀:Config G (C.side k p)→ Marker.Poly (Stock.census (Site (C.side J p))))
    (ht:C.ref d ≤ m) (hh:m ≤ k)(hsM:m<k)(hn:k<N) (hR: GridApprox.room C.path.levels J k (lensScope C d)) (hw:0<w)(hp:0<E)(hP:32*(1+(C.path.levels.params k).columns)*w * ‖alto C.path m d‖*(E/gainChart C.path k m) ≤ ζ d m/2)(hB:Chant W D ζ ψ φ Q E B hn.le)
include H h
lemma request (L:Stock.Tabs C.path.levels) (ht:C.ref d ≤ m) {hk:m ≤ k} (hN:k<N) (hsM:m < k) (hR:GridApprox.room C.path.levels J k (lensScope C d)) (hC:∀ b:C.label d,Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) (C.O N p b 0))
    (hf: Script C.path N p (hV.1.trans hk) hN.le id Finset.univ f₀ (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f)) (ha:Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) f) (hB: Chant W D ζ ψ φ Q E B hN.le)
    (hp:0<E) (hw:0<w)(hP:32*(1+(T|>.levels.params k).columns)*w * ‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2)
    (hZ:Served (R k) (fun i=> radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k d)) f₀ (o k) (α') ((C.path.levels.budget k).supportExponent-3) 1): Next.UVStress.quota C d k N p B.legacy ≤ 2*E∧ (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (f-C.O N p B.legacy 0) ≤ 2*(stakes C J m / w):=by
    obtain ⟨hX,hL,hY,hθ⟩:= hB.lyrics; obtain ⟨hK,hB',hU,hH,hΨ⟩:= hB.window w m ht hk hw hP
    let v':=8*E*w; have h':0<v':=by unfold v'; positivity
    let W₀:= center C.S p (hV.1.trans (hk.trans hN.le)) 0; let n:=lensScope C d; let y i:= lens C N k p d (q i); let r':= backTo T N p hN.le B.body
    have hz(i): Interior (GridApprox.window 0 n) (y i):=visible C N k p d _ H hN.le; let J' := hV.1.trans hk; have hy(i):= quakes C N k m p d H v' (q i) B.song h J L hN ht hk h' (hΨ i) hL hY hθ hV _ hR (hz i)
    obtain ⟨hW,hZc,hσ⟩:=posing C N k p d H J y B.blend J' hN.le B.aids B.legacy n hz (div_nonneg (Real.exp_pos _).le h'.le) hB.worth (Album.literal hB) hC hy hR
    refine ⟨?_,?_⟩
    · unfold Next.UVStress.quota; have hh : (s!).terminal.symm B.legacy=B.mark_:=LinearEquiv.symm_apply_apply ..
      rw [hh, hX,show ((B.song.draft T).inits k B.mark_).x=_ from (hL.earned k (ht.trans hk) hN.le).currents B.mark_]; exact hH
    let S:= stakes C J m/w
    have hPc:W₀.rootTest (C.beta N p) (-r' - C.O N p B.legacy 0) ≤ S:=by
       have he: 0 ≤ stakes C J m/w:=div_nonneg (Real.exp_pos _).le hw.le
       calc
          _ ≤ _ := hσ
          _ = S/2:=by unfold v' S stakes; field_simp; ring
          _ ≤ _ := div_le_self he (by norm_num)
    let V':= -f; have hv:Interior (W₀.chamber 0) V':= by rw [show V'=(-1:ℂ) • f from (neg_one_smul ..).symm]; exact ha.scale _
    let f':=r'-V'; let b'':= -r'-C.O N p B.legacy 0; have hPc' : Interior (W₀.chamber 0) b'':= by unfold b''; rw [show -r'=(-1:ℂ) • r' from (neg_one_smul ..).symm]; exact Next.UVStress.minus ((show Interior _ r' from hZc).scale _) (hC B.legacy)
    change W₀.rootTest (C.beta N p) _ ≤ 2*S
    suffices hy' : W₀.rootTest (C.beta N p) f' ≤ S by rw [show f-C.O N p B.legacy 0=f'+b'' from by unfold f' b'' V'; abel,two_mul]; exact ((seamless H N p).semi W₀ f' b'' (Next.UVStress.minus hZc hv) hPc').trans (add_le_add hy' hPc)
    exact celeri3 C N k m p d H w h L J hV f Q ht (hk:=hk) hN hR hsM f₀ hf E hw hp B.song hL B.pillar B.mark_ B.cost B.wing B.ear B.bill hK hU hB' B.blend hB.blended hΨ hB.worth hW hZ
end Chant
end YM.MergeProof.Ribbons.ManyCopies.Patrol
