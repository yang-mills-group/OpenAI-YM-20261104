import YM.RG17.Rains
/-! Extend Merman for canonical horizon 0 capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref 0
local notation "F"=> C.labels.level 0
local notation "Y!"=> C.localSection 0
local notation "a!"=> C.S.a
local notation "s!"=> C.factory 0 N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ 0
section
open GridApprox
variable (h:Scrim C W u ψ φ δ ζ r D) (L:Stock.Tabs C.path.levels)
variable (J:ℕ) (hV : Stock.Tabs.opens C.path.levels 1 J m) {hk:m≤k}{hN:k<N}
local notation "o"=> fun i=> Mix.camp C p J i
local notation "V"=> Site (C.side J p)
local notation "Bt"=> Stock.census V
local notation "u'"=> hands C p J
local notation "α'"=> march (fun _ : V=> w) φ m k
local notation "h!"=> center C.S p (hV.1.trans (hk.trans hN.le)) 0
variable (f:Config G (C.side N p)→ℂ) (Q:Coefficient (C.labels.level 0) (C.side k p)) {c t E:ℝ}
include H h L
local notation "xp"=> C.path.levels.params k
set_option maxHeartbeats 800000 in
lemma bequeathZero (hG:G.Simple) (ht:C.ref 0 ≤ m) {hk:m ≤ k} (hN:k<N) (hR:GridApprox.room C.path.levels J k (lensScope C 0)) (hC:∀ b:C.label 0,Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) (C.O N p b 0))
    (hf :Continuous f)(ha:Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) f) (hr:Q.Format 0 C.params (R k))(hb: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) t) (ht' : (F).coeffSize Q.x+t ≤ c)(hc: 0 < c)(hE:4*(1+(T|>.levels.params k).columns)*c ≤ E)
    (hw: 0 < w)(hP:32*(1+(T|>.levels.params k).columns)*w * ‖alto T m 0‖*(E/gainChart T k m) ≤ ζ 0 m/2)
    (hZ:Served (R k) (fun i=> radiant (alto T k 0) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k 0)) (gust T N p N (birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f)) k hN.le) (o k) (α') (C.path.levels.budget k).supportExponent 1):∃ b:C.label 0,Next.UVStress.quota C 0 k N p b ≤ 2*E∧ (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (f-C.O N p b 0) ≤ 2*(stakes C J m / w) ∧ (∀ U:Config G (C.side m p), flags (R m).p.threshold U=∅→ ‖pushTo T N p (hk.trans hN.le) (fun U=>liftVac T N p N U*f U) U / liftVac T N p m U - RG17.send0 C b‖ ≤ 2/w + stakes C J m/w):=by
    obtain ⟨X,hX,hL,hY,hθ⟩:= (h.costs.aim 0 N p (ht.trans (hk.trans hN.le))).lyrics
    let Q':=(T|>.levels.params k).columns; have hQ: 1 ≤ Q':= (C.path.levels.params k).columns_ge
    let L':= gainChart T k m; have hξ:0 < L':= Real.exp_pos _
    have hp:0 < E:= lt_of_lt_of_le (show 0 < 4*(1+Q')*c by positivity) hE
    let a':= 2*w; let v':= 8*E*w; have h':0 < v':=by unfold v'; positivity
    obtain ⟨P,x,b,hK,hH,hU,hB⟩:= commune C N k m p 0 H a' X h Q t c E ht hk hN.le hL hY hr hb ht' hE hc (mul_pos (by norm_num) hw) (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 32*(1+Q') from by linarith only [hQ]) hw.le) (norm_nonneg _)) (div_nonneg hp.le hξ.le)) hP)
    let B:= (s!).terminal b; let I:=Option (F).Index
    let q:= Size.axis F; have he(i):= embrace C N k m p 0 H v' (q i) X h 1 (4*(1+Q')) ht hk hN.le hL hY (Size.size_axis F i).le (by rw [mul_one]) zero_lt_one h' (le_trans (le_of_eq (b:=32*(1+Q')*w * ‖alto T m 0‖*(E/gainChart T k m)) (by unfold v';ring)) hP)
    choose Z g e hΨ using he; obtain ⟨s,hs,hy⟩:=modems C N k p 0 b X e (fun i=>(hΨ i).bias); have hs'(i:(F).Index):0 ≤ ‖s i‖:= norm_nonneg _; have hβ:(∑ i,‖s i‖)≤4*E:=by linarith only [hH, (show ∑ i,‖s i‖≤ _ from hy)] -- edit
    let W₀:= center C.S p (hV.1.trans (hk.trans hN.le)) 0; let b' i:=(s!).terminal (e i); let n:=lensScope C 0; let y i:= lens C N k p 0 (q i); let ℓ':= ∑ i,(-s i) • y i; let r':= backTo T N p hN.le ℓ'
    have hz(i): Interior (GridApprox.window 0 n) (y i):=visible C N k p 0 _ H hN.le; let J':= hV.1.trans hk; have hy(i):= quakes C N k m p 0 H v' (q i) X h J L hN ht hk h' (hΨ i) hL hY hθ hV _ hR (hz i)
    have hM : B=∑ i,s i • b' i:=by unfold B; rw [hs,map_sum]; simp_rw [map_smul]; rfl
    obtain ⟨hW,hZc,hσ⟩:=posing C N k p 0 H J y (fun i=>s i) J' hN.le b' B n hz (div_nonneg (Real.exp_pos _).le h'.le) hβ hM hC hy hR
    refine ⟨B,?_,?_⟩
    · unfold Next.UVStress.quota; have ha : (s!).terminal.symm B=b:=LinearEquiv.symm_apply_apply ..
      rw [ha,show (s!).entries=(X.draft T).inits from hX,show ((X.draft T).inits k b).x=_ from (hL.earned k (ht.trans hk) hN.le).currents b]; exact hH
    let S:= stakes C J m/w
    have hPc:W₀.rootTest (C.beta N p) (-r' - C.O N p B 0) ≤ S:=by
       have he: 0 ≤ stakes C J m/w:=div_nonneg (Real.exp_pos _).le hw.le
       calc
          _ ≤ _:= hσ
          _ = S/2:=by unfold v' S stakes; field_simp; ring -- edit
          _ ≤ _:= div_le_self he (by norm_num)
    let V':= -f; have hv:Interior (W₀.chamber 0) V':= by rw [show V'=(-1:ℂ) • f from (neg_one_smul ..).symm]; exact ha.scale _
    let f':=r'-V'; let b'':= -r'-C.O N p B 0; have hPc' : Interior (W₀.chamber 0) b'':= by unfold b''; rw [show -r'=(-1:ℂ) • r' from (neg_one_smul ..).symm]; exact Next.UVStress.minus ((show Interior _ r' from hZc).scale _) (hC B)
    constructor
    rotate_left
    · intro U hC'; let z:ℂ:= ∑ i, (-s i)*(q i 0)
      have hyq:ℓ'=(fun _=> z):=by unfold ℓ' y; simp_rw [lensZero C N k p H hN.le]; funext U; simp only [z,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      let z':=-z-RG17.send0 C B
      have hy': b''=(fun _=> z') :=by unfold b'' r'; rw [hyq,backTo_const,capZero C N p H hG (ht.trans (hk.trans hN.le)) B]; rfl
      have hc':‖z'‖ ≤ S:=by
         change W₀.rootTest (C.beta N p) b'' ≤ _ at hPc
         have hv: ‖moment (C.beta N p) b''‖ ≤ S:= (by
            have he : ‖moment (C.beta N p) b''‖≤ W₀.rootTest (C.beta N p) b'':=by
                 simpa [Fin.prod_univ_succ] using! W₀.planted (seamless H N p) (fun _ : Fin 1 => 0) (fun i j _=>Subsingleton.elim _ _) (fun _ => b'') (fun _ => hPc')
            exact he.trans hPc) -- syntax
         rw [hy'] at hv; simpa only [moment, MeasureTheory.integral_const,MeasureTheory.probReal_univ,one_smul] using hv
      let mouth:= pushTo T N p (hk.trans hN.le) (fun U=>liftVac T N p N U*f U) U/liftVac T N p m U
      change ‖mouth-RG17.send0 C B‖ ≤ 2/w+ S
      rw [show mouth - RG17.send0 C B = (mouth+z)+z' from by unfold z';ring]; exact (norm_add_le ..).trans (add_le_add (soleCeleri C N k m p H w h L J hV f Q ht (hk:=hk) hN hR hf E hw hp X hL P b x Z e g hK hU hB s hs hΨ hβ hW hZ z hyq U hC') hc')
    change W₀.rootTest (C.beta N p) _ ≤ 2*S
    suffices hy' : W₀.rootTest (C.beta N p) f' ≤ S by rw [show f-C.O N p B 0=f'+b'' from by unfold f' b'' V'; abel,two_mul]; exact ((seamless H N p).semi W₀ f' b'' (Next.UVStress.minus hZc hv) hPc').trans (add_le_add hy' hPc)
    exact celeri C N k m p 0 H w h L J hV f Q ht (hk:=hk) hN hR hf E hw hp X hL P b x Z e g hK hU hB s hs hΨ hβ hW hZ
end
end YM.MergeProof

