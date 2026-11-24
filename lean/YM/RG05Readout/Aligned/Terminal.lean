import YM.RG05Readout.Aligned.Tune
import YM.OPE.Sweep.Camp
/-!
# Volume-free physical discrepancy estimate after labelled match

Sharpen `bequeathed` for ANY of our matches read in this way (bind inputs,
use actual Challenge bounds; the final comparison below with `lens` follows
that of `MergeProof.South.Merman`). Not constructing the OPE by a seminorm
best-fit. Not comparing absolute-value vacuum partition errors, which in
general here would spend volume. The point is to issue *the very same*
matched label read by the actual step in all copies through the terminal cell.
Use the complete Served representation and denominator. The repayment after
taking the replication root is at levels J (cell), m (terminal budget
level), which may be chosen independent of N,k,p (e.g. for sufficiently far
collars with support/test costs fixed in advance).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Aligned.Pickup
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction
open MergeProof Exponential Overlay Accent MergeProof.Float Ribbons.ManyCopies.Cadet.Studio PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
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
variable (f:Config G (C.side N p)→ℂ) (Q:Coefficient (C.labels.level d) (C.side k p)) {c t E:ℝ}
include H h L
local notation "xp"=> C.path.levels.params k
set_option maxHeartbeats 800000 in
lemma root_cost {M:Extra.Histories.Music (C.labels.level d) C.path N p}
    {A:∀ i:ℕ,Relay.Solo (C.labels.level d) C.path p i} {hc:Committed C N p d W ψ D M}
    (hov:Pickup C M ψ D hc k Q t E A) (hp:0<E) (ht:C.ref d ≤ m) {hk:m ≤ k} (hN:k<N) (hR:GridApprox.room C.path.levels J k (lensScope C d)) (hC:∀ b:C.label d,Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) (C.O N p b 0))
    (hf :Continuous f)(ha:Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) f)
    (hw: 0 < w)(hP:32*(1+(T|>.levels.params k).columns)*w * ‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2)
    (hZ:Served (R k) (fun i=> radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k d)) (gust T N p N (birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f)) k hN.le) (o k) (α') (C.path.levels.budget k).supportExponent 1): let b:= (C.factory d N p).terminal (A (C.ref d)).a; Next.UVStress.quota C d k N p b ≤ 2*E∧ (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (f-C.O N p b 0) ≤ 2*(stakes C J m / w):=by
    let X:=M
    have hX:=hc.origin; have hL:=hc.sessions.sung; have hY:=hc.sessions.songs; have hθ:=hc.reborn
    let Q':=(T|>.levels.params k).columns; have hQ: 1 ≤ Q':= (C.path.levels.params k).columns_ge
    let L':= gainChart T k m; have hξ:0 < L':= Real.exp_pos _
    let a':= 2*w; let v' := 8*E*w; have h':0 < v':=by unfold v'; positivity
    let b:= (A (C.ref d)).a
    let Z:=dualize T N p X ℓ k A (-b); let P:=Z.voice; let x:=Z.cost
    have hK:= declare hov h a' (mul_pos (by norm_num) hw) ht hk (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 32*(1+Q') from by linarith only [hQ]) hw.le) (norm_nonneg _)) (div_nonneg hp.le hξ.le)) hP)
    have hH:= hov.size_bound H
    have ⟨hU,hB⟩:(P k).exponentialEntry 0 Y! (R k)= Q.exponentialEntry 0 Y! (R k) + ((X.tone k).plays (-b)).exponentialEntry 0 Y! (R k)∧ profile (R k).activities (P k).forced=profile (R k).activities Q.forced+profile (R k).activities ((X.tone k).plays (-b)).forced := by
       have he:P k=(pair T N p M Q t).bar M (-b) := congr_arg (fun s=>s.bar M (-b)) hov.starts
       rw [he]; exact Sessions.pastel Y! hc.sessions hov.admissible hN.le hov.opens hov.funds _
    let B:= (s!).terminal b; let I:=Option (F).Index
    let q:= Size.axis F; have he(i):= embrace C N k m p d H v' (q i) X h 1 (4*(1+Q')) ht hk hN.le hL hY (Size.size_axis F i).le (by rw [mul_one]) zero_lt_one h' (le_trans (le_of_eq (b:=32*(1+Q')*w * ‖alto T m d‖*(E/gainChart T k m)) (by unfold v';ring)) hP)
    choose Z g e hΨ using he; obtain ⟨s,hs,hy⟩:=modems C N k p d b X e (fun i=>(hΨ i).bias); have hs'(i:(F).Index):0 ≤ ‖s i‖:= norm_nonneg _; have hβ:(∑ i,‖s i‖)≤4*E:=by linarith only [hH, (show ∑ i,‖s i‖≤ _ from hy)] -- edit
    let W₀:= center C.S p (hV.1.trans (hk.trans hN.le)) 0; let b' i:=(s!).terminal (e i); let n:=lensScope C d; let y i:= lens C N k p d (q i); let ℓ':= ∑ i,(-s i) • y i; let r':= backTo T N p hN.le ℓ'
    have hz(i): Interior (GridApprox.window 0 n) (y i):=visible C N k p d _ H hN.le; let J' := hV.1.trans hk; have hy(i):= quakes C N k m p d H v' (q i) X h J L hN ht hk h' (hΨ i) hL hY hθ hV _ hR (hz i)
    have hM : B=∑ i,s i • b' i:=by unfold B; rw [hs,map_sum]; simp_rw [map_smul]; rfl
    obtain ⟨hW,hZc,hσ⟩:=posing C N k p d H J y (fun i=>s i) J' hN.le b' B n hz (div_nonneg (Real.exp_pos _).le h'.le) hβ hM hC hy hR
    intro u; refine ⟨?_,?_⟩
    · change Next.UVStress.quota _ _ _ _ _ B ≤ _
      unfold Next.UVStress.quota; have ha : (s!).terminal.symm B=b:=LinearEquiv.symm_apply_apply ..
      rw [ha,show (s!).entries=(X.draft T).inits from hX,show ((X.draft T).inits k b).x=_ from (hL.earned k (ht.trans hk) hN.le).currents b]; exact hH
    let S:= stakes C J m/w
    have hPc:W₀.rootTest (C.beta N p) (-r' - C.O N p B 0) ≤ S:=by
       have he: 0 ≤ stakes C J m/w:=div_nonneg (Real.exp_pos _).le hw.le
       calc
          _ ≤ _ := hσ
          _ = S/2:=by unfold v' S stakes; field_simp; ring -- edit
          _ ≤ _ := div_le_self he (by norm_num)
    let V':= -f; have hv:Interior (W₀.chamber 0) V':= by rw [show V'=(-1:ℂ) • f from (neg_one_smul ..).symm]; exact ha.scale _
    let f':=r'-V'; let b'':= -r'-C.O N p B 0; have hPc' : Interior (W₀.chamber 0) b'':= by unfold b''; rw [show -r'=(-1:ℂ) • r' from (neg_one_smul ..).symm]; exact Next.UVStress.minus ((show Interior _ r' from hZc).scale _) (hC B)
    change W₀.rootTest (C.beta N p) _ ≤ 2*S
    suffices hy' : W₀.rootTest (C.beta N p) f' ≤ S by rw [show f-C.O N p B 0=f'+b'' from by unfold f' b'' V'; abel,two_mul]; exact ((seamless H N p).semi W₀ f' b'' (Next.UVStress.minus hZc hv) hPc').trans (add_le_add hy' hPc)
    exact celeri C N k m p d H w h L J hV f Q ht (hk:=hk) hN hR hf E hw hp X hL P b x Z e g hK hU hB s hs hΨ hβ hW hZ
end
end YM.RG05Readout.Aligned.Pickup
