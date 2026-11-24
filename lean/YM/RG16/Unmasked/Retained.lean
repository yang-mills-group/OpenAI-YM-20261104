import YM.MergeProof.South.Merman

/-!
# Anti-circular price fixes for comparing bequeathed and exact OPE report

These strengthen individual steps of the **existing proof**
(YM/MergeProof/South/{Commune,Merman}.lean in baseline). Adapt their
selector proofs to export the crucial same-address density equality and the
actual budget on the output, so that we can pay for the difference
from using exact germ coordinates, without rerunning the high-order precision
comparison on a physical volume's worth of copies. Not using any bounds in
other constructions/branches.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)
local notation "R"=> C.path.rep N p
variable (H:C.Makes) {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (o:∀ i:ℕ,V→Site (C.side i p))(s:V→ C.label d)(t:V→Motion)(w:ℝ) {j :ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
variable (L:C.label d)(X:Extra.Histories.Music (C.labels.level d) C.path N p) -- `axis` maybe interf
local notation "yad"=> Extra.Histories.primary (0:Site (C.side k p)) L
local notation "a"=> alto C.path k d
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D)
include H h
lemma retains_cancellation (y : Coefficient (C.labels.level d) (C.side k p))(c₀ : ℝ) (Q E:ℝ)(hK:C.ref d ≤ m)(hk:m ≤ k)(hN:k≤N)(hL: Sung Y! T N p C.params W ℓ X) (hp:∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol Y! T N p i (D N p i hi) (X.tone (i+1)) (X.tone i) (ψ i)) (hχ:y.Format 0 C.params (R k))(hφ:y.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) c₀)(hq:(F).coeffSize y.x + c₀ ≤ Q) (hc:4*(1+(C.path.levels.params k).columns)*Q ≤ E) (hx:0<Q)(hw:0<w)(ht:w*‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2) : ∃ Z g b, Club C.path C.params (C.localSection d) (ζ d) ψ m k N p (fun i=> march (fun _:Unit=>w) φ m i ()) D Z g hN ∧
    (F).coeffSize ((X.tone k).index b) ≤ 2*E ∧ (Z k).exponentialEntry 0 (C.localSection d) (R k)= y.exponentialEntry 0 (C.localSection d) (R k) + ((X.tone k).plays (-b)).exponentialEntry 0 (C.localSection d) (R k)∧ profile (C.path.rep N p k).activities (Z k).forced=profile (C.path.rep N p k).activities y.forced+profile (C.path.rep N p k).activities ((X.tone k).plays (-b)).forced ∧
    (Z k).density 0 (C.localSection d) (R k) = y.density 0 (C.localSection d) (R k) + ((X.tone k).plays (-b)).density 0 (C.localSection d) (R k) ∧ (∀ i,m ≤ i → i ≤ k → g i+(F).coeffSize (Z i).x ≤ E/gainChart T k i):=by
    have hM:=hK.trans hk
    obtain ⟨A,hA,hx',hb,hc',hq',hp',h''⟩:= antilles Y! T N p C.params W X (D N p) ψ le_rfl hM hN H.wilson hL (fun i he hx=> ⟨h.listens d N p i he (hx.trans_le hN),hp i he (hx.trans_le hN)⟩) (y) hχ hφ hq h.costs.cost h.costs.back
    let b:= (A ℓ).a; let y':= -b; let Z:= Relay.dualize T N p X ℓ k A y'; let I:= X.tone k; let v:=(Z).voice k
    have hj :∀ i:ℕ,m ≤ i→i ≤ k→ w*0 ≤ ζ d i:=fun i hp _=> (mul_zero _).le.trans (h.grows d i (hK.trans hp)).le
    have he (i) (hi:m ≤ i) (ht:i≤k): Z.cost i+(F).coeffSize (Z.voice i).x ≤ E/gainChart T k i:= (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm ..).trans_le ((h'' i (hK.trans hi) ht).trans hc))
    let τ i:= march (fun _:Unit=>w) φ m i (); have h₀: Brine T m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    let c:=(C.path.levels.params k).columns; have hl :1 ≤ c:= (C.path.levels.params k).columns_ge; have hr:Q ≤ E:= le_trans (le_mul_of_one_le_left hx.le (show 1 ≤ 4*(1+(C.path.levels.params k).columns) by dsimp only [c] at hl; linarith only [hl])) hc
    have ht:= diet T d m φ (fun i=>ζ d i/2) w hw (fun i he=> (h₀.water i he).1) (fun i he=> le_trans (le_of_eq (b:=(φ i * ((C.S.block i).val:ℝ)^(d+1)* ζ d i)/2) (by ring)) (div_le_div_of_nonneg_right (h.jump d i (hK.trans he)) (by norm_num))) k E (hx.le.trans hr) ht
    have hτ i (he:m ≤ i): 0 < τ i:= march_pos _ _ _ _ _ (fun _=>hw) h₀ i he _
    have hs(i)(hi:ℓ ≤ i)(ht:i ≤ k): (Z.voice i).Format 0 C.params (R i) ∧ (Z.voice i).remBound 0 (R i) (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (Z.cost i):= keys Y! T N p C.params X y' (hx'.chairs i hi ht) (hL.earned i hi (ht.trans hN))|>.2
    have hS : v.x=y.x-I.index b:=by refine ((hc' y').1).trans ?_; change y.x+I.index (-b)=_; rw [map_neg]; rfl
    refine ⟨Z.voice,Z.cost,b,⟨fun i hi=> hs i (hK.trans hi),fun i hi h₁=> (mul_le_mul_of_nonneg_left (he i hi h₁) (mul_nonneg (hτ i hi).le (norm_nonneg _))).trans ((ht i hi).trans (div_le_self (h.grows d i (hK.trans hi)|>.le) (by norm_num))),fun i hi hm=> ⟨(hx'.ships i (hK.trans hi) hm).debt y',?_⟩⟩,?_,?_,?_,?_,he⟩
    · obtain ⟨v,hv,hP⟩:=(hb i (hK.trans hi) hm).plays; exact ⟨v,hv,hP y'⟩
    · let l:= F; have hT:= he k hk le_rfl; rw [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at hT
      have hz: (F).coeffSize (I.index b) ≤ 2*E:=by
         have hP : I.index b=y.x - v.x:=by rw [hS]; abel
         rw [hP,sub_eq_add_neg]; apply (Size.add ..).trans; have he : (F).coeffSize (- v.x)=(F).coeffSize v.x:= by simp [Labels.Frame.coeffSize]
         rw [he]; linarith only [rem_nonneg ((hs k hM le_rfl).2),hT,hq,rem_nonneg hφ,hr]
      exact hz
    · let t':= pair T N p X (y) c₀; let b':= t'.a; let Q':=t'.sil; let I':= X.tone k; have he :=hL.earned k hM hN; have hz(w):=(he.earns w).2; have hm:=duo_exp Y! hφ (hz (-b')); let q w:=(I'.plays w).exponentialEntry 0 Y! (R k); have hQ:IsLinearMap ℂ q:=expoLinear I'.plays I'.charge he.book hz
      have hs: Z.voice k=t'.bar X y':=show (A k).bar X y'=_ from by rw [hA]
      rw [hs,show t'.bar X y'=beside Q' (I'.plays (b'+y')) from rfl, show (beside Q' (I'.plays (b'+y'))).exponentialEntry 0 Y! (R k)=_ from duo_exp Y! ((presentation hχ hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+y'))]; change Q'.exponentialEntry _ _ _ + q (b'+y')=_; rw [show Q'.exponentialEntry _ _ _=_ from hm]; change _ + q (-b')+q (b'+y')=_+q y'
      rw [hQ.map_add, show q (-b')= -q b' from (IsLinearMap.mk' q hQ).map_neg b']; abel
    · let t':= pair T N p X (y) c₀; let b':= t'.a; let Q':=t'.sil; let I':= X.tone k; have he :=hL.earned k hM hN; have hz(w):=(he.earns w).2; have hm:=duo_profile hφ (hz (-b')); let q w:=profile (R k).activities (I'.plays w).forced; have hQ:IsLinearMap ℂ q:=inkL I'.plays I'.charge he.book hz
      have hs: Z.voice k=t'.bar X y':=show (A k).bar X y'=_ from by rw [hA]
      rw [hs,show t'.bar X y'=beside Q' (I'.plays (b'+y')) from rfl, show profile (R k).activities (beside Q' (I'.plays (b'+y'))).forced=_ from duo_profile ((presentation hχ hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+y'))]; change profile (R k).activities Q'.forced+q (b'+y')=_; rw [show profile (R k).activities Q'.forced =_ from hm]
      change (_+q (-b'))+q (b'+y')=_+q y'; rw [hQ.map_add,show q (-b')= -q b' from (IsLinearMap.mk' q hQ).map_neg b']; abel
    · exact (hc' _).2 -- tower Z at k
end YM.MergeProof.Accent

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
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
lemma root_bequest (ht:C.ref d ≤ m) {hk:m ≤ k} (hN:k<N) (hR:GridApprox.room C.path.levels J k (lensScope C d)) (hC:∀ b:C.label d,Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) (C.O N p b 0))
    (hf :Continuous f)(ha:Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) f) (hr:Q.Format 0 C.params (R k))(hb: Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) t) (ht' : (F).coeffSize Q.x+t ≤ c)(hc: 0 < c)(hE:4*(1+(T|>.levels.params k).columns)*c ≤ E)
    (hw: 0 < w)(hP:32*(1+(T|>.levels.params k).columns)*w * ‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2)
    (hZ:Served (R k) (fun i=> radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k d)) (gust T N p N (birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f)) k hN.le) (o k) (α') (C.path.levels.budget k).supportExponent 1):∃ b:C.label d,Next.UVStress.quota C d k N p b ≤ 2*E∧ (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (f-C.O N p b 0) ≤ 2*(stakes C J m / w)
   ∧ ∃ (Z:∀ i:ℕ,Coefficient F (C.side i p))(g:ℕ→ℝ),
    Club C.path C.params Y! (ζ d) ψ m k N p (fun i=> march (fun _:Unit=>2*w) φ m i ()) D Z g hN.le ∧
    (∀ i,m ≤ i → i ≤ k → g i+(F).coeffSize (Z i).x ≤ E/gainChart T k i) ∧
    (Z k).density 0 (C.localSection d) (R k) = Q.density 0 (C.localSection d) (R k) + ((s!).entries k (- (s!).terminal.symm b)).density 0 (C.localSection d) (R k):=by
    obtain ⟨X,hX,hL,hY,hθ⟩:= (h.costs.aim d N p (ht.trans (hk.trans hN.le))).lyrics
    let Q':=(T|>.levels.params k).columns; have hQ: 1 ≤ Q':= (C.path.levels.params k).columns_ge
    let L':= gainChart T k m; have hξ:0 < L':= Real.exp_pos _
    have hp:0 < E:= lt_of_lt_of_le (show 0 < 4*(1+Q')*c by positivity) hE
    let a':= 2*w; let v' := 8*E*w; have h':0 < v':=by unfold v'; positivity
    obtain ⟨P,x,b,hK,hH,hU,hB,density,price⟩:= retains_cancellation C N k m p d H a' X h Q t c E ht hk hN.le hL hY hr hb ht' hE hc (mul_pos (by norm_num) hw) (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 32*(1+Q') from by linarith only [hQ]) hw.le) (norm_nonneg _)) (div_nonneg hp.le hξ.le)) hP)
    let B:= (s!).terminal b; let I:=Option (F).Index
    let q:= Size.axis F; have he(i):= embrace C N k m p d H v' (q i) X h 1 (4*(1+Q')) ht hk hN.le hL hY (Size.size_axis F i).le (by rw [mul_one]) zero_lt_one h' (le_trans (le_of_eq (b:=32*(1+Q')*w * ‖alto T m d‖*(E/gainChart T k m)) (by unfold v';ring)) hP)
    choose Z g e hΨ using he; obtain ⟨s,hs,hy⟩:=modems C N k p d b X e (fun i=>(hΨ i).bias); have hs'(i:(F).Index):0 ≤ ‖s i‖:= norm_nonneg _; have hβ:(∑ i,‖s i‖)≤4*E:=by linarith only [hH, (show ∑ i,‖s i‖≤ _ from hy)] -- edit
    let W₀:= center C.S p (hV.1.trans (hk.trans hN.le)) 0; let b' i:=(s!).terminal (e i); let n:=lensScope C d; let y i:= lens C N k p d (q i); let ℓ':= ∑ i,(-s i) • y i; let r':= backTo T N p hN.le ℓ'
    have hz(i): Interior (GridApprox.window 0 n) (y i):=visible C N k p d _ H hN.le; let J' := hV.1.trans hk; have hy(i):= quakes C N k m p d H v' (q i) X h J L hN ht hk h' (hΨ i) hL hY hθ hV _ hR (hz i)
    have hM : B=∑ i,s i • b' i:=by unfold B; rw [hs,map_sum]; simp_rw [map_smul]; rfl
    obtain ⟨hW,hZc,hσ⟩:=posing C N k p d H J y (fun i=>s i) J' hN.le b' B n hz (div_nonneg (Real.exp_pos _).le h'.le) hβ hM hC hy hR
    refine ⟨B,?_,?_,P,x,hK,price,?_⟩
    · unfold Next.UVStress.quota; have ha : (s!).terminal.symm B=b:=LinearEquiv.symm_apply_apply ..
      rw [ha,show (s!).entries=(X.draft T).inits from hX,show ((X.draft T).inits k b).x=_ from (hL.earned k (ht.trans hk) hN.le).currents b]; exact hH
    rotate_right
    · -- Witness compatibility: these are the factory entries used for the corridor.
      -- resolve already reconstructed hX, don't run at a new copy of B
      rw [density, show (s!).terminal.symm B=b from LinearEquiv.symm_apply_apply .., show (s!).entries=(X.draft T).inits from hX]
      rfl
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
end YM.MergeProof
