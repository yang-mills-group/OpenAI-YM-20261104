import YM.OPE.Gallery.Orb
/-! # Coaster local haloes and balances through one layer -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet.Lecture
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Cadet Drapery Playout Playout.Rake
open scoped Topology BigOperators Classical
variable {G:Gauge}{I J V L B X : Type}[Fintype V][DecidableEq V]{n:Side}
variable [Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype L][DecidableEq L][Fintype B][DecidableEq B][Fintype X][DecidableEq X]
variable {H:History G}{N p k m i j b T ℓ μ:ℕ}
set_option quotPrecheck false
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
    {δ ψ φ η:ℕ→ℝ}{z r:ℕ→ℕ}{P:Playout H p b N V}{A:Fibers I J}{K:Fibers I L}{C:Fibers L J}
    {α:ℝ}{W:ℕ→I→ℝ}{F:∀ m:ℕ,I→ Cup (H.rep N p m)} {s:Finset J} {s':Ward (Names V J)} {p':∀ m:ℕ,I→ Site (H.S.side m p)}
    (p₀:I→ Config G (H.S.side N p)→ℂ) (U:Season P k j δ ψ φ z η r A s p' s' T W α D F)
local notation "P'"=> (H.levels.budget i)
local notation "L'"=> ( (H.S.block i).val:ℝ)
local notation "S"=> (H.levels.clock.op i p)
local notation "Ξ"=> H.rep N p
local notation "Q"=> (D N p)
local notation "W₀"=> (W i)
local notation "W₁"=> (W (i+1))
local notation "a₀"=> bill H i j (Fintype.card I-Fintype.card L+1) α W₀ K
local notation "a₁"=> bill H (i+1) j (Fintype.card I-Fintype.card L+1) α W₁ K
local notation "Y" => Playout.Rake.grouped_X p₀ K
local notation "Hosts" => Hostage (P:=P) (F:=F) (s:=s) (s':=s') (p':=p')
variable {u:L→ Cup (H.rep N p (i+1))}
variable (h:splitAt A K C)(hX:∀ i,Continuous (p₀ i))(hk:k ≤ i)(hi:i < j) (he:Hostage (P:=P) (F:=F) (s:=s) (s':=s') (p':=p') p₀ (i+1) (hi.trans U.bound) K C u (bill H (i+1) j (Fintype.card I-Fintype.card L+1) α (W (i+1)) K)) -- `hi.trans U.bound` evidence. careful named args variable macros
include h hX hk hi he U
lemma possible : ∃ (u':L→Cup (Ξ i))(x:L→ℂ), P.ArcMarket (pullback C s') (p' i ∘ K.twig) u' (P.intention Y i (hi.le.trans U.bound.le)) a₁ (δ i) (φ i) x ∧ (∀ j,C.bunch j∈s→u' j=F i (K.twig j)) ∧ (∀ j,C.bunch j∉s→ Blade (Ξ i) (p' i (K.twig j)) (u' j).home (u' j).leaves 0 (1/(2*a₀ j))) :=by
    have hm:= hi.trans U.bound; let Y':= grouped_X p₀ K; have hM(k):=Rake.cont p₀ K hX k; obtain ⟨h0,h1⟩:= U.group i hk hi.le; have hV:= hi.trans j.lt_succ_self; have hf:= U.width i hk hV.le; have ht:= U.width (i+1) (hk.trans i.le_succ) hV; obtain ⟨ht',hA⟩:= U.thaws
    have hp := U.depth.trans hk; let p':= p'; let o(i):= p' i ∘ K.twig
    have hh(l:L):o i l=(S).ratio.parent (o (i+1) l):= U.roomP _ hk hi.le _
    have hx(l:L):∃ f:Cup (Ξ i), ∃ x:ℂ, Cup.Edge S (Q i hm) (u l) f (o (i+1) l) (o i l) x (a₁ l) ∧ (C.bunch l∈s → f=F i (K.twig l)) ∧ (C.bunch l∉s → Blade (Ξ i) (o i l) f.home f.leaves 0 (1/(2*a₀ l))):=by
       let x:=K.twig l; by_cases ha:C.bunch l∈s
       · have hz:A.bunch x∈s:= (h.runs _).symm ▸ ha; obtain ⟨c,hc⟩:= (U.staying x hz).follows i hk hV; rw [he.stays _ ha]; refine ⟨_,c,hc.thin ((he.market.width _).le) (paidOne s K C U.rests h ha ht' hA (ht _|>.le) hi),fun _=>rfl, fun hv=> (hv ha).elim⟩
       obtain ⟨f,hx,hZ⟩:= sloshes U hk hi (he.lives l ha) (he.market.width l) (bill_pos K l ht' hf) (awaken s K C h ha (U.awake _ hk hi) hf ht ht'); rw [hh]; exact ⟨f,0,hx,fun hh=> (ha hh).elim,fun _=>hZ⟩
    choose f x hx hf he' using hx; rw [P.intention_step Y' hm] -- maybe rw doesn't match
    exact ⟨f,x,he.market.strides P U.store.well U.store.host hp hp hm (by linarith only) (P.paidFor _ U.store.well hM hm) hh (occupied_trans h1 K) (occupied_trans h0 K) hx,hf,he'⟩ -- `hm` proof le .trans.N

set_option maxHeartbeats 600000 in
lemma marchNext : ∃ (J':Type)(_ : Fintype J')(_ : DecidableEq J')(K:Fibers I J')(C:Fibers J' J)(u:J'→Cup (H.rep N p i)), splitAt A K C ∧ Hosts p₀ i (hi.le.trans U.bound.le) K C u (bill H i j (Fintype.card I-Fintype.card J'+1) α W₀ K):=by
    have hb:= U.store; have hm:= hi.trans U.bound; let Y':= grouped_X p₀ K; let o:= p' i ∘ K.twig; obtain ⟨h0,h1⟩:= U.group i hk hi.le; obtain ⟨u',x,hU,hF,hΓ⟩:= possible p₀ U h hX hk hi he; let v:= z i; let W':=a₁; let a:=a₀; let μ:=P.spectrum i o; have hp:= U.depth.trans hk; obtain ⟨hη0,hη1,hδ0,hδ1⟩:= hb.params i hp; obtain ⟨hlt,hy,hC,hκ,hρ⟩:= U.budgets i hk hi.le
    have hh:= hi.trans j.lt_succ_self; have hw':= U.width i hk hh.le; have hw:=U.width (i+1) (hk.trans i.le_succ) hh; obtain ⟨ha,hα⟩:=U.thaws; have he_:L→ Cup (Ξ i):=u' -- local heap
    have ht(l:L):= show 0< a l from bill_pos K l ha hw'
    have h0':= occupied_trans h0 K
    by_cases hq:Spaced (pullback C s') μ ((P').B*z i)
    · have hK(l:L): η i*a l ≤ W' l:= consumingCost s U.rests h hη0 hη1 ha (U.awake _ hk hi) hw' hw (U.payment i hk hi.le) _
      let T' := (P').supportExponent; have hm0:= ArcMarket.peek P U.store.well hb.host hp hp hm hU h0' (trial C s' U.bare) ht (moderated hb hp ht hK hq)
      exact ⟨L,inferInstance,inferInstance,K,C,u',h, ⟨hm0.shy P ht le_rfl (by linarith only),hF,hΓ⟩⟩
    obtain ⟨J,cX,cY,Fk,Xk,hk',hφ,hY⟩:=near_stay U h hq hk hi.le
    have hL:= h.headset Fk Xk hk'; let E:=K.comp Fk; let b':=Fintype.card I-Fintype.card J+1; let w:=bill H i j b' α W₀ E; have hv(x):0<w x:=bill_pos E x ha hw'
    have ho:Fintype.card L ≤ T:=(card_size K).trans U.purchase
    let s1:=univ.filter (fun i=> Xk.bunch i∈s); have hs(i): i∈s1↔ Xk.bunch i∈s:=by simp [s1]
    let l:= z i + 2; have hb0 (x): w x ≤ grouped H δ T l i W' Fk x /8:= combine_budget K Fk (show splitAt E K Fk from fun _=>rfl) (U.payment i hk hi.le) hw' hw hη0 hη1 ha hα hlt hy (license_pos _ _ hδ0 U.licence) (by dsimp only [b']; have he:=card_size K; omega) _
    obtain ⟨U',hV,hψ,hJ⟩:= ArcMarket.integrate P U.store.well U.store.host Fk hp hp hm hC hκ (hh:=hk'.wardrobe s' ▸ hU) (z:=s1) (fun i hi=> hk'.dorm1 _ (h.dorm2 (U.rests (Xk.bunch i) ((hs i).mp hi)))) U.licence ho h0' (fun j=> hφ j) (s':=pullback Xk s') (fun j hj=> (ready_up Fk _ j).2 hj)
    have hh': Market P (pullback Xk s') (o ∘ Fk.twig) U' (fun U=>Fibers.reap (partialGroup V Fk) (P.intention Y' i hm.le U)) w ((P').supportExponent-3):= (Market.shy P hV hv (fun x=>(hb0 x).trans (div_le_self (le_of_lt (hV.width ..)) (by norm_num))) (by linarith only)) -- id
    refine ⟨J,cX,cY,E,Xk,U',hL,?_,fun j hj=>?_,fun j hj=> ?_⟩ -- constructor syntax
    · convert! hh' using 1; -- proof operation intent
      have ht':grouped_X p₀ E=grouped_X Y' Fk:= funext fun i=> funext fun U=> (show splitAt E K Fk from fun _=>rfl).group_prod ℂ (fun p=>p₀ p U) i
      rw [ht']; exact (funext (Rake.intention_eq P _ Fk U.store.well (Rake.cont _ K hX) hm.le)).symm
    · rw [hJ j ((hs _).mpr hj)]; exact hF _ ((hk'.runs ..|>.symm) ▸ hj)
    apply (hψ j (mt (hs j).mp hj)).more; have Hx:=hb0 j; have h1:=hv j; have h2:= hV.width j; let p:= grouped H δ T l i W' Fk j; change 4*(1/p) ≤ 1/(2* w j); rw [← mul_div_assoc]; exact (div_le_div_iff₀ h2 (mul_pos (by norm_num) h1)).2 (by linarith only [Hx])
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Lecture
