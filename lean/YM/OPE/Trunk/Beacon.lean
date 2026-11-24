import YM.OPE.Trunk.Mutation
/-! # Commitment for on-C: in one fixed arrangement, main cluster mismatch and parent. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Rhythm.Store
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake
open scoped Topology BigOperators Classical ContDiff
variable {I J Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p T t t' q d:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {S:Q.Loom}{P:I→ Z→ Prop}{u:∀ i:ℕ,I→Site (C.side i p)}
    (U:Q.Tour C S b H N p u)
variable {W r D}(L:LogPackage C W r D)(h:C.Makes)
namespace Variant
open Plain Highest Studio Playout Pigment
variable {S':Loom Q}(U':Q.Strike H l)(d':I→ℕ)(z:(i:I)→ C.label (d' i))
variable (A:I→ℝ) (u₀ :∀ i:ℕ,I→Site (C.side i p))
    {Y': Finset ℕ}{x:ℕ→ℝ} (H':Rates S L T Y' x)
set_option quotPrecheck false
local notation "Θ"=> standC C b N p
local notation "Y"=> C.path.levels
local notation "V_c!"=> Site (C.side b p)
local notation "ω'"=> (fun t=>S.below t) -- binder syntax
local notation "β"=> (fun i:I=>birthClock C (S.launch (Q.age i)) (d' i) (A i))
variable {e:ℕ} -- H root output horizon d, e sign-v
local notation "m!"=> S.below H
local notation "j!"=> S.below 0
local notation "Z₀"=> (C.labels.level d).Index
local notation "Z₁"=> (C.labels.level e).Index
local notation "w!"=> estate H β (owner Q H)
local notation "λa"=> (owner Q H) -- replace reserved
local notation "q!"=> walletF Z₀ (Q.fold (Nat.zero_le 1))
local notation "y!"=> (past C d' N p z (u N))
local notation "δ"=> discharged L S T x
local notation "Ψ"=> provision L S T x
local notation "θ'"=> base_price Q C S d' A*widen S C H l e
include U L h U' H'
set_option maxHeartbeats 2000000 in
lemma committed (hf:Stock.Tabs.opens C.path.levels 1 b q)(he:q ≤S.below 0)(hk:C.ref 0 < b)(hc:C.ref d ≤ q)(hh:C.ref e ≤ q)(hd:e∈ Y')(hG:G.Simple) (ht: Fintype.card I+Fintype.card (Z₀ ⊕ Z₁) ≤ T)(hF:∀ m,S.below 0 ≤ m→T ≤ r m)(hS:∀ i,A i>0)(hV:∀ i,C.ref (d' i) ≤ S.launch (Q.age i))(hQ:∀ i,Next.UVStress.quota C (d' i) (S.launch (Q.age i)) N p (z i)≤A i)
    (hZ:∀ k,m! ≤ k→k ≤ N→∀ i,i∉ Q.focus H→((Y).budget k).B^2≤ separation (u k i) 0) :
    let f (v:C.label e):= childF (C:=C) y! Q H - C.O N p v 0; let g (v:C.label e) g:= f v g* ∏ i∈ univ\ Q.focus H,y! i g
    ∃ (z₁:C.label e)(z₀:C.label d), Next.UVStress.quota C e m! N p z₁ ≤ 2*stampOut C m! e (Ψ H*w!) ∧ Next.UVStress.quota C d j! N p z₀ ≤ 2*stampOut C j! d (Ψ 0* θ') ∧ ∃ hj:b≤N, let x':=center C.S p hj 0;
      x'.rootTest (C.beta N p) (f z₁) ≤ stakes C b q/(road C m! e (δ H e*w!) q)∧ x'.rootTest (C.beta N p) (g z₁-C.O N p z₀ 0) ≤ stakes C b q/(road C j! d (δ 0 d* θ') q):=by
     intro f₁ f₀; let V':= (C.labels.level d).Index; let J':= (C.labels.level e).Index; let t:= m!; let j:= j!; have hp:= U'.before; have hH:=U'.atMost; have ht' := (S.le_below Q (Nat.zero_le H) hH); have hx:= ((Q.belowLaunch S hH).trans (U.lasts hH)).le; have h_j:= he.trans ht'; let v:=carried Q V' H; let v₀:=carried Q V' 0; let X:= finalScan (Site (C.side b p)) V' (Q.ticket Q.star 0); let i:ℕ:=1; have hi:i≤H:=by omega
     have hx'(i): S.launch (Q.age i) ≤ N:= (U.lasts (Q.bounded i)).le; choose P hP using fun i=> Studio.seriesExist (p:=p) L.system ((hV i).trans (hx' i)); obtain ⟨E,hE⟩:= Studio.seriesExist (p:=p) L.system ((hc.trans h_j).trans hx); obtain ⟨E',hE'⟩:= Studio.seriesExist (p:=p) L.system ((hh.trans h_j).trans hx)
     let Z:= Z₀ ⊕ Z₁; let z':= roles (fun _ : Z₀=>d) (fun _:Z₁=> e); let d₀:I⊕Z→ℕ:= roles d' z'; let Ue:= basisUp (C:=C) E j; let Um:=basisUp (C:=C) E' t; let Q' : (i:I⊕ Z) → C.label (d₀ i):= labelsAll z (labelsAll (d:=(fun _:Z₀=>d) ) (d':=(fun _:Z₁=>e)) Ue Um); let D' : (i:I⊕Z)→Music (C.labels.level (d₀ i)) C.path N p:= seals P (seals (fun _=>E) (fun _=>E')); let φ:Z→ℕ:= Sum.elim (fun _ => j) (fun _=> t)
     let P₀:=Sum.elim (fun _: Z₀=> (1:ℝ)) (fun _ :Z₁=>1); let w : I⊕Z→ℝ:= Sum.elim A P₀; have h_T: Strands C L d₀ (origin Q S φ) w b N p Q' D':= swords L ⟨hP,fun i=>⟨U.born.trans (S.up_b Q (Q.bounded i)|>.le),hx' _⟩,hV,hS,hQ⟩ (swords L (forge L (hc.trans he) U.born (ht'.trans hx) hE) (forge L (hh.trans h_j) (U.born.trans ht') hx hE'))
     let s:= pullback q! X; let Qκ:= walletF Z₀ (Q.fold hi); let S':=pullback Qκ s; let s' := spoil Q H S' Z₁; have hV:= oneHost Q (Site (C.side b p)) (C.labels.level d).Index; have hV':Q.Host i (fun _ _=>False) s:= hV.trans (Nat.zero_le 1); have hV0:Q.Host H (fun _ _=>False) S':= hV'.trans hi; have hh':Q.Host H (film Q Z₀ Z₁ H) s':= turnAbout S' Z₁ hV0; let K':= walletF Z (Q.fold H.le_succ); let Xw:=planWord C d₀ N p Q' (u N) Q
     let φ₀(_:Z₀):= j; let φ₁(_:Z₁):=t; have hφ'(z:Z): b ≤ φ z∧ φ z≤ t:=by cases z; exact ⟨U.born,ht'⟩; exact ⟨U.born.trans ht',le_rfl⟩
     let a(s):=S.launch (Q.age s); let W₀:=β; let W₁:= earn C φ₁ (fun _=>birthClock C t e 1); let W₂:= earn C φ₀ (fun _=>birthClock C j d 1); let u'_ := showAt Q S C φ w d₀; have h_wk(l):u'_ l= Plain.width Q S C W₀ (augments W₂ W₁) l:=by
         let z_ : I→ℝ:= labelCost C (origin Q S φ) w d₀ ∘ Sum.inl; have he:z_=W₀:=rfl
         change Plain.width _ _ _ z_ ?_ _= _; rw [he]; congr 1; -- need argue augments w₂ proof afterClocks
         funext i z; cases z <;> rfl
     have hΩ:∀ k,t≤k→k ≤ N → ∀ i j,film Q Z₀ Z₁ H i j→((Y).budget k).B^2≤ separation (u k i) 0:=by
         intro k he ht i z h'; cases z; exact False.elim h'; exact hZ k he ht i h'
     obtain ⟨p₁,hp₁,hQ⟩:=Plain.upper (s₀:=pullback K' s') U L h h_T (hh'.trans H.le_succ) H' (Nat.succ_le_succ hH) ht hk hG hF (fun l hv' hs i=> (hφ' i).2.trans (S.le_below Q (Nat.le_of_succ_le hv') hs)) (fun l hl h k he hk=>hΩ k ((S.le_below Q (Nat.le_of_succ_le hl) h).trans he) hk)
     obtain ⟨hS',htV⟩:=Plain.no_sign U L φ U.born hH hφ' ht hF hΩ
     let z₁:=carried Q (Z₀⊕Z₁) H; let t':= S.launch l
     have hh_(i:Z₁): W₁ t i=birthClock C t e 1∧ Xw (H+1) (.inr (.inr i))= C.O N p (Um i) 0∧ Mantle C.path N p t (C.localSection e) (1,false) 0 ((E'.tone t).plays (az E' t i)) (p₁ t (.inr (.inr i))):=by
         refine ⟨earning_here _ i (clock_pos one_pos),z_extra ..,?_⟩ -- Wake usage at own.Cash
         rw [← show (C.factory e N p).terminal.symm (Um i)= az E' _ i from LinearEquiv.symm_apply_apply ..]; exact hQ (.inr i)
     rw [show showAt Q S C φ w d₀ (H+1)=_ from h_wk _] at hp₁
     obtain ⟨z1,hz1,hN1,hM,p₂,hp₂,hpr⟩:= convoy_mid U L h U' S' hV0 H' (φ:=φ₀) hp₁ hf hh he hk hG hd hE' hS' htV hh_
     let f:= applySign e ((Xw H ∘ (exchangeShape _ _ _).symm) ∘ Sum.inl) z1 v; let g := grouped_X f Qκ; have hξ := group_later Q' (u N) Q H.le_succ
     rw [hξ] at hp₂ hM
     have HT:Xw H (carried Q Z H)=childF (C:=C) y! Q H∧ grouped_X f (walletF Z₀ (Q.fold (Nat.zero_le H))) (carried Q Z₀ 0)= f₀ z1:= joins_E (f:= (Xw H ∘ (exchangeShape _ _ _).symm)∘Sum.inl ) (Z:=Z₀) z1 (y!) (fun k=>funext fun g=>panel_z Q' (u N) Q k g)
     let W' := patchWidth Q S C H l e W₀ W₂; let K:ℕ→ℕ:=S.launch; let φ':=patchDues Q S V' l φ₀
     have ht'' : Fintype.card I+Fintype.card Z₀ ≤ T:=by simpa only [Fintype.card_sum] using ((Nat.add_le_add_left (show Fintype.card Z₀ ≤ Fintype.card (Z₀⊕ Z₁) from (by rw [Fintype.card_sum]; omega)) (Fintype.card I)).trans ht) -- `add_le_add_left`
     have H_z(k:ℕ)(he:k < H): ∃ U₂: Case Q S L u N T k (fun _ (_:Z₀)=>False) (keep Q Z₀ l k) (φ' (k+1)), Plans U₂ b (φ' k):= tempCase (t:=k) U L h U' φ₀ he (fun z=> ⟨U.born,S.le_below Q (Nat.zero_le k) (he.le.trans hH)⟩) ht'' hF
     have hB:Bowl S L φ' W' (fun _ _=>False) b T p N u i H:=by refine ⟨fun k hk ht=>?_⟩; obtain ⟨V,hV⟩:= H_z k ht; exact ⟨_,V,hV,along_w U' W₀ W₂ ht⟩
     obtain ⟨p₃,hp₃,hC⟩:= transit U L h H' hV' hk hG hi hB hp₂
     have h_X_ : grouped_X g (q!)=grouped_X f (walletF Z₀ (Q.fold (Nat.zero_le H))):=funext fun i=>funext fun q=> ((Q.transShape_panel Z₀ (Nat.zero_le 1) hi).group_prod ℂ (fun i=> f i q) i).symm
     have hA : lineRelease (q!) (W' 1 j) v₀=θ':= (edge_root (d:=e) U' W₀ W₂) -- x price formula
     have hX(i:Z₀): W' 1 j (.inr i)=birthClock C j d 1 ∧ g (.inr i)= C.O N p ((C.factory d N p).terminal (az E j i)) 0 ∧ Mantle C.path N p j (C.localSection d) (1,false) 0 ((E.tone j).plays (az E j i)) (p₃ j (.inr i)):=by
         refine ⟨(otherRates W₀ W₂ (show Sum.inr i≠carried Q Z₀ 1 from (fun h=>by cases h))).trans ?_,?_,?_⟩
         · exact (show W₂ j i=birthClock C j d 1 from earning_here _ i (clock_pos one_pos))
         · funext U; unfold g grouped_X; rw [(Q.solo_c Z₀ hi i).content,prod_singleton]; change f (.inr i) U=_; rw [show f (Sum.inr i)= Xw H (.inr (.inl i)) from if_neg (show Sum.inr i≠ carried Q Z₀ H from (fun h=>by cases h))]; exact congr_fun (z_extra Q' _ _ (.inl i)) U
         rw [hC,hpr,← show ((C.factory d N p).terminal).symm (Ue i)= az E j i from LinearEquiv.symm_apply_apply ..]; exact hQ (.inl i)
     obtain ⟨Z',_⟩:=H_z 0 (by omega); have hY : v₀∉ keep Q V' l 0:= by rw [keep,if_neg (Nat.not_lt_zero _)]; exact ownerAlive U' (Nat.zero_le _) V';
     obtain ⟨z0,hz0,hn,hΩ⟩:= Highest.issue U L h Z' hp₃ hf he hk hc hY hG hE hX
     refine ⟨z1,z0,hz1,?_,hn, ?_ ⟩; · rw [← hA]; exact hz0
     intro Y_; refine ⟨?_,?_⟩; · change Y_.rootTest _ (f₁ z1)≤ _; unfold f₁; rw [← HT.1]; exact hM
     rw [← hA,← HT.2,← h_X_]; exact hΩ
end Variant
end YM.OPE.Log.Trunk.Rhythm.Store
