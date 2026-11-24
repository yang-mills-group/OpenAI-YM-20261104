import YM.OPE.Gallery.Merge
/-! # Path budget through a whole segment ending really gathered. -/
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
    (p₀:I→ Config G (H.S.side N p)→ℂ) (U:Season P k j δ ψ φ z η r A s p' s' T W α D F)(hX:∀ i,Continuous (p₀ i))
local notation "P'"=> (H.levels.budget i)
local notation "Ξ"=> H.rep N p
local notation "Hosts" => Hostage (P:=P) (F:=F) (s:=s) (s':=s') (p':=p')
include U hX
local notation "Y"=> (fun k=> H.levels.budget k)
private lemma same_launch (h:P.Market (pullback A s') (p' (j+1)) (F (j+1)) (P.intention p₀ (j+1) U.bound) (W (j+1)) ((H.levels.budget (j+1)).supportExponent-3)) : ∃ (F':I→Cup (Ξ j)), Hosts p₀ j U.bound.le (Fibers.same I) A F' (bill H j j 1 α (W j) (Fibers.same I)):=by
    choose c hc using U.readiness; let hJ:=U.tall.le; obtain ⟨h0,h1⟩:= U.group j hJ le_rfl; have he:= U.bound; have hj:= U.depth.trans hJ; have hφ:P.ArcMarket (pullback A s') (p' j) (F j) (P.intention p₀ j he.le) (W (j+1)) (δ j) (φ j) c:=by
       rw [P.intention_step p₀ he]; exact h.strides P U.store.well U.store.host hj hj he (by linarith only) (P.paidFor p₀ U.store.well hX he) (U.roomP j hJ le_rfl) h1 h0 hc
    let z':=(univ.filter fun i=> A.bunch i∈s); let K':= Fibers.same I; let H':=z j+2; have hk':∀ i:I,K'.Solo i:=fun i l hl=> hl.symm
    obtain ⟨hK,hL,hT,hB,-⟩:= U.budgets j hJ le_rfl; obtain ⟨hη,hβ,hδ,hθ⟩:=U.store.params j hj
    have hp : ∀ l,coverNumber (Y j).B ({p' j (K'.twig (K'.bunch l)),p' j l}:Support _) ≤ H':=fun l=> OPE.Log.moderateRadius (p' j l) (p' j l) (Y j|>.B) (z j) (by simp)
    obtain ⟨F',he',hf,hF⟩:= hφ.integrate P U.store.well U.store.host K' hj hj he hT hB (fun i (_:i∈z')=> hk' i) U.licence U.purchase h0 hp (s':=pullback A s') (fun j hj=> (pull_same (pullback A s')) ▸ ((ready_up K' (pullback A s') j).2 hj)  ) -- not defeq under same. fix
    let g:= grouped H δ T H' j (W (j+1)) K'; let w:=bill H j j 1 α (W j) K'; have h_z(l):0 < w l:= bill_pos K' l U.thaws.1 (U.width j hJ j.le_succ)
    have hξ(l): w l ≤ g l /8:=by
       unfold w g grouped; rw [pay_single _ (hk' l), (hk' l).content, prod_singleton]; change cell H j j 1 α (W j l) ≤ license H δ T H' j * W (j+1) l /8; unfold cell; rw [div_self (H.S.a_pos j).ne',one_pow,one_mul,pow_one]; apply (le_div_iff₀ (by norm_num)).2; let y:= license H δ T H' j; have he:= U.payment j hJ le_rfl l; linarith only [mul_le_mul_of_nonneg_left he (show 0≤ license H δ T H' j from (license_pos _ _ hδ U.licence).le),mul_le_mul_of_nonneg_right hK (show 0 ≤ W j l from (U.width _ hJ j.le_succ _).le)] -- normalization linarith
    refine ⟨F', ?_,?_,?_⟩
    · have hp1:= he'.shy P h_z (fun l=> (hξ l).trans (div_le_self (le_of_lt (he'.width l)) (by norm_num))) (by linarith only: ((Y j).supportExponent-3:ℝ) ≤ (Y j).supportExponent-2)
      have ht : ∀ i:I,K'.contents i={i}:=fun i=>(hk' i).content
      have hp': grouped_X p₀ K'= p₀:= by funext i U; unfold grouped_X; simp [ht i]
      have hp0 : (fun U'=> Fibers.reap (partialGroup V K') (P.intention p₀ j U.bound.le U'))= P.intention p₀ j he.le:=funext (fun i=> Fibers.same_reap _)
      rw [hp0] at hp1; rw [hp']; exact hp1
    · intro l he; exact hF l (mem_filter.mpr ⟨mem_univ _,he⟩)
    intro l ht; apply (hf l (fun hp=>ht (mem_filter.mp hp).2)).more; change 4*(1/g l) ≤ 1/(2* w l); rw [← mul_div_assoc]; exact (div_le_div_iff₀ (show 0 < g l from he'.width l) (mul_pos (by norm_num) (h_z l))).2 (by linarith only [hξ l])
where fix:= () -- edit
lemma Season.finishBudget (h:P.Market (pullback A s') (p' (j+1)) (F (j+1)) (P.intention p₀ (j+1) U.bound) (W (j+1)) ((H.levels.budget (j+1)).supportExponent-3)) : ∃ (F':J→Cup (Ξ k)), let u:= bill H k j (T+2) α (W k) A; P.Market s' (p' k ∘ A.twig) F' (P.intention (grouped_X p₀ A) k (U.tall.trans U.bound|>.le)) u ((Y k).supportExponent-3) ∧ (∀ i:J,i∈s→ F' i=F k (A.twig i)) ∧ ∀ i:J,i∉s→ Blade (Ξ k) (p' k (A.twig i)) (F' i).home (F' i).leaves 0 (1/(2*u i)):=by
    have hb:= U.store; obtain ⟨hP,hQ⟩:=U.thaws; have hK:=U.tall; have hN:=U.bound; have hm:=hK.trans hN
    have h(i:ℕ)(hi:k+1 ≤ i)(hj:i≤j): ∃ (J':Type)(_ : Fintype J')(_ : DecidableEq J')(K:Fibers I J')(C:Fibers J' J)(x:J'→Cup (H.rep N p i)), splitAt A K C ∧ Hosts p₀ i (hj.trans hN.le) K C x (bill H i j (Fintype.card I-Fintype.card J'+1) α (W i) K):=by
       induction hj using Nat.decreasingInduction with
       | self=> obtain ⟨F',hF⟩:= same_launch p₀ U hX h; refine ⟨I,inferInstance,inferInstance,Fibers.same I,A,F',fun _=>rfl,?_⟩; rw [Nat.sub_self]; exact hF -- rw not
       | of_succ i hi IH=> obtain ⟨L,cY,cV,K,C,x,he,hX⟩:= IH (‹k+1 ≤ i›.trans i.le_succ); exact marchNext p₀ U he ‹∀ i, Continuous (p₀ i)› (by omega) ‹i<j› hX
    obtain ⟨L,cY,cV,K,C,x,he,hΦ⟩:= h (k+1) le_rfl hK; obtain ⟨x',q,hφ,hV,hR⟩:= possible p₀ U he hX le_rfl hK hΦ; let u0(k):=p' k ∘ K.twig
    have hE(a:J):A.bunch (K.twig (C.twig a))=a:= (he.runs _).trans (C.sectioned ..); have hE': u0 k ∘ C.twig=p' k ∘ A.twig:= funext (fun i=> U.landing _ _ ((hE i).trans (A.sectioned _).symm))
    have hx: Fintype.card L ≤ T:= (card_size K).trans U.purchase; have hy:= U.group k le_rfl hK.le; obtain ⟨hξ,hA,hX',hU,-⟩:= U.budgets k le_rfl hK.le; let t:=z k+2
    have hh : ∀ i:L, coverNumber (H.levels.budget k).B ({u0 k (C.twig (C.bunch i)),u0 k i}:Support _) ≤ t:= by
       intro i; rw [show u0 k (C.twig (C.bunch i))=u0 k i from U.landing _ _ ((hE (C.bunch i)).trans (he.runs i).symm)]; exact OPE.Log.moderateRadius _ _ _ _ (by simp)
    obtain ⟨Y',hB',hY,hB⟩:= ArcMarket.integrate P hb.well hb.host C U.depth U.depth hm hX' hU hφ (z:=s) (fun i hi=> he.dorm2 (U.rests i hi)) U.licence hx (occupied_trans hy.1 K) hh (s':=s') (fun i hi=> (ready_up C s' i).2 hi)
    let d:= bill H (k+1) j (Fintype.card I-Fintype.card L+1) α (W (k+1)) K; let y:= grouped H δ T t k d C; let u:= bill H k j (T+2) α (W k) A; obtain ⟨hb0,hb1,hb2,-⟩:= U.store.params k U.depth; have hu:=hK.trans j.lt_succ_self
    have he_i:= U.width k le_rfl hu.le; have hg(x:J):0<u x:=bill_pos A _ hP he_i; have hv(x:J): u x ≤ y x/8 := combine_budget K C he (U.payment k le_rfl hK.le) he_i (U.width (k+1) k.le_succ hu) hb0 hb1 hP hQ hξ hA (license_pos _ _ hb2 U.licence) (by have h:=U.purchase; omega) x
    have hK' : grouped_X p₀ A=grouped_X (grouped_X p₀ K) C:=funext fun i=>funext fun U=> he.group_prod ℂ (fun p=> p₀ p U) i
    have hh': (p' k ∘ K.twig) ∘ C.twig=p' k ∘ A.twig:= hE'
    refine ⟨Y',?_,fun j hj=>?_,fun j hj=>?_⟩
    · have he_T : P.intention (grouped_X p₀ A) k hm.le = (fun U=> Fibers.reap (partialGroup V C) (P.intention (grouped_X p₀ K) k hm.le U)):= by rw [hK']; exact (funext (intention_eq P _ _ U.store.well (Rake.cont p₀ K hX) hm.le)).symm
      rw [← hh',he_T]; exact hB'.shy P hg (fun x=>(hv x).trans (div_le_self (le_of_lt (hB'.width x)) (by norm_num))) (by linarith only)
    · rw [hB j hj,hV (C.twig j) (C.sectioned j|>.symm ▸ hj),he.occupySame U.rests j hj]
    · have ht: u0 k (C.twig j)=p' k (A.twig j):=congr_fun hE' j; rw [← ht]; apply (hY j hj).more; change 4*(1/y j) ≤ 1/(2*u j); rw [← mul_div_assoc]; exact (div_le_div_iff₀ (show 0 < y j from hB'.width _) (mul_pos (by norm_num) (hg j))).2 (by linarith only [hv j])
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Lecture
