import YM.Contacts.Barrage.Loose
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
variable {X Y ι:Type}{b c d h a v:ℝ}
variable {e: Oasis G}
variable [Fintype ι] {p:ℕ}{l:Pulse.Range X}{L:Pulse.Range Y}{u:X→ Y→ℝ}{R S:X→Y→ℝ}{F U :Field ι X}
section stat
lemma prints_sub (F G :Field ι X): printRun (F-G)=printRun F-printRun G:= by ext1 i; simp [printRun,reorder,sum_sub_distrib,mul_sub]
lemma hoist_sub {k:ℕ} [NeZero k] {F U : Field (Fin k) X}(hu: Ripple l L u)(h:Weirs u R b c)(he:Rooted l F a)(hf: Rooted l U d) : hoist R (F-U)=hoist R F-hoist R U:= by
    unfold hoist; rw [← prints_sub]; congr 1; ext1 x; simp only [allAt,Pi.sub_apply,sub_mul]; exact (all_summable he hu (fun _=> h) x).of_norm.tsum_sub ((all_summable hf hu (fun _=> h) x).of_norm)
lemma weir_up (H: Weirs u R b c)(hp:b≤ d)(hx:c ≤ h): Weirs u R d h:= ⟨H.left.trans hp,H.right.trans hx,fun i=>budget_loosen (H.columns i) hp,fun i=> budget_loosen (H.rows i) hx⟩
private lemma pivot_sub (t:ι) (U:ι→ X→Y→ℝ)(h:∀ i,Weirs u (U i) b b) (hr : Weirs u R b b)(hs: Weirs u S b b)(hx: Weirs u (R-S) c c)(hu:Ripple l L u)(hf:Rooted l F d) : Rooted L (allAt (Function.update U t R) F - allAt (Function.update U t S) F) (d*c*b^(Fintype.card ι-1)):= by
    let W (T:X→Y→ℝ):= Function.update U t T; let V:ι→X→Y→ℝ:= W (R-S); let f:ι→ℝ:= Function.update (fun _=> b) t c
    have hw i : Weirs u (V i) (f i) (f i):= by by_cases hi:i=t; subst i; simpa [V,W,f] using hx; simpa only [V,W,f,update_of_ne hi] using h i
    letI: Nonempty ι:= ⟨t⟩; have ht (T:X→Y→ℝ) (hT:Weirs u T b b) (p:ι→ Y) : Summable (fun x:ι→X=> F x*∏ i,W T i (x i) (p i)):= (all_summable hf hu (fun i=> show Weirs u _ b b from (by by_cases he:i=t; subst i; simpa [W] using hT; simpa only [W,update_of_ne he] using h i)) p).of_norm
    have he (T:X→Y→ℝ) (p:ι→Y)(x:ι→X) : (∏ i:ι,W T i (x i) (p i))= T (x t) (p t)*(∏ i∈ univ.erase t,U i (x i) (p i)):= by
       rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), show W T t=T from update_self ..]; refine congr_arg _ (Finset.prod_congr rfl fun i hi=> ?_); erw [show W T i=U i from Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _]
    have hrb:= hr.left; have hcb:= hx.left; have hdb:=hf.cash; change Rooted L (allAt (W R) F - allAt (W S) F) _
    rw [show allAt (W R) F-allAt (W S) F=allAt V F from (by funext p; rw [Pi.sub_apply,allAt,allAt,← (ht R hr p).tsum_sub (ht S hs p),allAt]; exact tsum_congr fun x=> by rw [he,he, show V=W (R-S) from rfl,he,Pi.sub_apply,Pi.sub_apply,sub_mul,mul_sub])]
    refine all_root hf hu hw (fun i=>?_ ) (by positivity); rw [mul_right_comm (f i),Finset.mul_prod_erase _ _ (mem_univ _),←Finset.mul_prod_erase _ _ (mem_univ t)]; erw [show f t=c from Function.update_self ..] -- remove
    simp_rw [show (∏ i∈univ.erase t,f i)= (∏ i∈univ.erase t,b) from Finset.prod_congr rfl fun i hi=> update_of_ne (Finset.mem_erase.mp hi).1 _ _ ,Finset.prod_const, Finset.card_erase_of_mem (mem_univ _),Finset.card_univ]; apply le_of_eq; ring
private lemma psub (s:Finset ι) (hu:Ripple l L u)(hf:Rooted l F d)(hr : Weirs u R b b)(hs: Weirs u S b b)(hx: Weirs u (R-S) c c) : let v i:= if i∈s then R else S; Rooted L (allAt v F-allAt (fun _=> S) F) ((s.card:ℝ)*(d*c*b^(Fintype.card ι-1))):= by
    induction s using Finset.induction with
    | empty=> simp only [Finset.card_empty,Nat.cast_zero,zero_mul, Finset.notMem_empty, ↓reduceIte,sub_self]; apply Rooted.tranquility L
    | insert i s hi ih=>
      intro V; let M:=d*c*b^(Fintype.card ι-1); let U(x:ι):= if x∈s then R else S; have he:=pivot_sub (X:=X) (Y:=Y) (F:=F) i U (fun i=> by by_cases h:i∈s; simpa only [U,h,↓reduceIte] using hr; simpa only [U,h,↓reduceIte] using hs) hr hs hx hu hf; have hh: update U i S=U:= by ext1 j; by_cases h:j=i; subst j; simp [U,hi]; exact update_of_ne h _ _
      have hv: update U i R=V:= by ext1 j; by_cases h:j=i; subst j; simp [V]; rw [update_of_ne h]; simp [U,V,h] -- likely layout
      rw [hv,hh] at he; change Rooted L _ ((Finset.card _ : ℝ)* M); rw [card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one, show ((s.card:ℝ)+1)*M=M+s.card*M by ring]; convert he.add ih using 1; abel
lemma hoist_drift (k:ℕ){F:Field (Fin k) X} (hu:Ripple l L u) (hr:Weirs u R b b)(hs:Weirs u S b b)(hx: Weirs u (R-S) c c)(hf:Rooted l F d): Rooted L (hoist R F-hoist S F) (k*(d*c*b^(k-1))):= by unfold hoist; rw [← prints_sub]; apply Rooted.even; simpa using psub Finset.univ hu hf hr hs hx -- card casts
end stat
namespace Balance
-- indicator H= < or ≤; keep pair of cut requests rightwards
variable {α:ℕ→Type}{l: ∀ i,Pulse.Range (α i)}{H:ℕ→ℕ→Prop}{R S:∀ i,ℕ→Field ι (α i)}
def Base (e:Oasis G)(H:ℕ→ℕ→Prop)(l: ∀ i,Pulse.Range (α i))(F:∀ i,ℕ→ Field ι (α i)) := e.Permit fun i b=> ∀ n,H i n→Rooted (l i) (F i n) b
def Shade (e:Oasis G)(H:ℕ→ℕ→Prop)(l: ∀ i,Pulse.Range (α i))(F:∀ i,ℕ→ Field ι (α i)):=e.Permit fun i b=> ∀ n m,H i n→H i m→Rooted (l i) (F i n-F i m) (b*e.η i (min n m))
def Stable (e:Oasis G)(H:ℕ→ℕ→Prop)(l: ∀ i,Pulse.Range (α i))(F:∀ i,ℕ→ Field ι (α i)):=Base e H l F ∧ Shade e H l F
variable {F F' :ℕ→ℕ→ℝ}
def Funds (e:Oasis G)(H:ℕ→ℕ→Prop)(f: ℕ→ℕ→ℝ) := (e.Permit fun i b=> ∀ n,H i n→ ‖f i n‖ ≤ b) ∧ (e.Permit fun i b=> ∀ n m,H i n→H i m→ ‖f i n-f i m‖ ≤ b * e.η i (min n m))
namespace Funds
lemma zero (a:ℝ) : Funds e H (fun _ _=>a):= ⟨⟨_,e.fair_const ‖a‖ (by positivity),fun _ _ _=>le_rfl⟩,_,e.fair_const 0 le_rfl,fun _ _ _ _ _=>by simp⟩
lemma mul (h:Funds e H F)(k:Funds e H F') : Funds e H (fun i n=>F i n* F' i n):= by
   obtain ⟨⟨p,hp,Hq⟩,q,hq,Hg⟩:=h; obtain ⟨⟨m,hM,hv⟩,n,hn,hh⟩:=k; refine ⟨⟨_,hp.mul hM,fun i n h=>?_⟩,_, (hp.mul hn).add (hq.mul hM),fun i n' m' h k=>?_⟩
   · dsimp only; rw [norm_mul]; exact mul_le_mul (Hq i n h) (hv i n h) (norm_nonneg _) (hp.bank i)
   let a:= F i n'; let b:= F i m'; let c:=F' i n'; let d:= F' i m'; change ‖a*c-b*d‖≤_; rw [show a*c-b*d=a*(c-d)+(a-b)*d by ring]; refine (norm_add_le ..).trans ?_; rw [norm_mul,norm_mul]; have ht:=mul_le_mul (Hq i n' h) (hh i n' m' h k) (norm_nonneg _) (hp.bank i); have hz:= mul_le_mul (Hg i n' m' h k) (hv i m' k) (norm_nonneg _) (mul_nonneg (hq.bank i) (e.η_pos ..).le); exact (add_le_add ht hz).trans_eq (by ring)
lemma add (h:Funds e H F)(hp:Funds e H F'): Funds e H (fun i n=> F i n+F' i n):= by obtain ⟨⟨p,hp',he⟩,q,Hq,h⟩:=h; obtain ⟨⟨v,hv,ht⟩,w,hw,hp⟩:=hp; exact ⟨⟨_,hp'.add hv,fun i n hn=>(norm_add_le ..).trans (add_le_add (he i n hn) (ht i n hn))⟩,_,Hq.add hw,fun i n m hn hm=>by simp only [add_sub_add_comm (F i n),add_mul]; exact (norm_add_le ..).trans (add_le_add (h i n m hn hm) (hp i n m hn hm))⟩ -- lemma
lemma sum {β:Type}{F:β→ℕ→ℕ→ℝ}(T:Finset β)(hp:∀ i∈T,Funds e H (F i)): Funds e H (fun i n=>∑ k∈T,F k i n):= by induction T using Finset.induction with| empty=>simp only [sum_empty]; apply zero| insert i v hi ih=>simp_rw [sum_insert hi]; exact (hp i (mem_insert_self ..)).add (ih fun j hj=> hp j (mem_insert_of_mem hj))
end Funds
namespace Stable
lemma cong (h:Stable e H l R)(hk:∀ i n,H i n→ R i n=S i n): Stable e H l S:= by obtain ⟨⟨p,hp,hv⟩,q,hq,hg⟩:=h; exact ⟨⟨p,hp,fun i m hi=> hk i m hi ▸ hv i m hi⟩,q,hq,fun i n m hi he=> by rw [← hk i n hi,← hk i m he]; exact hg i n m hi he⟩
lemma eq (h:Stable e H l R)(hk:∀ i n,R i n=S i n): Stable e H l S:= h.cong fun i n _=> hk i n
lemma zero : Stable (ι:=ι) e H l (fun _ _=>0) := ⟨⟨_,e.fair_const 0 le_rfl,fun _ _ _=> Rooted.tranquility ..⟩,_,e.fair_const 0 le_rfl,fun i m n _ _=>by simp only [sub_zero,zero_mul]; exact Rooted.tranquility ..⟩
lemma costsEmpty [IsEmpty ι] : Stable e H l R := ⟨⟨_,e.fair_const 0 le_rfl,fun _ _ _=> Rooted.emptySpace _ _ le_rfl⟩,_,e.fair_const 0 le_rfl,fun _ _ _ _ _=>Rooted.emptySpace _ _ (zero_mul ..|>.ge)⟩
lemma add (h:Stable e H l R)(hk:Stable e H l S): Stable e H l (fun i n=> R i n+S i n):= by obtain ⟨⟨p,hp,hv⟩,q,hq,hg⟩:=h; obtain ⟨⟨u,hu,ht⟩,t,hd,hk⟩:=hk; exact ⟨⟨_,hp.add hu,fun i m hm=>(hv i m hm).add (ht i m hm)⟩,_, hq.add hd,fun i n m hn hm=>by simp only [add_sub_add_comm (R i n),add_mul]; exact (hg i n m hn hm).add (hk i n m hn hm) ⟩
lemma scale (hg:Stable e H l R)(hp:Funds e H F): Stable e H l (fun i n=> F i n • R i n):= by
   obtain ⟨⟨p,hp',hF⟩,q,hq,hQ⟩:=hp; obtain ⟨⟨v,hv,ht⟩,w,hw,hW⟩:=hg; refine ⟨⟨_,hp'.mul hv,fun i n h=> ((ht i n h).smul (F i n)).weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right (hF i n h) (hv.bank i))⟩,_,(hp'.mul hw).add (hq.mul hv),fun i n m hn hm=>?_⟩
   let M:=F i n; let N:= F i m; change Rooted _ (M • R i n-N • R i m) _; rw [show _- N • R i m=M • (R i n-R i m)+(M-N) • R i m from (by rw [smul_sub,sub_smul]; abel)]; refine (((hW i n m hn hm).smul M).add ((ht i m hm).smul (M-N))).weaken (fun _=>le_rfl) ?_; exact (add_le_add (mul_le_mul_of_nonneg_right (hF i n hn) (mul_nonneg (hw.bank i) (e.η_pos ..).le)) (mul_le_mul_of_nonneg_right (hQ i n m hn hm) (hv.bank i))).trans_eq (by ring)
lemma smul (h:Stable e H l R)(b:ℝ): Stable e H l (fun i n=> b • R i n):= h.scale (Funds.zero b)
lemma neg (h:Stable e H l R): Stable e H l (fun i n=> -R i n):=by simpa only [neg_one_smul] using h.smul (-1)
lemma sub (h:Stable e H l R)(hk:Stable e H l S): Stable e H l (fun i n=>R i n-S i n):= by simpa only [← sub_eq_add_neg] using h.add hk.neg
lemma sum {β:Type}{F:β→∀ i,ℕ→Field ι (α i)}(T:Finset β)(hp:∀ i∈T,Stable e H l (F i)): Stable e H l (fun i n=>∑ j∈T,F j i n):= by induction T using Finset.induction with|empty=> simp only [Finset.sum_empty]; apply zero|insert i v hi ih=> simp_rw [Finset.sum_insert hi]; exact (hp i (mem_insert_self ..)).add (ih fun j hj=> hp j (mem_insert_of_mem hj))
lemma even (h:Stable e H l R): Stable e H l (fun i n=> printRun (R i n)):= by obtain ⟨⟨p,hp,hg⟩,q,hq,h⟩:=h; exact ⟨⟨p,hp,fun i n ht=> (hg i n ht).even⟩,q,hq,fun i n m hy ht=> by rw [← prints_sub]; exact (h i n m hy ht).even⟩
lemma renew {κ:Type}[Fintype κ] (p:ι≃κ) (h:Stable e H l R): Stable e H l (fun i n=> reorder p (R i n)):= by obtain ⟨⟨f,hf,hg⟩,q,hq,h⟩:=h; exact ⟨⟨f,hf,fun i n ht=> (hg i n ht).renew p⟩,q,hq,fun i n m ht he=> (h i n m ht he).renew p⟩
lemma further (h:Stable e H l R){k:∀ i,Pulse.Range (α i)}(hk:∀ i (x:ι→α i),(k i).bill x ≤ (l i).bill x): Stable e H k R:= by obtain ⟨⟨p,hp,hv⟩,q,hq,hg⟩:=h; exact ⟨⟨p,hp,fun i n hi=> (hv i n hi).weaken (hk i) le_rfl⟩,q,hq,fun i n m hn hm=>(hg i n m hn hm).weaken (hk i) le_rfl⟩
lemma all (r:∀ i,Field ι (α i))(h: e.Permit fun i b=> Rooted (l i) (r i) b) : Stable e H l (fun i _=> r i):= by obtain ⟨p,hp,h⟩:=h; exact ⟨⟨_,hp,fun i _ _=> h i⟩,_,e.fair_const 0 le_rfl,fun _ _ _ _ _=>by simp only [sub_self,zero_mul]; exact Rooted.tranquility .. ⟩
end Stable
variable {k q:ℕ}{β:ℕ→Type}{J:∀ i, Pulse.Range (β i)}{u : ∀ i,α i→β i→ℝ}{Z:∀ i,ℕ→α i→α i→ℝ}{R:∀ i,ℕ→α i→ β i →ℝ}
structure Reef (e:Oasis G)(H:ℕ→ℕ→Prop)(l:∀ i,Pulse.Range (α i))(Z :∀ i, ℕ→ α i → α i → ℝ):Prop where
   coag : e.Permit fun i b=> ∀ n,H i n→ Pulse.Track (l i) (Z i n) b
   off : e.Permit fun i b=> ∀ n m,H i n→ H i m→ Pulse.Track (l i) (Z i n-Z i m) (b*e.η i (min n m))
structure Loans (e:Oasis G)(H:ℕ→ℕ→Prop)(u: ∀ i,α i → β i → ℝ)(R:∀ i,ℕ→ α i → β i → ℝ):Prop where
   coag : e.Permit fun i b=> ∀ n,H i n→ Weirs (u i) (R i n) b b
   off : e.Permit fun i b=> ∀ n m,H i n→ H i m→ let v:=b*e.η i (min n m); Weirs (u i) (R i n-R i m) v v
lemma Reef.borrow (h:Reef e H l Z): Loans e H (fun i=> (l i).step) Z:= by obtain ⟨⟨p,hp,hq⟩, q,hg,hc⟩:=h; exact ⟨⟨p,hp,fun i n h=> (hq i n h).flow⟩, q,hg,fun i n m hp ht=> (hc i n m hp ht).flow⟩
namespace Loans
-- expose P.1 witness for direct use
lemma hoistVal (h:Loans e H u R)(hu:∀ i, Ripple (l i) (J i) (u i)) {F:∀ i,ℕ→ Field (Fin k) (α i)}(hp:Base e H l F): Base e H J (fun i n=> hoist (R i n) (F i n)):= by obtain ⟨p,hp',ht⟩:=hp; obtain ⟨q,hq,hc⟩:=h.coag; exact ⟨_, (hq.mul hp').mul (hq.pow (k-1)),fun i n h=> hoist_pay (hu i) (hc i n h) (ht i n h) ⟩
lemma driftFee (h:Loans e H u R)(hu:∀ i,Ripple (l i) (J i) (u i)){F:∀ i,ℕ→Field (Fin k) (α i)} (hp:Base e H l F): e.Permit (fun i t=> ∀ n m,H i n→H i m→ Rooted (J i) (hoist (R i n) (F i m)-hoist (R i m) (F i m)) (t*e.η i (min n m))):= by
   obtain ⟨p,hp',ht⟩:=hp; obtain ⟨⟨a,ha,hA⟩,b,hb,hB⟩:=h; refine ⟨_,(e.fair_const k (by positivity)).mul ((hp'.mul hb).mul (ha.pow (k-1))),fun i n m hn hm=>?_⟩; convert hoist_drift k (hu i) (hA i n hn) (hA i m hm) (hB i n m hn hm) (ht i m hm) using 1; ring
lemma lift (h:Loans e H u R)(hu:∀ i, Ripple (l i) (J i) (u i)){F:∀ i,ℕ→ Field (Fin k) (α i)} (hp:Stable e H l F): Stable e H J (fun i n=> hoist (R i n) (F i n)):= by
   by_cases hi:k=0; · subst k; exact Stable.costsEmpty
   letI : NeZero k:= ⟨hi⟩; obtain ⟨p,hp',hP⟩:= h.driftFee hu hp.1; obtain ⟨a,ha,hA⟩:= h.coag; refine ⟨h.hoistVal hu hp.1,?_⟩; obtain ⟨⟨u',hu',hU⟩, v,hv,hV⟩:=hp; refine ⟨_, ((ha.mul hv).mul (ha.pow (k-1))).add hp', fun i n m hn hm=>?_ ⟩
   have he:= (hoist_pay (hu i) (hA i n hn) (hV i n m hn hm)).add (hP i n m hn hm); rw [hoist_sub (hu i) (hA i n hn) (hU i n hn) (hU i m hm)] at he; convert he using 1; abel; ring
end Loans
namespace Reef
lemma closes {x:∀ i,ℕ→Field (Option (Option ι)) (α i)} (h:Reef e H l Z)(hp:Stable e H l x): Stable e H l (fun i n=> loop (Z i n) (x i n)):= by
   rcases isEmpty_or_nonempty ι with hI|hI; · apply Stable.costsEmpty
   obtain ⟨⟨p,hp,hq⟩,q,Hq,hc⟩:= hp; obtain ⟨⟨a,ha,hA⟩,b,hb,hB⟩:=h; refine ⟨⟨_,ha.mul hp,fun i n h=> loop_root (hA i n h) (hq i n h)⟩,_, (ha.mul Hq).add (hb.mul hp), fun i n m hn hm=>?_⟩; have he:= (loop_root (hA i n hn) (hc i n m hn hm)).add (loop_root (hB i n m hn hm) (hq i m hm)); rw [loop_less (hA i n hn) (hq i n hn) (hq i m hm), loop_line (hA i n hn).cap (hA i m hm).cap (hq i m hm) (ha.bank i) (ha.bank i)] at he; convert he using 1; abel; ring
lemma connect {κ:Type} [Fintype κ]{x:∀ i,ℕ→Field (Option ι) (α i)}{y:∀ i,ℕ→Field (Option κ) (α i)} (h:Reef e H l Z)(hp:Stable e H l x)(hk:Stable e H l y): Stable e H l (fun i n=> stitch (Z i n) (x i n) (y i n)):= by
   rcases isEmpty_or_nonempty (ι⊕κ) with hI|hI; · apply Stable.costsEmpty
   obtain ⟨⟨p,hp,hq⟩,q,Hq,hc⟩:=hp; obtain ⟨⟨a,ha,hA⟩,b,hb,hB⟩:= h; obtain ⟨⟨v,hv,hV⟩,w,hw,hW⟩:=hk; refine ⟨⟨_,hp.mul (ha.mul hv),fun i n h=> stitch_root (hA i n h) (hq i n h) (hV i n h)⟩,_, ((Hq.mul (ha.mul hv)).add (hp.mul (hb.mul hv))).add (hp.mul (ha.mul hw)),fun i n m hn hm=> ?_⟩; have he:= stitch_diff (hA i n hn) (hA i m hm) (hB i n m hn hm) (hq i n hn) (hq i m hm) (hV i n hn) (hV i m hm) (hc i n m hn hm) (hW i n m hn hm); convert he using 1; ring
lemma degree {x:∀ i,ℕ→Field (Fin (k+2)) (α i)} (h:Reef e H l Z) (hp:Stable e H l x): Stable e H l (fun i n=> Pulse.degree (Z i n) (x i n)):= Stable.smul (Stable.even (h.closes (hp.renew (spanLift _)))) _
lemma list {j:ℕ}{x y:∀ i, ℕ→Pulse.Rack (α i)} (h:Reef e H l Z)(hp:Stable e H l (fun i n=> x i n (k+1)))(hk:Stable e H l (fun i n=> y i n (q+1))) : Stable e H l (fun i n=> light (Z i n) j k q (x i n) (y i n)):= by
    unfold light; by_cases he:k+q=j; · subst j; simp only; exact Stable.smul (Stable.even (Stable.renew finSumFinEquiv (h.connect (x:=fun i n=>squeeze (x i n (k+1))) (hp.renew (finSuccEquiv _)) (hk.renew (finSuccEquiv _))))) _
    simp_rw [dif_neg he]; exact Stable.zero
end Reef
end Balance
end Reserve
end
end YM.Contacts.Barrage
