import YM.Contacts.Prairie.Lease
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
-- basic family of costs on real linear spaces; phrase gains independent of any NormedSpace completeness
variable {X Y Z:Type*}
def Bases (S:Boom)(P : X→ℝ→Prop)(f:Word→X):Prop:= ∃ p≥(0:ℝ),∀ n,OK S n → P (f n) p
def Diff (S:Boom)(P : X→ℝ→Prop)[Sub X](f:Word→X):Prop:= ∃ b≥(0:ℝ),∀ p q u, OK S p → OK S q → OK S u → P (f (u++p)-f (u++q)) (b*mileage u)
def Holds (S:Boom)(P:X→ℝ→Prop)[Sub X] (f:Word→X) := Bases S P f ∧ Diff S P f
variable {S:Boom}{P Q : X→ℝ→Prop}{R:Y→ℝ→Prop}{f g:Word→X}{Z':Word→Y}{c:ℝ}
lemma Bases.eq (h:Bases S P f)(ht:∀ u,OK S u→ f u=g u): Bases S P g:= by obtain ⟨b,hb,hp⟩:=h; exact ⟨b,hb,fun u hu=>ht u hu ▸ hp u hu⟩
lemma Bases.trade (h:Bases S P f)(a:ℝ)(ha:0≤a)(he:∀ x v,P x v→Q x (a*v)): Bases S Q f:= by obtain ⟨b,hb,hp⟩:=h; exact ⟨a*b,mul_nonneg ha hb,fun n hn=> he _ _ (hp n hn)⟩
lemma Diff.trade [Sub X] (h:Diff S P f)(a:ℝ)(ha:0≤a)(he:∀ x v,P x v→ Q x (a*v)): Diff S Q f:= by obtain ⟨b,hb,hp⟩:=h; exact ⟨a*b,mul_nonneg ha hb,fun p q u hi hj hk=> by rw [mul_assoc]; apply he _ _ (hp p q u hi hj hk)⟩
namespace Holds
lemma map [Sub X][Sub Y] (h:Holds S P f)(F:X→Y)(hp:∀ p q,F (p-q)= F p-F q)(ht : ∀ v x,P x v → R (F x) v): Holds S R (fun n=>F (f n)):= by obtain ⟨⟨p,hp',hP⟩,q,hq,hQ⟩:=h; exact ⟨⟨_,hp',fun n hn=> ht _ _ (hP n hn)⟩,_,hq,fun p q u hi hj hk=> by simp only [← hp]; exact ht _ _ (hQ p q u hi hj hk) ⟩
lemma trade [Sub X] (h:Holds S P f)(a:ℝ)(ha:0≤a)(he:∀ x v,P x v→Q x (a*v)): Holds S Q f:= ⟨h.1.trade a ha he,h.2.trade a ha he⟩
lemma weaken [Sub X](h:Holds S P f)(ht:∀ v x,P x v→Q x v): Holds S Q f:= h.trade 1 zero_le_one (fun x v he=>by rw [one_mul]; exact ht v x he)
lemma eq [Sub X](h:Holds S P f)(hq:∀ p,OK S p→ f p=g p): Holds S P g:= by refine ⟨h.1.eq hq,?_⟩; obtain ⟨v,hv,h⟩:=h.2; exact ⟨v,hv,fun p q u hi hj hk=>by rw [← hq _ (hk.append hi),← hq _ (hk.append hj)]; exact h p q u hi hj hk⟩
lemma init {x:X}[Sub X] [Add X] (h:P (x-x) 0) (hh:P x c) (hv:0≤c): Holds S P (fun _=>x):= ⟨⟨c,hv,fun _ _=>hh⟩,0,le_rfl,fun p q u _ _ _=> by simpa only [zero_mul] using h⟩
lemma cons [Sub X] (h:Holds S P f)(hh:∀ x,Monotone (P x))(a:Step)(he:a∈ S): Holds S P (fun u=> f (a::u)):= by
   obtain ⟨⟨v,hv,H⟩,b,hb,G⟩:=h; exact ⟨⟨v,hv,fun u hu=> H _ (hu.cons he)⟩,b,hb,fun p q u hi hj hk=> hh _ (mul_le_mul_of_nonneg_left (by rw [mileage_cons]; apply div_le_self (mileage_pos _).le (by norm_num)) hb) (G p q (a::u) hi hj (hk.cons he))⟩
lemma binary [AddCommGroup X] (h:Holds S P f)(ht:Holds S P g)(hx:∀ a b x y,P x a→P y b→P (x+y) (a+b)): Holds S P (fun n=> f n+g n):= by
   obtain ⟨⟨v,hv,H⟩,b,hb,h⟩:=h; obtain ⟨⟨w,hw,G⟩,c,hc,ht⟩:=ht; exact ⟨⟨_,add_nonneg hv hw,fun i hi=> hx _ _ _ _ (H i hi) (G i hi)⟩,_,add_nonneg hb hc,fun p q u hi hj hk=> by rw [add_sub_add_comm (f (u++p)),add_mul]; exact hx _ _ _ _ (h p q u hi hj hk) (ht p q u hi hj hk) ⟩
end Holds
abbrev Backs (S:Boom)(f:Word→ℝ):= Holds S (fun x v=> ‖x‖≤v) f
namespace Backs
variable {a b: Word→ℝ}
lemma given (v:ℝ):Backs S (fun _=>v):= Holds.init (P:= fun x v=> ‖x‖≤v) (by simp) le_rfl (norm_nonneg v)
lemma add (h:Backs S a)(g:Backs S b): Backs S (fun u=>a u+b u):= h.binary g fun _ _ _ _ ht he=> (norm_add_le ..).trans (add_le_add ht he)
lemma mul (h:Backs S a)(g:Backs S b): Backs S (fun u=>a u*b u):= by
   obtain ⟨⟨v,hv,hV⟩,p,hp,hP⟩:=h; obtain ⟨⟨w,hw,hW⟩,q,hq,hQ⟩:=g; refine ⟨⟨_,mul_nonneg hv hw,fun i hi=> by exact (norm_mul ..).le.trans (mul_le_mul (hV _ hi) (hW _ hi) (norm_nonneg _) hv)⟩,_, add_nonneg (mul_nonneg hv hq) (mul_nonneg hp hw),fun i j u hi hj hu=>?_⟩; let x := u++i; let y:=u++j; change ‖a x*b x-a y*b y‖ ≤ _; have hZ:= mileage_pos u; calc
    _ = ‖a x*(b x-b y)+(a x-a y)*b y‖:= by congr 1; ring
    _ ≤ _:= le_trans (norm_add_le ..) (le_trans (add_le_add ((norm_mul ..).le.trans (mul_le_mul (hV _ (hu.append hi)) (hQ i j u hi hj hu) (norm_nonneg _) hv)) ((norm_mul ..).le.trans (mul_le_mul (hP i j u hi hj hu) (hW _ (hu.append hj)) (norm_nonneg _) (mul_nonneg hp hZ.le)))) (le_of_eq (by ring)))
lemma sum (s:Finset X){a:X→Word→ℝ}(h:∀ i∈s,Backs S (a i)): Backs S (fun n=>∑ i∈s,a i n):= by induction s using Finset.induction with|empty=>simp only [sum_empty]; exact Backs.given _|insert i v hi ih=>simp_rw [sum_insert hi]; exact Backs.add (h i (mem_insert_self ..)) (ih fun j hj=>h j (mem_insert_of_mem hj))
end Backs
section
variable {ι α:Type}[Fintype ι] {l k:Pulse.Range α} {f g:Word→Field ι α}
abbrev Will (S:Boom)(l:Pulse.Range α)(f: Word→ Field ι α):= Bases S (Rooted l) f
abbrev Fleet (S:Boom)(l:Pulse.Range α)(f: Word→ Field ι α):= Holds S (Rooted l) f
namespace Fleet
lemma eq (h:Fleet S l f)(ht:∀ n,OK S n→ f n=g n): Fleet S l g:= Holds.eq h ht
lemma given {A:Field ι α}(h:Rooted l A b): Fleet S l (fun _=> (A:Field ι α)):= Holds.init (P:=Rooted l) (by rw [sub_self]; apply Rooted.tranquility) h h.cash
lemma fzero : Fleet (ι:=ι) S l (fun _=>0):= given (Rooted.tranquility _)
lemma empty [IsEmpty ι]: Fleet S l f:=⟨⟨_,show 0≤(0:ℝ) from le_rfl,fun _ _=> Rooted.emptySpace _ _ le_rfl⟩,_,show 0≤(0:ℝ) from le_rfl,fun i j u _ _ _=> by simp only [zero_mul]; exact Rooted.emptySpace _ _ le_rfl⟩
lemma next (h:Fleet S l f)(t:Step)(ht:t∈S):Fleet S l (fun p=>f (t::p)):= h.cons (fun _ _ _ ha he=> he.weaken (fun _=>le_rfl) ha) t ht
lemma add (h:Fleet S l f)(ht:Fleet S l g):Fleet S l (fun n=> f n+g n):= h.binary ht (fun _ _ _ _=> fun hx hy=> Rooted.add hx hy)
lemma scale {p: Word→ℝ} (h:Backs S p)(he:Fleet S l f): Fleet S l (fun i=> p i • f i):= by
   obtain ⟨⟨w,hw,hW⟩,y,hy,hY⟩:=h; obtain ⟨⟨x,hx,hX⟩,z,hz,hZ⟩:=he; refine ⟨⟨_,mul_nonneg hw hx,fun i hi=> ((hX _ hi).smul _).weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right (hW _ hi) hx)⟩,_, add_nonneg (mul_nonneg hw hz) (mul_nonneg hy hx),fun i j u hi hj hu=>?_⟩
   let n:= u++i; let m:= u++j; change Rooted l (p n • f n - p m • f m) _; rw [show _-p m • f m=p n • (f n-f m)+(p n-p m) • f m from by rw [smul_sub,sub_smul]; abel]; have h':= mileage_pos u; refine ((((hZ i j u hi hj hu).smul (p n))).add ((hX _ (hu.append hj)).smul (p n-p m))).weaken (fun _=>le_rfl) ((add_le_add (mul_le_mul_of_nonneg_right (hW _ (hu.append hi)) (mul_nonneg hz h'.le)) (mul_le_mul_of_nonneg_right (hY i j u hi hj hu) hx)).trans_eq ?_); ring
lemma smul (h:Fleet S l f)(v:ℝ): Fleet S l (fun n=> v • f n):= scale (Backs.given _) h
lemma neg (h:Fleet S l f): Fleet S l (fun i=> -f i):= by simpa only [neg_one_smul] using Fleet.smul h (-1)
lemma sub (h:Fleet S l f)(ht:Fleet S l g): Fleet S l (fun i=>f i - g i):= by simpa only [←sub_eq_add_neg] using Fleet.add h (Fleet.neg ht)
lemma even (h:Fleet S l f): Fleet S l (fun i=> printRun (f i)):= Holds.map (R:=Rooted l) h (fun f=>printRun f) prints_sub (fun _ _ hx=> Rooted.even hx)
lemma rename {κ:Type} [Fintype κ] (e:ι≃κ) (h:Fleet S l f): Fleet S l (fun i=> reorder e (f i)):= Holds.map (R:=Rooted l) h _ (fun _ _=>rfl) fun _ _ ht=> ht.renew e
lemma weaken (h:Fleet S l f)(he:∀ x:ι→α,k.bill x≤l.bill x): Fleet S k f:= Holds.weaken h (fun _ _ hx=> hx.weaken he le_rfl)
lemma sum (s:Finset X){f:X→Word→Field ι α}(h:∀ x∈s,Fleet S l (f x)): Fleet S l (fun i=>∑ x∈s,f x i):= by induction s using Finset.induction with|empty=>simp only [sum_empty]; exact Fleet.fzero | insert i v hi ih=> simp_rw [sum_insert hi]; exact Fleet.add (h i (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj))
end Fleet
end
end Parcel
end
end YM.Contacts.Prairie
