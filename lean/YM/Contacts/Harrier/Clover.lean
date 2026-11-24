import YM.Contacts.Prairie.Motion
import YM.Contacts.Harrier.Gift
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
/-! # Uniform transmission for multiple parameters held along words -/
namespace Mileage
open Prairie Prairie.Parcel Barrage Barrage.Reserve
variable {U:Type} {S:Boom} {F Y:Word→U→Field ι X} 
-- U extra parameter (profile, short-step unit-norm probes, etc.)
variable [Fintype ι] [Fintype κ]{τ:X→A→ℝ}
def Stable (U X:Type)(S:Boom)(l:Pulse.Range X)(F: Word →U→Field ι X):Prop:= Holds S (fun y b=> ∀ u, Rooted l (y u) b) F
variable {l:Pulse.Range X}{q:Pulse.Range A}{G:Word→X→A→ℝ}{C:Word→X→X→ℝ}
local notation "L" => Rooted l
namespace Stable
lemma pulse (h:Stable U X S l F)(HE:∀ i,OK S i→∀ p,F i p=Y i p): Stable U X S l Y:= Holds.eq h (fun i hi=>funext fun p=> HE i hi p)
lemma gift (g:U→Field ι X)(h:∀ u,L (g u) b)(ht:0≤b): Stable U X S l (fun _=>g):= Holds.init (P:=fun (f:U→Field ι X) x=>∀ u,L (f u) x) (fun u => by simp only [sub_self,Pi.zero_apply]; apply Rooted.tranquility) h ht
lemma zero : Stable (ι:=ι) U X S l (fun _=>0):= gift 0 (fun _=> Rooted.tranquility _) le_rfl
lemma for_all (h:Fleet S l (f:Word→Field ι X)): Stable U X S l (fun p _=> f p):= Holds.map (R:=fun (f:U→Field ι X) a=>∀ u:U,L (f u) a) h (fun f _=> f) (fun _ _=> rfl) (fun _ _ h' _=> h')
lemma empty [IsEmpty ι]: Stable U X S l F:= by refine ⟨⟨0,le_rfl,fun p _ u=> Rooted.emptySpace _ _ le_rfl⟩,0,le_rfl,fun i j u _ _ _ t=> Rooted.emptySpace _ _ (by rw [zero_mul])⟩
lemma add (h:Stable U X S l F)(H:Stable U X S l Y): Stable U X S l (fun p x=> F p x+ Y p x):= Holds.binary (P:=fun (f:U→Field ι X) b=>∀ u,L (f u) b) h H (fun _ _ _ _ h he u=> (h u).add (he u))
lemma sum' {f:α→Word→U→ Field ι X}(s:Finset α)(h:∀ i∈s,Stable U X S l (f i)):Stable U X S l (fun p u=>∑ x∈s,f x p u):= by induction s using Finset.induction with|empty=>simp only [Finset.sum_empty]; exact Stable.zero| insert i v hi ih=> simp_rw [sum_insert hi]; exact Stable.add (h i (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma smul (h:Stable U X S l F)(a:ℝ): Stable U X S l (fun p u=> a • F p u):= by obtain ⟨⟨c,hc,hC⟩,b,hb,h⟩:=h; refine ⟨⟨_,mul_nonneg (norm_nonneg a) hc, fun p hp u=> (hC p hp u).smul a⟩,_, mul_nonneg (norm_nonneg a) hb,fun p q v hp hq hv u=>?_⟩; change L (a • F (v++p) u - a • F (v++q) u) _; rw [← smul_sub,mul_assoc]; exact (h p q v hp hq hv u).smul a
lemma even (h:Stable U X S l F): Stable U X S l (fun p u=>printRun (F p u)):= Holds.map (R:=fun (f:U→Field ι X) a=>∀ u,L (f u) a) h (fun f u=> printRun (f u)) (fun _ _ =>funext fun _=> prints_sub ..) (fun _ _ h' u=> (h' u).even)
lemma rename (h:Stable U X S l F)(e:ι≃κ): Stable U X S l (fun p u=> reorder e (F p u)) := Holds.map (R:=fun (f:U→Field κ X) a=> ∀ u,L (f u) a) h (fun f u=> reorder e (f u)) (fun _ _=>rfl) (fun _ _ h' u=> (h' u).renew e)
lemma hoist (H:Threads S τ G)(hu:Ripple l q τ){F:Word→U→Field (Fin k) X}(h:Stable U X S l F):Stable U A S q (fun p x=> Forge.hoist (G p) (F p x)):= by
   by_cases hk:k=0; · subst k; exact empty
   letI : NeZero k:= ⟨hk⟩; obtain ⟨⟨b,hb,hB⟩,c,hc,hC⟩:=H; obtain ⟨⟨v,hv,H⟩,w,hw,hW⟩:=h; let W:=b^(k-1); have h' :0≤W := pow_nonneg hb _; refine ⟨⟨(b*v)*W,mul_nonneg (mul_nonneg hb hv) h', fun i hi u=> hoist_pay hu (hB _ hi) (H _ hi u)⟩,_, add_nonneg (mul_nonneg (mul_nonneg hb hw) h') (mul_nonneg (Nat.cast_nonneg k) (mul_nonneg (mul_nonneg hv hc) h')),fun i j u hi hj hk f=>?_⟩
   have hk1:=hk.append hi; have hk2:=hk.append hj; let n:=u++i; let m:=u++j; have hh:= (hoist_pay hu (hB n hk1) (show L (F n f-F m f) _ from hW i j u hi hj hk f)).add (hoist_drift k hu (hB n hk1) (hB m hk2) (hC i j u hi hj hk) (H m hk2 f)); rw [hoist_sub hu (hB _ hk1) (H _ hk1 _) (H _ hk2 _)] at hh; convert hh using 1; swap; · unfold W; ring
   change _- Forge.hoist (G m) (F m f)=_; abel -- missing explicit
lemma loop {J : Word→U→ Field (Option (Option ι)) X}(h: Stable U X S l J)(hp:Climb S l C): Stable U X S l (fun p u=>Pulse.loop (C p) (J p u)):= by
   rcases isEmpty_or_nonempty ι with _|_; · exact empty
   obtain ⟨⟨a,ha,A⟩,b,hb,B⟩:= hp; obtain ⟨⟨c,hc,H⟩,d,hd,D⟩:=h; refine ⟨⟨_,mul_nonneg ha hc,fun i h u=>loop_root (A _ h) (H _ h u)⟩,_,add_nonneg (mul_nonneg ha hd) (mul_nonneg hb hc),fun i j u hi hj hk v=>?_⟩; let n:=u++i; let m:=u++j; have he := hk.append hi; have ht:=hk.append hj; have hp:= (loop_root (A n he) (show L (J n v - J m v) _ from D i j u hi hj hk v)).add (loop_root (B i j u hi hj hk) (H m ht v)); rw [loop_less (A n he) (H n he _) (H m ht _), loop_line (Pulse.Track.cap (A n he)) (Pulse.Track.cap (A m ht)) (H m ht _) ha ha] at hp; convert hp using 1; change _ - Pulse.loop (C m) (J m v) = _; abel; ring
lemma stitch {F:Word→ U→Field (Option ι) X}{Y:Word→U→Field (Option κ) X} (h:Stable U X S l F)(hy:Stable U X S l Y)(ht:Climb S l C):Stable U X S l (fun i u=> Pulse.stitch (C i) (F i u) (Y i u)):= by
   rcases isEmpty_or_nonempty (ι⊕κ) with _|_; · exact empty
   obtain ⟨⟨b,hb,B⟩,c,hc,H⟩:=ht; obtain ⟨⟨x,hx,X'⟩,v,hv,V⟩:=h; obtain ⟨⟨y,hy,Y'⟩,w,hw,W⟩:=hy; refine ⟨⟨_,mul_nonneg hx (mul_nonneg hb hy),fun i hi t=> stitch_root (B i hi) (X' i hi t) (Y' i hi t)⟩,_,add_nonneg (add_nonneg (mul_nonneg hv (mul_nonneg hb hy)) (mul_nonneg hx (mul_nonneg hc hy))) (mul_nonneg hx (mul_nonneg hb hw)), fun i j u hi hj hk t=>?_⟩; let n:=u++i; let m:=u++j; have he:=hk.append hi; have hh:= hk.append hj; convert stitch_diff (B n he) (B m hh) (H i j u hi hj hk) (X' n he t) (X' m hh t) (Y' n he t) (Y' m hh t) (V i j u hi hj hk t) (W i j u hi hj hk t) using 1 <;> first | rfl| ring
lemma light {F V: Word→U→Pulse.Rack X}(h:Climb S l C)(ht:Stable U X S l (fun i v=>F i v (k+1)))(hh:Stable U X S l (fun i v=> V i v (n+1))): Stable U X S l (fun i v=> Pulse.light (C i) j k n (F i v) (V i v)):= by
   unfold Pulse.light; by_cases he:k+n=j; swap; · simp_rw [dif_neg he]; exact Stable.zero
   subst j; simp only; exact Stable.smul (Stable.even (Stable.rename (Stable.stitch (F:=fun i v=>squeeze (F i v (k+1))) (ht.rename (finSuccEquiv _)) (hh.rename (finSuccEquiv _)) h) finSumFinEquiv)) _
-- quantities only at the occurrence energy request
lemma mass {T:Word→U→House X}(h:∀ i ≤ k,∀ r, Stable U X S l (fun p u=> T p u i r))(ht:Climb S l C): Stable U X S l (fun p u=> Form.massaged (C p) (T p u) k r):= by
   let A p v:=gathering (C p) (T p v); suffices hz:∀ t,∀ n ≤ k,∀ r,Stable U X S l (fun p v=> A p v t n r) by exact Stable.sum' _ fun t _=>hz t k le_rfl r
   intro t; induction t using Nat.strongRecOn with| _ t ih=>
   intro n hh r; cases t; · simp only [A,gathering_start]; exact h n hh r
   rename_i t; simp_rw [A,gathering_next,wake]; apply Stable.smul; refine Stable.add (Stable.smul (Stable.even (Stable.loop (J:=fun p v=>reorder _ (A p v t n (r+2))) ((ih t (by omega) n hh (r+2)).rename (spanLift _)) ht)) _) ?_; apply Stable.sum'; intro i hi; apply Stable.sum'; intro j hj; unfold listPay; apply Stable.sum'; intro v hv; have hi:= mem_antidiagonal.mp hi; have hj:=mem_antidiagonal.mp hj; exact Stable.light (F:=fun p v=>A p v j.1 i.1) ht (ih _ (by omega) _ (by omega) _) (ih _ (by omega) _ (by omega) _)
end Stable
end Mileage
end
end YM.Contacts.Harrier
