import YM.Contacts.Prairie.Bank
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
variable (e:Parcel G) (p q u:Word) (s:Step)  {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
variable {A B ι κ: Type} [Fintype ι] [Fintype κ] {S:Boom}{T: Word→A→A→ℝ} {l: Pulse.Range A} {k:Pulse.Range B}{n r h k':ℕ}
abbrev Threads (S:Boom)(τ:A→B→ℝ)(R: Word→A→B→ℝ) := Holds S (fun f x=> Weirs τ f x x) R
abbrev Climb (S:Boom)(l:Pulse.Range A)(R:Word→A→A→ℝ):= Holds S (fun f x=> Pulse.Track l f x) R
variable {Z : Word→A→B→ℝ}{τ:A→B→ℝ}{R:Word→Field (Fin n) A}
namespace Threads
lemma alone {z:A→B→ℝ}{x:ℝ}(h:Weirs τ z b x): Threads S τ (fun _=>z):= by refine Holds.init (P:=fun f c=> Weirs τ f c c) ?_ (weir_up h (le_add_of_nonneg_right h.right) (le_add_of_nonneg_left h.left)) (add_nonneg h.left h.right); simp only [sub_self]; exact ⟨le_rfl,le_rfl,by intro; simpa using budget_zero,by intro; simpa using budget_zero⟩
lemma basic (h:Threads S τ Z)(ht:Ripple l k τ) (he:Will S l R): Will S k (fun p=> hoist (Z p) (R p)):= by obtain ⟨b,hb,H⟩:=h.1; obtain ⟨c,hc,hP⟩:= he; exact ⟨_,mul_nonneg (mul_nonneg hb hc) (pow_nonneg hb _), fun i hi=> hoist_pay ht (H _ hi) (hP _ hi)⟩
lemma rider (h:Threads S τ Z)(ht:Ripple l k τ)(he:Will S l R) : ∃ z≥0,∀ p q u,OK S p → OK S q → OK S u → Rooted k (hoist (Z (u++p)) (R (u++q))-hoist (Z (u++q)) (R (u++q))) (z*mileage u):= by obtain ⟨b,hb,hB⟩:=he; obtain ⟨⟨c,hc,H⟩,r,hr,hR⟩:=h; refine ⟨_,mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (mul_nonneg hb hr) (pow_nonneg hc (n-1))), fun p q u hp hq hu=>?_⟩; convert hoist_drift n ht (H _ (hu.append hp)) (H _ (hu.append hq)) (hR p q u hp hq hu) (hB _ (hu.append hq)) using 1; ring
lemma lift (h:Threads S τ Z)(ht:Ripple l k τ)(he:Fleet S l R) : Fleet S k (fun p=>hoist (Z p) (R p)):= by
   by_cases hn:n=0; · subst n; exact Fleet.empty
   letI:NeZero n:=⟨hn⟩; refine ⟨basic h ht he.1,?_⟩; obtain ⟨b,hb,hB⟩:=rider h ht he.1; obtain ⟨a,ha,H⟩:=h.1; obtain ⟨⟨_,_,hQ⟩,x,hx,hX⟩:=he; refine ⟨_,add_nonneg (mul_nonneg (mul_nonneg ha hx) (pow_nonneg ha (n-1))) hb,fun p q u hp hq hu=>?_⟩; have hr:= (hoist_pay ht (H _ (hu.append hp)) (hX p q u hp hq hu)).add (hB p q u hp hq hu); rw [hoist_sub ht (H _ (hu.append hp)) (hQ _ (hu.append hp)) (hQ _ (hu.append hq))] at hr; convert hr using 1; abel; ring
end Threads
namespace Climb
variable {x:Word→Field (Option ι) A} {y:Word→Field (Option κ) A}
lemma borrow (h:Climb S l T): Threads S l.step T:= Holds.weaken h (fun _ _ ht=> Pulse.Track.flow ht)
lemma closes {x: Word→Field (Option (Option ι)) A}(h:Climb S l T)(ht:Fleet S l x): Fleet S l (fun p=> loop (T p) (x p)):= by
   rcases isEmpty_or_nonempty ι with _|_; · exact Fleet.empty
   obtain ⟨⟨a,ha,H⟩,b,hb,hB⟩:=h; obtain ⟨⟨c,hc,hC⟩,d,hd,hD⟩:=ht; refine ⟨⟨_,mul_nonneg ha hc,fun i hi=> loop_root (H _ hi) (hC _ hi)⟩,_, add_nonneg (mul_nonneg ha hd) (mul_nonneg hb hc),fun p q u hp hq hu=>?_⟩
   have he:= (loop_root (H _ (hu.append hp)) (hD p q u hp hq hu)).add (loop_root (hB p q u hp hq hu) (hC _ (hu.append hq))); rw [loop_less (H _ (hu.append hp)) (hC _ (hu.append hp)) (hC _ (hu.append hq)), loop_line (Pulse.Track.cap (H _ (hu.append hp))) (Pulse.Track.cap (H _ (hu.append hq))) (hC _ (hu.append hq)) ha ha] at he; convert he using 1; abel; ring
lemma stitchF (h:Climb S l T)(hp:Fleet S l x)(hr:Fleet S l y): Fleet S l (fun i=> stitch (T i) (x i) (y i)):= by
   rcases isEmpty_or_nonempty (ι⊕κ) with _|_; · exact Fleet.empty
   obtain ⟨⟨b,hb,B⟩,c,hc,C⟩:=h; obtain ⟨⟨x',hx,X'⟩,v,hv,V⟩:=hp; obtain ⟨⟨y',hy,H⟩,w,hw,W⟩:=hr; refine ⟨⟨_,mul_nonneg hx (mul_nonneg hb hy),fun i hi=> stitch_root (B _ hi) (X' _ hi) (H _ hi)⟩, _,add_nonneg (add_nonneg (mul_nonneg hv (mul_nonneg hb hy)) (mul_nonneg hx (mul_nonneg hc hy))) (mul_nonneg hx (mul_nonneg hb hw)), fun p q u hi hj hk=>?_⟩; have hn:=hk.append hi; have hm:=hk.append hj; convert stitch_diff (B _ hn) (B _ hm) (C p q u hi hj hk) (X' _ hn) (X' _ hm) (H _ hn) (H _ hm) (V p q u hi hj hk) (W p q u hi hj hk) using 1; ring
lemma dose {F:Word→Field (Fin (n+2)) A} (h:Climb S l T)(ht:Fleet S l F): Fleet S l (fun i=>Pulse.degree (T i) (F i)):= Fleet.smul (Fleet.even (Climb.closes (T:=T) (l:=l) (S:=S) h (Fleet.rename (spanLift _) ht))) _
lemma link {X Y : Word→Pulse.Rack A}(h:Climb S l T)(ht:Fleet S l (fun i=> X i (k'+1)))(hv:Fleet S l (fun i=> Y i (r+1))) : Fleet S l (fun i=> light (T i) j k' r (X i) (Y i)):= by
   unfold light; by_cases he:k'+r=j; · subst j; simp only; exact Fleet.smul (Fleet.even (Fleet.rename finSumFinEquiv (Climb.stitchF (x:=fun i=>squeeze (X i (k'+1))) h (Fleet.rename (finSuccEquiv _) ht) (Fleet.rename (finSuccEquiv _) hv)))) _
   simp_rw [dif_neg he]; exact Fleet.fzero
end Climb
end Parcel
end
end YM.Contacts.Prairie
