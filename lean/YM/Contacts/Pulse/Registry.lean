import YM.Contacts.Pulse.Oppose
/-! Two-systems propagation of budgets on the temporal recursion. No holomorphic width
cost paid per temporal/arity convolution. A second width on the cover pays for one winding
when comparing the internal loop of one received step.

All costs here are polynomials of finite inputs and obey the consecutive displacement
accounting needed in repeated steps. We are not raising a finite torus initial price
through arbitrary UV scales in this handoff.
-/
noncomputable section
namespace YM.Pulse
open Function Filter Finset RG
open scoped Classical Topology NNReal BigOperators
variable {ι κ α β X Y : Type*}[Fintype ι][Fintype κ]
variable (p : X→Y)(m:Range X)(l:Range Y) (T:Type*) [Group T] [MulAction T X]
structure MirrorWay (p:X→Y) (T:Type*) [Group T][MulAction T X] (m:Range X)(l:Range Y) where
  gears : Gaugeway p T
  t : Range X
  closed (a b x y : X): t.step x y * l.step (p a) (p b) ≤ max (m.step x y) (m.step a b)
variable {p m l T}
variable {b c d f e u v x y : ℝ}
namespace MirrorWay
lemma lower (w:MirrorWay p T m l) (q:ι→X): l.bill (p∘q) ≤ m.bill q:= by
  apply l.wide _ (m.one_bill _) _; intro i j; calc
    l.step _ _ ≤ w.t.step (q i) (q j) * l.step (p (q i)) (p (q j)) := le_mul_of_one_le_left (by positivity) w.t.one_fee
    _ ≤ _:= (w.closed (q i) (q j) (q i) (q j)).trans (max_le (m.width ..) (m.width ..))
lemma shaded (w:MirrorWay p T m l) (q:ι→X): w.t.bill q * (l.pull p).bill q ≤ m.bill q:= by
   let k:=l.pull p
   have hx:=k.one_bill q; have hp: k.bill q≤ m.bill q:= w.lower q
   rcases isEmpty_or_nonempty ι with h|h
   · have hi: w.t.bill q=1:= le_antisymm (w.t.wide _ le_rfl fun i _=> isEmptyElim i) (w.t.one_bill q); rw [hi,one_mul]; exact hp
   have top (l:Range X): ∃ a b:ι,l.bill q=l.step (q a) (q b) := by
      haveI:=h; obtain ⟨a,_,ha⟩:= Finset.exists_mem_eq_sup _ (f:=fun i:ι=>univ.sup fun j:ι=>l.fee (q i) (q j)) (by exact Finset.univ_nonempty)
      obtain ⟨b,_,hb⟩:= Finset.exists_mem_eq_sup _ (f:=fun j:ι=>l.fee (q a) (q j)) (by exact Finset.univ_nonempty); unfold Range.bill Range.height
      exact ⟨a,b,by rw [ha,hb,max_eq_right (l.one ..)]⟩
   obtain ⟨x,y,ha⟩:=top w.t; obtain ⟨a,b,hb⟩:=top (l.pull p); rw [ha,hb]; exact (w.closed ..).trans (max_le (m.width q x y) (m.width q a b))
end MirrorWay
structure Two (W:MirrorWay p T m l)(F:Field ι X)(G:Field ι Y)(b c:ℝ): Prop where
  risen: Carried T F
  ground: Rooted m F b
  seats : Rooted l G b
  owes : ∃ H:Field ι Y, Shadow p F H ∧ Rooted l (G-H) c

structure Waves (W: MirrorWay p T m l)(G:X→X→ℝ)(H:Y→Y→ℝ)(b d e:ℝ):Prop where
  left: Track m G b
  right: Track l H b
  risen: ∀ x y (t:T), G (t • x) (t • y)=G x y
  rate : 0 ≤ d
  owes : ∃ I, Trails p p G I ∧ Track l I b ∧ Track l (H-I) e ∧ ∀ x y, ‖I (p x) (p y)-G x y‖ ≤ d* W.t.step x y
namespace Two
variable {W : MirrorWay p T m l} {F M:Field ι X}{G N:Field ι Y}
lemma shift (h: Two W F G b c) (ha:b≤ d)(hc:c≤ f): Two W F G d f:= by obtain ⟨i,hi,hf⟩:=h.owes; exact ⟨h.risen,h.ground.weaken (fun _=>le_rfl) ha,h.seats.weaken (fun _=>le_rfl) ha,i,hi,hf.weaken (fun _=>le_rfl) hc⟩
lemma coins (h:Two W F G b c): 0≤ c:= let ⟨_,_,hc⟩:=h.owes; hc.cash -- elimination into Prop
lemma empty (W : MirrorWay p T m l): Two (ι:=ι) W 0 0 0 0:= ⟨fun _ _=>rfl,Rooted.tranquility m,Rooted.tranquility l,0,Shadow.empty p,(by rw [sub_zero]; exact Rooted.tranquility l)⟩
lemma scale (h: Two W F G b c)(a:ℝ): Two W (a • F) (a • G) (‖a‖*b) (‖a‖*c):= by
   obtain ⟨i,hi,hf⟩:=h.owes; refine ⟨fun _ _=>congr_arg (a*·) (h.risen ..),h.ground.smul a,h.seats.smul a,a • i, hi.scale a,?_⟩
   rw [←smul_sub]; exact hf.smul a
lemma add (h: Two W F G b c)(g: Two W M N d f) : Two W (F+M) (G+N) (b+d) (c+f):= by
   obtain ⟨i,hi,hf⟩:=h.owes; obtain ⟨x,hx,hX⟩:=g.owes; refine ⟨fun _ _=> congr_arg₂ (·+·) (h.risen ..) (g.risen ..),h.ground.add g.ground,h.seats.add g.seats,_, hi.add hx h.ground g.ground,?_⟩; convert! hf.add hX using 1; abel
lemma finite {F:α→Field ι X}{G:α→Field ι Y}(s: Finset α){b c: α→ℝ}(h:∀ i ∈ s, Two W (F i) (G i) (b i) (c i)): Two W (∑ i∈s,F i) (∑ i∈s,G i) (∑ i∈s,b i) (∑ i∈s,c i):= by
   induction s using Finset.induction_on with
   | empty=> simpa using (empty (ι:=ι) W)
   | @insert i s hi ih=> simp only [hi,not_false_eq_true,sum_insert]; exact (h i (mem_insert_self ..)).add (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma renew (h: Two W F G b c)(e:ι≃κ): Two W (reorder e F) (reorder e G) b c:= by
   obtain ⟨i,hi,hf⟩:=h.owes; exact ⟨fun t x=>h.risen t (x∘ e),h.ground.renew e,h.seats.renew e,reorder e i,hi.replace (e:=e.symm),hf.renew e⟩
lemma print (h: Two W F G b c): Two W (printRun F) (printRun G) b c := by
   have ht:=finite univ (fun (i:Equiv.Perm ι) _=> h.renew i) |>.scale (Fintype.card (Equiv.Perm ι):ℝ)⁻¹
   unfold printRun; simpa only [norm_inv, Real.norm_natCast,Finset.sum_const,card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ (show (Fintype.card (Equiv.Perm ι) : ℝ) ≠0 by exact_mod_cast Fintype.card_ne_zero),one_mul] using ht
-- estimate across systems through one vertex of temporal recursion
variable {I:X→X→ℝ}{J:Y→Y→ℝ}
lemma stitch_cost {F:Field (Option ι) X}{M:Field (Option κ) X}{G:Field (Option ι) Y}{N:Field (Option κ) Y}(hD:Waves W I J d u v)(h:Two W F G b x)(hx:Two W M N c y): Two W (stitch I F M) (stitch J G N) (b*(d*c)) (x*(d*c)+ b*(v*c)+ b*(d*y)):= by
   obtain ⟨O,hO,hw⟩:= h.owes; obtain ⟨P,hP,hX⟩:= hx.owes; obtain ⟨K,hK,H,hT,H'⟩:= hD.owes
   refine ⟨fun t=> mir_stitch (e:=MulAction.toPerm t) (fun i j=> hD.risen i j t) (h.risen t) (hx.risen t),stitch_root hD.left h.ground hx.ground,stitch_root hD.right h.seats hx.seats,stitch K O P,stitch_snapshot hO hP hK h.ground hx.ground hD.left,?_⟩
   rcases isEmpty_or_nonempty (ι⊕κ) with Z|Z
   · have A:=h.coins; have B:=hx.coins; have C:=h.seats.cash; have Y:= hx.seats.cash; have S:=H.cash; have T:= hT.cash; exact Rooted.emptySpace l _ (by positivity)
   exact stitch_diff hD.right H hT h.seats (hO.cost h.ground W.lower W.gears.onto) hx.seats (hP.cost hx.ground W.lower W.gears.onto) hw hX
lemma loop_est {F:Field (Option (Option ι)) X}{G:Field (Option (Option ι)) Y}(hD:Waves W I J d u v)(h:Two W F G b x) : Two W (loop I F) (loop J G) (d*b) (v*b+d*x+u*b):= by
   have hR:Carried T (loop I F):= fun t=>mir_loop (e:=MulAction.toPerm t) (h.risen t) (fun i j=> hD.risen i j t)
   obtain ⟨O,hO,hw⟩:= h.owes; obtain ⟨K,hK,H,hT,H'⟩:= hD.owes
   refine ⟨hR,loop_root hD.left h.ground,loop_root hD.right h.seats,?_⟩
   rcases isEmpty_or_nonempty ι with hl|hl
   · exact ⟨0,fun i => isEmptyElim i,Rooted.emptySpace l _ (by have h₁:=hD.left.cash; have h₂:=h.ground.cash; have h₃:=hw.cash; have h₄:=hT.cash; have h₅:= hD.rate; positivity)⟩
   have hA:= hO.cost h.ground W.lower W.gears.onto
   let V:= W.gears.lower (loop I F)
   have hV:=W.gears.lower_shadow hR
   let K' i j:= K (p i) (p j); have hk (i j:X): ‖K' i j‖ ≤ d:= H.cap ..
   have hu:=weather (G:=K'-I) H' hD.rate h.ground W.shaded
   rw [loop_line hk hD.left.cap h.ground H.cash H.cash] at hu; have hb:= snapshot_reflected hO h.ground H.cap H.cash
   have ht:Shadow p (loop K' F-loop I F) (loop K O-V):= by
     have hp:Shadow p (-loop I F) (-V):= by simpa only [neg_one_smul] using hV.scale (-1)
     rw [sub_eq_add_neg,sub_eq_add_neg (loop K O)]; exact hb.add hp (loop_attains hk h.ground H.cash) ((loop_root hD.left h.ground).neg)
   have he:= ht.cost hu (fun r=> (show l.bill (p∘r) ≤ (l.pull p).bill r from le_rfl)) W.gears.onto; -- l.pull bill
   refine ⟨V,hV,?_⟩
   have hv:= ((loop_root hT h.seats).add (loop_root H hw)).add he
   rw [loop_line hD.right.cap H.cap h.seats H.cash H.cash, loop_less H h.seats hA] at hv; convert! hv using 1; abel
end Two
end YM.Pulse
