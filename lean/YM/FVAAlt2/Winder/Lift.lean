import YM.FVAAlt2.Winder.Pine
/-! # Extend by zero to the COVER, using the same lift convention behind Stalk.collect. Diagram operations compute exactly with padded lobe before Qual.Period. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind.Lift
open Function Layer Packet Tuple Filter Set Diagram
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y Z W J J' : Type} {C D : ℝ≥0∞} {r s:ℕ} (e:X ↪ Y) (f:J ↪ J')
-- use two-sided observation
lemma warrant (v:X→ℝ)(z:X): Stalk.collect (⇑e) v (e z)= v z:= by
 unfold Stalk.collect; rw [tsum_eq_single ⟨z,rfl⟩]; intro j hj; exact (hj (Subtype.ext (e.injective j.property))).elim
lemma warrant0 (v:X→ℝ) (z:Y)(h:z ∉ Set.range e): Stalk.collect (⇑e) v z=0:= by unfold Stalk.collect; haveI : IsEmpty (Stalk (⇑e) z):=⟨fun j=>h ⟨ j.val,j.property⟩⟩; exact tsum_empty
lemma here_p (z:Tuple Y r): z ∈ Set.range (acrossT e) ↔ ∀ i,z i∈ Set.range e:= by
 constructor; exact fun ⟨ y,h ⟩ i=> ⟨y i,congr_fun h i⟩; intro h; choose F he using h; exact ⟨F,funext he⟩
def shore (K:Layer X J) : Layer Y J' := fun i j=> Stalk.collect (⇑e) (fun x=> Stalk.collect (⇑f) ( K x ) j ) i
lemma season (K:Layer X J) (x:X) (j:J') : shore e f K (e x) j=Stalk.collect (⇑f) (K x) j:= warrant ..
lemma bears (K:Layer X J)(x:X)(j:J): shore e f K (e x) (f j)= K x j:= by rw [season,warrant]
lemma season0 (K:Layer X J)(x:Y)(hx:x∉Set.range e): shore e f K x=0:= funext fun _=> warrant0 _ _ _ hx
lemma seasonT (K: Layer X J): shore f e (swap K) = swap (shore e f K):= by
 ext1 i; ext1 j; by_cases he : i∈ Set.range f <;> by_cases hh:j∈Set.range e
 · obtain ⟨i,rfl⟩:=he; obtain ⟨j,rfl⟩:=hh; unfold swap; simp_rw [ bears ]
 · obtain ⟨i,rfl⟩:=he; unfold swap; rw [season,season0 _ _ _ _ hh,warrant0 _ _ _ hh]; rfl
 · obtain ⟨j,rfl⟩:=hh; unfold swap; rw [season,season0 _ _ _ _ he,warrant0 _ _ _ he]; rfl
 unfold swap; rw [season0 _ _ _ _ he,season0 _ _ _ _ hh];rfl
lemma season' (K:Layer X J) (i:Y) (j:J): shore e f K i (f j)= Stalk.collect (⇑e) (swap K j) i:= (congr_fun (congr_fun (seasonT e f K) (f j)) i).symm.trans (season ..)
lemma absent (K:Layer X J)(x:Y) (j:J')(hj:j∉Set.range f): shore e f K x j=0:= by rw [show shore _ _ K x j=shore f e (swap K) j x from (congr_fun (congr_fun (seasonT e f K) j) x).symm, season0 _ _ _ _ hj]; rfl
-- ports.J aggregation includes rank=0
lemma dark : offer e (0:Packet X r)= 0:=by ext1 x; exact tsum_zero
lemma pushPlus (v u: Packet X r): offer e (v+u)=offer e v+ offer e u:= by
 ext1 x; by_cases h:x∈ Set.range (acrossT e)
 · obtain ⟨x,rfl⟩:=h; rw [Pi.add_apply,offer_eq,offer_eq,offer_eq];rfl
 rw [Pi.add_apply,offer_zero e h,offer_zero e h,offer_zero e h]; ring
lemma pushScale (v:Packet X r)(t:ℝ): offer e (t • v)=t • offer e v:=by ext1 x; unfold offer Stalk.collect; simp_rw [Pi.smul_apply,smul_eq_mul,tsum_mul_left]
lemma pushSum (I:Finset Z)(v:Z→Packet X r): offer e (∑ i∈I,v i) =∑ i∈I,offer e (v i):=by
 induction I using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,Finset.sum_empty,dark]
 | insert i I he ih=> rw [Finset.sum_insert he,Finset.sum_insert he,pushPlus,ih]
lemma pushRot (v:Packet X r)(u: Equiv.Perm (Fin r)) : offer e (v ∘ Tuple.perm X u)=offer e v ∘ Tuple.perm Y u:=by
 ext1 x; by_cases h:x∈Set.range (acrossT e)
 · obtain ⟨x,rfl⟩:=h; rw [offer_eq]; exact (offer_eq e v (Tuple.perm _ _ x)).symm
 rw [offer_zero e h,Function.comp_apply,offer_zero]; rintro hv; apply h; rw [here_p]; intro i; have hx:= (here_p e _).mp hv (u.symm i); change x (u (u.symm i))∈_ at hx; rwa [u.apply_symm_apply] at hx
lemma pushSyn (v:Packet X r): offer e ( Packet.symmetry v )=Packet.symmetry (offer e v):= by unfold symmetry; rw [pushScale,pushSum]; simp_rw [pushRot]
lemma pushLoop (v:Packet X (r+2))(K:Layer X X): offer e (loop v K)=loop (offer e v) (shore e e K):= by
 ext1 y; let P:= shore e e K; let f:=offer e v; unfold Packet.loop
 have H : (∑' u:Y×Y,curve f P y u)=∑' u:X× X, curve f P y (e u.1,e u.2):=by
    refine Eq.symm ((e.injective.prodMap e.injective).tsum_eq ?_) -- correct binder?
    intro z hz; by_cases hj:z.1∈Set.range e <;> by_cases hk:z.2∈Set.range e
    · obtain ⟨a,ha⟩:=hj; obtain ⟨b,hb⟩:=hk; exact ⟨(a,b),Prod.ext ha hb ⟩
    all_goals apply False.elim; apply hz; change P _ _ * _=0; first| (rw [ show P z.1 z.2=0 from congr_fun (season0 _ _ _ _ hj) z.2, zero_mul ])| rw [show P _ _=0 from absent e e K z.1 z.2 hk, zero_mul]
 rw [H]
 by_cases h:y∈Set.range (acrossT e)
 · obtain ⟨y,rfl⟩:=h; rw [offer_eq]; refine tsum_congr fun z=>?_ ; rw [curve,curve]; change _= shore e e K (e z.1) (e z.2)* f (linked ((e:X→ Y)∘ y) (e z.1,e z.2)); rw [bears, ← map_link (⇑e)]; exact congr_arg (_ * ·) (offer_eq e v (linked y z)).symm
 rw [offer_zero _ h,tsum_congr (g:=fun _=>0) (fun x=>?_), tsum_zero]; unfold curve; rw [show f (linked y _)=0 from offer_zero e ?_,mul_zero ]; intro hx; apply h; rw [here_p]; intro i; have he:=(here_p e _).mp hx i.succ.succ; rwa [link_here] at he
lemma pushRay (v:Packet X r)(K:Layer X X)(i:Fin r): offer e (ray i v K)=ray i (offer e v) (shore e e K):=by
 ext1 y; unfold ray; rw [← e.injective.tsum_eq]; swap
 · exact fun z hz=> Classical.not_not.mp fun h=> hz (by change swivel _ _ _ _ _=0; rw [swivel,absent _ _ _ _ z h,zero_mul])
 by_cases h:y∈Set.range (acrossT e)
 · obtain ⟨y,rfl⟩:=h; rw [offer_eq]; refine tsum_congr (fun z=>?_); unfold swivel; rw [ show acrossT e y i=e (y i) from rfl, show shore e e K _ _= _ from bears e e K (y i) z, show update (acrossT e y) i (e z)=acrossT e (update y i z) from (Function.comp_update ..).symm,offer_eq] -- change maybe metavariable failure
 rw [offer_zero e h,tsum_congr (g:=fun _=>0) (fun z=>?_ ),tsum_zero]; unfold swivel; by_cases hx:y i∈ Set.range e
 · rw [offer_zero,mul_zero]; intro hy; apply h; rw [here_p]; intro j; by_cases he:j=i; rw [he]; exact hx; have ht:=(here_p e _).mp hy j; rwa [update_of_ne he] at ht
 rw [season0 _ _ _ _ hx]; simp
lemma pushSplicing (v:Packet X (r+1))(u:Packet X (s+1)): offer e (splice v u) = splice ( offer e v ) ( offer e u ):=by
 ext1 z; unfold splice; rw [ ← e.injective.tsum_eq]; swap
 · intro j hj; by_contra hp; apply hj; change lace _ _ _ _ _=0; rw [lace,offer_zero e,zero_mul]; intro hy; exact hp ((here_p e _).mp hy 0)
 by_cases hh:z∈ Set.range (acrossT e)
 · obtain ⟨z,rfl⟩:=hh; rw [offer_eq]; apply tsum_congr; intro x; unfold lace; change _= offer e v (Fin.cons (α:=fun _=>Y) (e x) ((e: X→Y)∘cutLeft z))* offer e u (Fin.cons (α:=fun _=>Y) (e x) ((e:X→Y)∘cutRight z)); rw [← Tuple.comp_cons,← Tuple.comp_cons]; exact congr_arg₂ (· * ·) (offer_eq e v ( Fin.cons x (cutLeft z) )).symm (offer_eq e u (Fin.cons x (cutRight z))).symm
 rw [offer_zero e hh,tsum_congr (g:=fun _=>0) (fun z=>?_), tsum_zero]; unfold lace; apply mul_eq_zero.mpr; by_contra! h; apply hh; rw [here_p]; intro i; induction i using Fin.addCases <;> rename_i j
 · exact (here_p e _).mp (Classical.not_not.mp fun h'=> h.1 (offer_zero _ h')) j.succ
 exact (here_p e _).mp ( Classical.not_not.mp fun h'=> h.2 (offer_zero _ h') ) j.succ
lemma pushKnot (v:Packet X (r+1))(u:Packet X (s+1))(K:Layer X X) : offer e (knot K v u)=knot (shore e e K) (offer e v) (offer e u) := by unfold knot; rw [pushSplicing,pushRay]
lemma pushDraw (v:Packet X r)(K:Layer X X)(s:List (Fin r)): offer e (drawing v K s)=drawing (offer e v) (shore e e K) s:=by induction s with | nil=> rfl | cons x s ih=> rw [drawing,drawing,pushRay,ih]
lemma pushDraft (v:Packet X r)(K:Layer X X): offer e (draft K v)= draft (shore e e K) (offer e v):= by unfold draft; rw [pushSyn,pushDraw]
end YM.RegulatorIR.Budget.FVAAlt2.Wind.Lift
