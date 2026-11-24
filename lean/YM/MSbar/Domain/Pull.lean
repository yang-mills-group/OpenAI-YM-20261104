import YM.MSbar.Domain.Site
/-! Calculus of plot costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Function Set Filter Symbol Dim Transfer MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {X Y W : ℕ→Type} {S:Site X} {K:Site Y}{C:Site W} {U:Set ℂ} {m n j : ℕ}
structure Draw (S:Site X)(K:Site Y)(f:∀m,X m→Y m):Prop where
   compose {n m:ℕ} (L:Move n m)(x:X n): K.move L (f n x)= f m (S.move L x)
   paint (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m:ℕ} (x:E→ X m) : S.plot x → K.plot (f m ∘ x)

namespace Draw
variable {F:∀m,X m→Y m}
lemma follow (h:Draw S K F){g:∀ m,Y m→W m}(hh:Draw K C g): Draw S C (fun m=> g m ∘ F m):= by
   refine ⟨fun L x=>?_,fun _ _ _ _ _ x hx=>?_⟩ -- binder count?
   · unfold Function.comp; rw [hh.compose, h.compose]
   exact hh.paint _ _ (h.paint _ _ hx)
lemma prod (h:Draw S K F){g:∀ m,X m→W m}(hh:Draw S C g):Draw S (K.prod C) (fun m x=>(F m x,g m x)):= ⟨fun L x=> Prod.ext (h.compose L x) (hh.compose L x), by introv H; exact ⟨h.paint _ _ H,hh.paint _ _ H⟩⟩
lemma fst : Draw (S.prod K) S (fun _=>Prod.fst) := ⟨fun _ _=> rfl, by introv H; exact H.1⟩
lemma snd : Draw (S.prod K) K (fun _=>Prod.snd) := ⟨fun _ _=> rfl, by introv H; exact H.2⟩
lemma stay (S:Site X) : Draw S S (fun _=> id):= ⟨fun _ _=> rfl, by introv H; exact H⟩
end Draw
namespace Eligible
variable {F G : Record X} {V:Set ℂ}
lemma upon (hf:Eligible U j S F)(hu : V ⊆ U): Eligible V j S F:=⟨fun z hz=>hf.natural z (hu hz),fun E _ _ _ _ x hx=> (hf.ev E x hx).upon hu⟩
lemma arg (hf:Eligible U j S F){p:∀ m,Y m→ X m}(hp:Draw K S p): Eligible U j K (fun z m x=>F z m (p m x)):=by
    refine ⟨fun z hz ⦃_ _⦄ L y=>?_,?_⟩
    · rw [← hp.compose]; exact hf.natural z hz L _
    introv H; exact hf.ev _ _ (hp.paint _ _ H)
lemma cte (c:ℂ) : Eligible U 0 S (fun _ _ _=>c):=⟨fun _ _ ⦃_ _⦄ _ _=>rfl,by intros; apply Bet.cte⟩
lemma zero : Eligible U m S 0:=⟨fun _ _ ⦃_ _⦄ _ _=>rfl,by intros; exact Bet.zero⟩
lemma add (hf:Eligible U j S F)(hg:Eligible U j S G): Eligible U j S (F+G):=
    ⟨fun z hz ⦃_ _⦄ L x=> congr_arg₂ (·+·) (hf.natural z hz L x) (hg.natural z hz L x),by introv H; exact (hf.ev _ _ H).add (hg.ev _ _ H)⟩
lemma neg (hf:Eligible U j S F) : Eligible U j S (-F):=⟨fun z hz ⦃_ _⦄ L x=> congr_arg Neg.neg (hf.natural z hz L x),by introv H; exact (hf.ev _ _ H).neg⟩
lemma sub (hf:Eligible U j S F) (hg:Eligible U j S G) : Eligible U j S (F-G):=by rw [sub_eq_add_neg]; exact hf.add hg.neg
lemma mul (hf:Eligible U m S F)(hg:Eligible U n S G): Eligible U (m+n) S (F*G):=
   ⟨ fun z hz ⦃_ _⦄ L x=>congr_arg₂ (·*·) (hf.natural z hz L x) (hg.natural z hz L x),by introv H; exact (hf.ev _ _ H).mul (hg.ev _ _ H)⟩
lemma scale (hf:Eligible U j S F)(c:ℂ): Eligible U j S (c • F) := by simpa only [zero_add] using! (cte c).mul hf
lemma sum {ι:Type} {F:ι→Record X}(I: Finset ι)(H:∀ i∈I, Eligible U j S (F i)): Eligible U j S (∑ i∈ I,F i):= by induction I using Finset.induction_on with | empty=>simp only [Finset.sum_empty]; exact zero | insert i s h ih=>rw [Finset.sum_insert h]; exact (H _ (Finset.mem_insert_self ..)).add (ih fun j hj=> H _ (Finset.mem_insert_of_mem hj))
lemma sum' {ι:Type} {F:ι→ Record X}(s:Finset ι)(H:∀ i∈s,Eligible U j S (F i)): Eligible U j S (fun z m x=>∑ i∈s,F i z m x):=by simpa only [← Finset.sum_apply] using sum s H
lemma agrees (hf:Eligible U j S F)(hu : IsOpen U)(hV : ∀ z∈U,F z=G z): Eligible U j S G := by
   refine ⟨fun z hz=> hV z hz ▸ hf.natural z hz,?_⟩; introv H; exact (hf.ev _ _ H).congr hu fun z hz x=> congr_fun (congr_fun (hV z hz) _) _

section
variable {G: Record (fun m=> X m × Hat m)}
variable (hf:Eligible U j (S.prod Site.moving) G) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
include hf
lemma trace (T:Prop) (hp:∀ z ∈ U,∀ i (x:X i), Two T fun y=>G z _ (x,y)) : Eligible U j S (fun z=> metric S.toMotion T z (G z)):= by
   refine ⟨fun z hz=> Trace.coherent (hf.natural z hz) (hp z hz) z, ?_⟩; intro E i1 i2 i3 m p h
   have hh (y : Hat m): Bet U j (fun w:ℂ×E=> G w.1 m (p w.2,y)):= hf.ev _ (fun v=>(p v,y)) ⟨h, HasTemperateGrowth.const _⟩
   have hi: Bet U j (fun w:ℂ×E=> G w.1 (m+1) (above S.toMotion (p w.2), Trace.step m)):= hf.ev _ (fun v=>(above S.toMotion (p v), Trace.step m)) ⟨S.size_up (up m) h, HasTemperateGrowth.const _⟩
   have he := Bet.sum_e (index T m) (fun y _=> hh y); unfold metric; split_ifs; swap; simpa only [add_zero] using he
   exact (he.add (zero_add j ▸ (((Bet.identity (U:=U) (E:=E)).sub (Bet.cte (m:ℂ))).const_scale 2|>.mul hi)))

lemma plate (k:ℝ) (hu : IsOpen U)(hp:∀ z∈U,∀ i (x:X i), Packed i k (fun y=> G z (i+1) (above S.toMotion x,y))) : Eligible U (1+j) S (fun z=> request S.toMotion (G z) z):=by
   refine ⟨fun z hz=> Tower.compact_lift (hf.natural z hz) z (fun i x=>⟨k,hp z hz _ x⟩), ?_⟩; intro E i1 i2 i3 m p h
   let Y(v:ℂ × (E × Hat (m+1))) := G v.1 (m+1) (S.move (up m) (p v.2.1),v.2.2)
   have hV : S.plot (p ∘ (Prod.fst : E × Hat (m+1) → E)):= S.views h tame_projL
   change Bet U (1+j) (fun q:ℂ×E=>Dim.plate q.1 (fun y=>Y (q.1,q.2,y)))
   have he:Bet U j Y:=hf.ev _ (fun v:(E × Hat (m+1))=> (S.move (up m) (p v.1),v.2)) ⟨S.size_up (up m) hV, tame_projR⟩ -- `p` name argument?
   refine ⟨plate_ah (m:=m) (G:=Y) (K:=k) (t:=id) he.cost differentiableOn_id hu (fun z hz x=>hp z hz _ (p x)),fun h=>?_⟩
   exact plate_market (m:=m) (he.gains h) (K:=k) (fun z x=> hp z (h ▸ mem_univ _) m (p x))
end
end Eligible
end YM.MSbar.Domain
