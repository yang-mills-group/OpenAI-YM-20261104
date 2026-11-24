import YM.FVAAlt2.Winder.Lift
/-! # Qualifying transits from native torus padding through genuinely iterated histories. Entry via
 matrix or unmarked ''holding'' stencil projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind
open Set Filter Function Packet Layer Tuple Lift
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y W Z J : Type} {R S : W→ Type} {C D:ℝ≥0∞} {l:Filter W} {K:Layer X Y}{U: (i:W)→Layer (R i) (S i)} {r :ℕ}
lemma Earn.comes {v:X→ℝ}{F G:W→X→ℝ} (m:Earn l C v F)(H: F =ᶠ[l] G)(h:∀ w,cost (G w) ≤ C): Earn l C v G:= ⟨m.high,m.roof,h,m.up.congr' ( H.mono fun _ hx=> congr_arg (fun u:X→ℝ=> cost (u-v)) hx ) ⟩
-- atom map rows without mix restriction (indicate holds)
lemma sleek (z:X): cost (Tape.atOne z)=1:= by rw [cost,quota_base]; exact Tape.mass_single z
lemma atoms (g:X→Y)(v:X→ℝ) : Tape.mix v (Tape.atOne ∘ g)= Stalk.collect g v:= by
 ext1 i; unfold Tape.mix; change _=∑' x: ↑{z:X| g z=i},v x
 rw [_root_.tsum_subtype (s:={z:X|g z=i}) (f:=v)] -- sect mem
 apply tsum_congr; intro x; by_cases h:g x=i <;> simp [ indicator,h, Tape.atOne,eq_comm ]
lemma Earn.gathers (h: X→X) (p:W→X→X)(he:∀ i:X, ∀ᶠ j in l, p j i=h i) {v:X→ℝ}(hx:cost v≤ C)(hc:C≠⊤) : Earn l C (Stalk.collect h v) fun w=> Stalk.collect (p w) v:= by
 have H(i:X):Earn l 1 (Tape.atOne (h i)) (fun w=> Tape.atOne (p w i)):= (Earn.const (sleek (h i)).le ENNReal.one_ne_top ).comes ((he i).mono (fun j he=> congr_arg _ he.symm)) (fun _=>(sleek _).le)
 let u:X × X ≃ X × X:= Equiv.prodComm _ _
 have ht:= (( Earn.const hx hc ).link (t:=fun i=> Tape.atOne (h i)) (a:=fun w i=> Tape.atOne (p w i)) H ENNReal.one_ne_top |>.pays u u.injective ).sumSecond
 rw [mul_one] at ht; simp_rw [← atoms]; exact ht
lemma Earn.gath (p:W→X→X)(he:∀ i:X, ∀ᶠ j in l,p j i=i){v:X→ℝ}(hx:cost v≤C)(hc:C≠⊤) : Earn l C v fun w=> Stalk.collect (p w) v:=by
 have h:=Earn.gathers (fun x=>x) p he hx hc; rwa [show Stalk.collect (fun x:X=>x) v= v from ( atoms _ v ).symm.trans (Tape.mix_id v)] at h
lemma united (g:X→Y)(e:Y ↪ Z)(v:X→ℝ) : Stalk.collect (⇑e) (Stalk.collect g v) = Stalk.collect ((e:Y→Z)∘g) v:= by
 ext1 z; by_cases he:z∈ Set.range e
 · obtain ⟨z,rfl⟩:= he; rw [Lift.warrant e]; let E : Stalk g z≃ Stalk ((e:Y→Z) ∘ g) (e z):= Equiv.subtypeEquiv (Equiv.refl _) (fun x:X=> ⟨fun h=> congr_arg _ h,fun h=> e.injective h⟩)
   exact (E.tsum_eq (fun i=>v i.val)) -- orientation? E.tsum_eq = ∑domain v ∘ E = ∑ target. 
 rw [Lift.warrant0 e _ z he]; haveI : IsEmpty (Stalk ( (e:Y→ Z)∘ g ) z):=⟨fun j=> he ⟨g j.val,j.property⟩⟩; unfold Stalk.collect;rw [tsum_empty]
structure Arch (X:Type)(l:Filter W)(R:W→Type) where
 spring : ∀ w,R w ↪ X
 pack : ∀ w,X→ R w
 due w x : pack w (spring w x)=x
 tides x : ∀ᶠ w in l, spring w (pack w x)=x
namespace Arch
variable (T:Arch X l R)(P: Arch Y l S)
abbrev pos (w:W) := T.pack w
abbrev cen (w:W):= T.spring w
lemma EarnMoney {v:X→ℝ}(hx:cost v≤C)(hc:C≠⊤): Earn l C v fun i=>Stalk.collect (⇑(T.cen i)) (Stalk.collect ( T.pack i ) v):=by simp_rw [united]; exact Earn.gath (fun w=> _ ) T.tides hx hc
abbrev projection (p:X→Y)(i:Fin r)(x:X): Hold i x→Hold i (p x):= fun u=>⟨p∘ u.val, congr_arg _ u.property ⟩
def gloss : Arch (Tuple X r) l (fun w=>Tuple (R w) r):={
 spring:=fun w=>⟨acrossT (T.spring w),injectT _⟩, pack:=fun w u=> T.pack w ∘ u, due:=fun _ _=> funext fun _=> T.due _ _, tides:=fun x=> (eventually_all.mpr (fun i:Fin r=> T.tides (x i))).mono fun _ h=> funext h }
lemma EarnView {v:Packet X r}(hx:cost v≤C)(hc:C≠⊤): Earn l C v fun i=> offer ( T.spring i ) ( Stalk.collect (fun u:Tuple X r=> T.pack i∘ u) v ):= T.gloss.EarnMoney hx hc
variable {T P}
def wing (T:Arch X l R) (P:Arch Y l S)(K:Layer X Y)(U:(i:W)→ Layer (R i) (S i)):Prop:=∀ w (i:X),(U w) (T.pos w i)=Stalk.collect (P.pos w) (K i)
def Baked (T:Arch X l R)(P:Arch Y l S)(K:Layer X Y)(U:(i:W)→ Layer (R i) (S i)): Prop:= wing T P K U∧ wing P T (swap K) (fun i=> swap (U i))
lemma earns_row (m:wing T P K U)(h:∀ x:X,cost (K x)≤ C)(hv:C ≠⊤)(x:X): Earn l C (K x) (fun i=> (shore (T.cen i) (P.cen i) (U i)) x):=by
 have hp w (z:X) (he:T.cen w (T.pos w z)=z): shore (T.cen w) (P.cen w) (U w) z=Stalk.collect (⇑( P.cen w )) (Stalk.collect ( P.pos w ) (K z)):= by
    rw [← m w z]; nth_rw 1 [← he ]; exact funext ( fun _=> season .. ) -- binder order z implicit?
 refine ( P.EarnMoney (h x) hv ).comes ((T.tides x).mono (fun w he=> (hp w x he).symm)) fun w=>?_
 by_cases hx : x∈ Set.range (T.cen w)
 · rw [ hp w x ]; exact ( P.EarnMoney (h x) hv ).terms w
   obtain ⟨x,rfl⟩:=hx; exact congr_arg _ (T.due w x)
 rw [ season0 _ _ _ x hx ]; exact le_trans (quota_zero _).le zero_le
lemma earns_split (m:Baked T P K U) (h:∀ x,cost (K x)≤ C)(h':∀ y,cost (swap K y)≤ C)(he:C ≠⊤): SplitT l C K (fun i=>shore (T.cen i) (P.cen i) (U i)):=by
 refine ⟨he,fun x=> earns_row m.1 h he x,?_ ⟩; simp_rw [ ←seasonT ]; exact earns_row m.2 h' he
lemma hold_l (w:W)(i:Fin r)(x:X)(z:Hold i x): (T.pack w ∘ z.val) i=T.pack w x:= congr_arg _ z.property
noncomputable def towards (T:Arch X l R)(w:W) (i:Fin r)(x:X)(z: Hold i x): Hold i x := ⟨update (T.spring w ∘ T.pack w ∘ z.val) i x,update_self ..⟩
-- actually easier to generalize customs.Go.Equal recast transport along hh.
noncomputable def touch (w:W)(i:Fin r)(x:X) (hh:T.cen w (T.pos w x)=x) : Hold i (T.pack w x) ↪ Hold i x := {
 toFun:=fun j=>⟨T.cen w ∘ j.val,( congr_arg (T.cen w) j.property ).trans hh⟩, inj':=fun _ _ he=> Subtype.ext (injectT _ (Subtype.mk.inj he)) }
lemma funds (w i)(x:X)(hh:T.cen w (T.pos w x)=x) (u:Packet (R w) r): (offer ( T.cen w ) u)∘(Subtype.val: Hold i x→ Tuple X r)=Stalk.collect (⇑(touch w i x hh)) (u ∘ Subtype.val):=by
 ext1 k; let H : Stalk (touch w i x hh) k ≃ Stalk (acrossT (T.cen w)) k.val := {
  toFun:=fun s=>⟨s.val.val,Subtype.ext_iff.mp s.property⟩, invFun:=fun s=>⟨ ⟨s.val,(T.cen w).injective (( congr_fun s.property _).trans (k.property.trans hh.symm ) ) ⟩,Subtype.ext s.property⟩, left_inv:=fun _=>rfl,right_inv:=fun _=> rfl }
 exact ( H.tsum_eq (fun i=>u i.val) ).symm
lemma paid (i:Fin r)(x:X){v:Packet X r}{V:(i:W)→Packet (R i) r}(w:W) (hh:T.cen w (T.pos w x)=x) (hp: V w ∘ ( Subtype.val: Hold i (T.pack w x) → Tuple (R w) r ) = Stalk.collect ( projection (T.pack w) i x ) (v ∘ Subtype.val) ) : (offer (T.cen w) (V w))∘(Subtype.val: Hold i x→ Tuple X r)=Stalk.collect (T.towards w i x) (v ∘ Subtype.val):=by
 rw [funds w i x hh (V w),hp, united]
 congr 1; ext1 a; apply Subtype.ext; change (T.spring w) ∘ _= update _ _ _; ext1 b; by_cases he:b=i
 · subst b; rw [update_self]; exact (touch w i x hh (projection (T.pack w) i x a)).property
 rw [update_of_ne he]
lemma towards_sends (T:Arch X l R)(i:Fin r)(x:X)(z:Hold i x) : ∀ᶠ w in l,T.towards w i x z=z:=by
 filter_upwards [eventually_all.mpr (fun j:Fin r=> T.tides (z.val j)) ] with w hw; apply Subtype.ext; ext1 y; change update (T.spring w ∘ T.pack w ∘ z.val ) i x y=z.val y; by_cases hy:y=i; rw [hy,update_self]; exact z.property.symm; rw [update_of_ne hy]; exact hw _
def Wingtips (T:Arch X l R)(v:Packet X r)(V:(i:W)→ Packet (R i) r):=∀ w i x, V w ∘ (Subtype.val: Hold i (T.pack w x) → Tuple (R w) r)= Stalk.collect (projection (T.pack w) i x) (v ∘ Subtype.val)
variable {v:Packet X r}{V:(i:W)→ Packet (R i) r}
lemma EarnPivot (h:Wingtips T v V)(hp:∀ x:X,∀ i:Fin r, cost ( v∘ (Subtype.val : Hold i x → Tuple X r )) ≤ C)(hc:C≠⊤): Pivot l C v (fun w=> offer (T.cen w) (V w)):=by
 refine ⟨hc,fun x i=>?_⟩; let τ:=v ∘ (Subtype.val : Hold i x→ Tuple X r); have hm:= Earn.gath (fun w=>T.towards w i x ) ( T.towards_sends i x ) (hp x i) hc
 refine hm.comes ((T.tides x).mono fun w hh=>(paid i x w hh (h w i x)).symm ) fun w=>?_
 by_cases hx:x∈Set.range (T.spring w)
 · change cost ( offer (T.cen w) (V w)∘ _) ≤ _; rw [paid i x w (show T.cen w (T.pos w x) =x from ?_) (h w i x) ]; exact hm.terms w; obtain ⟨a,h'⟩:=hx; rw [← h']; exact congr_arg _ (T.due w a)
 simp_rw [export_miss _ (T.cen w) i x hx]; exact (quota_zero _).le.trans zero_le

def allSum (T:Arch X l R)(A:Arch Y l S): Arch (X⊕Y) l (fun w=>(R w)⊕ (S w)) :={
 spring:= fun w=> (T.spring w).sumMap (A.spring w), pack:= fun w=> Sum.map (T.pack w) (A.pack w), due:= fun w=> Sum.rec (fun x=>congr_arg (Sum.inl: R w→ R w⊕ S w) (T.due w x)) (fun y=>congr_arg _ (A.due w y)), tides:= Sum.rec (fun x=>( T.tides x ).mono fun _ h=>congr_arg Sum.inl h ) (fun y=>( A.tides y ).mono fun _ h=>congr_arg Sum.inr h ) }

end Arch
end YM.RegulatorIR.Budget.FVAAlt2.Wind
