import YM.RegulatorIR.Pupil.High

/-!
# Unfold a nonlocalized vacuum through all slots (without global charge)
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum Laurent WOne Gradient Gradient.Train
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {X Y Z:Type}{G:Gauge}{r:ℕ}

-- enough authority using interpolation entries just billed rows in reverse from output
-- and sup T at fixed legs.
def Limits (T:Packet X r): Prop:=∃ c:ℝ≥0∞,c≠⊤∧∀ x,‖T x‖ₑ≤c
lemma bounds_from {T:Packet X r}{B:Tariff X} {v:ℝ≥0∞} (h:localQ B T v)(hv:v≠⊤): Limits T:=by
 by_cases hp:0<r
 · refine ⟨v,hv,fun x=>?_⟩; let i:Fin r:= ⟨0,hp⟩; let p:Hold i (x i) :=⟨x,rfl⟩; exact le_trans ((mul_one (‖T x‖ₑ)).ge.trans (mul_le_mul_right (B.diameter_unit x) _)) (le_trans (term_le (fun u:Hold i (x i)=> T u.val) (fun u=> B.diameter u.val) p) (h i (x i)))
 have ho:r=0:=by omega
 subst r; let x:Tuple X 0:= fun i=> Fin.elim0 i; exact ⟨_,enorm_ne_top (x:=T x),fun y=> by rw [Subsingleton.elim y x]⟩ -- name
lemma tallS (Z:Type)(t : ℕ)(F: Fin t→ Z→ ℝ≥0∞)(H:∀ i,(∑' j,F i j)≠⊤) : (∑'v: Fin t → Z,∏ i,F i (v i))≠⊤:=by
 rw [Train.tsum_family]; 
 suffices hf :∀ s:Finset (Fin t), (∏ i∈s, (∑' j,F i j))≠⊤ from hf _
 intro s; induction s using Finset.induction_on with | empty=>simp | insert i s hi ih=>rw [prod_insert hi];exact ENNReal.mul_ne_top (H i) ih
lemma offerL {T:Packet X r}(h:Limits T) (p:X↪ Y): Limits (offer p T):=by
 obtain ⟨c,hc,H⟩:=h; refine ⟨_,hc,fun y=>?_⟩; by_cases hv:y∈Set.range (acrossT p)
 · obtain ⟨v,rfl⟩:=hv; rw [offer_eq]; exact H v
 rw [offer_zero _ hv]; simp
lemma pricedField {T:Packet X r}(hT:Limits T) (K:Layer X X)(h:Billed K) (x: Tuple X r)(s:List (Fin r)) : Summable (Gradient.field T K x s):=by
 let f(i:Fin r)(v:X):ℝ≥0∞:=if i∈ s then ‖K (x i) v‖ₑ else if x i=v then 1 else 0
 have hp(i) : (∑' y,f i y)≠⊤:=by unfold f;split_ifs with he; rw [← quota_base]; exact h.rows _; simp
 obtain ⟨c,hc,Hc⟩:=hT; let v(z:Tuple X r):= ∏ i,f i (z i) -- typo
 apply quota_summable (w:=1) (fun _=>le_rfl); rw [quota_base]; apply ne_top_of_le_ne_top (show c* (∑' z,v z)≠⊤ from ENNReal.mul_ne_top hc (tallS X r f hp))
 rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum;intro p; unfold Gradient.field;split
 next he=>
    rw [enorm_mul]; refine mul_le_mul' (Hc p) ?_
    have hh : v p= ∏ i∈ s.toFinset, ‖K (x i) (p i)‖ₑ:=by
       unfold v; rw [← Finset.prod_subset (Finset.subset_univ (s.toFinset)) ?_]; apply prod_congr rfl; intro i hi; unfold f; rw [if_pos (by simpa using hi)]
       intro i _ hi; have hp:i∉ s:=by simpa using hi
       unfold f; rw [if_neg hp,if_pos (he _ hp)]
    rw [hh]; generalize s.toFinset=L; induction L using Finset.induction_on with
    | empty=>simp
    | insert i S h ih=> rw [prod_insert h,prod_insert h,enorm_mul]; apply mul_le_mul_right ih -- hs dep
 next=> rw [enorm_zero];exact bot_le

-- Repeat arrangement. General use covers.We.
lemma wind_up {T:Packet X r}(hT: Limits T)(K:Layer X X)(h:Billed K)(x: Tuple X r)(s: List (Fin r))(H:s.Nodup): drawing T K s x=∑'i,Gradient.field T K x s i:=by
 induction s generalizing x with
 | nil=>
   unfold drawing; rw [tsum_eq_single x]; simp [Gradient.field,Gradient.covers]
   intro i hi; refine if_neg fun hg=>hi (funext fun a=> (hg a (by simp)).symm)
 | cons i s ih=>
    have ht:=pricedField hT K h x (i::s)
    rw [← Stalk.collected_sum _ ht,drawing]; unfold Packet.ray; apply tsum_congr;intro y
    let p(v: Tuple X r):=v i;let z:=Function.update x i y; let v:=Gradient.field T K z s; have he:i∉s:= (List.nodup_cons.mp H).1
    have hf: (∑' u,v u) = ∑' q : Stalk p y,v q.val:=by
       rw [show (∑' u, v u) = ∑' u,(if p u=y then v u else 0) from ?_]; exact (stalk_collect p y v).symm
       apply tsum_congr;intro t;symm; rw [ite_eq_left_iff] -- wrong
       intro ht;symm;apply if_neg; intro hu; exact ht ((hu i he).symm.trans (Function.update_self ..))
    unfold swivel; rw [ih _ (List.nodup_cons.mp H).2]; change K (x i) y* (∑'u,v u)= Stalk.collect p _ y
    rw [hf, ← tsum_mul_left];apply tsum_congr;intro ⟨u,hu⟩;change u i=y at hu
    have hh : covers u x (i::s)↔ covers u z s:=by
       constructor
       · intro h j hi; by_cases H:j=i
         · subst j; rw [show z i=y from Function.update_self ..,hu]
         rw [show z j=x j from Function.update_of_ne H ..]; exact h _ (by simp [hi,H])
       intro h j hi;rw [← show z j=x j from Function.update_of_ne (show j ≠ i from fun he=>hi (by rw [he]; simp)) ..]; exact h _ (fun h=> hi (List.mem_cons_of_mem _ h))
    have ht:∏ j∈ s.toFinset,K (z j) (u j)=∏ j∈s.toFinset,K (x j) (u j):= prod_congr rfl fun j hj=> by rw [show z j=x j from Function.update_of_ne (fun h=>he (by simpa [h] using hj)) ..]
    change K (x i) y * v u=Gradient.field T K x (i::s) u; unfold v Gradient.field; rw [List.toFinset_cons, prod_insert (by simpa using he), hu, ht]; simp_rw [hh]; split <;> ring

lemma draw_update (Γ:Curve X Y)(T:Packet X r)(p:X↪Z)(q:Y↪Z)(K:Layer Z Z)(hc: Gradient.diagonal p q K Γ)(ht:Limits T)(h:Billed K): updateQ Γ T 0=crop q (draft K (offer p T)):=by
 let g:Fin r→ℕ:=0
 have he : Gradient.turns r 0={g}:= by ext i; rw [Gradient.turns_iff, entryZero, Finset.mem_singleton]
 let S:=series Γ g T; let V:= drawing (offer p T) K (List.finRange r); have hf: charge g=0:= (entryZero g).mpr rfl
 let J:((i:Fin r)×Fin (g i+1)) ≃ Fin r := Equiv.ofBijective (fun u=>u.fst) ⟨?_,fun x=> ⟨⟨x,0⟩, rfl⟩⟩
 let e :Fin (r+charge g) ≃ Fin r:=(stations g).symm.trans J
 have hx(v: Tuple Z r): V v= ∑' t, offer p T t* (∏ i,K (v i) (t i)):=by unfold V; rw [wind_up (offerL ht p) _ h _ _ (List.nodup_finRange r)]; simp [Gradient.field,Gradient.covers]
 have hS (z:Tuple Y r): S (z∘e)=crop q V z:=by
    unfold S crop; rw [Function.comp_apply,hx]
    unfold series
    rw [← (injectT p).tsum_eq]; apply tsum_congr; intro x; rw [offer_eq]; apply congr_arg
    unfold tracked trips; apply Finset.prod_congr rfl;intro i _; change Γ _ 0 (_:Tuple Y _) = _; rw [hc]
    apply congr_arg (K · (p (x i))); apply congr_arg q; change z (e (stations g ⟨i,0⟩)) = z i
    unfold e; rw [Equiv.trans_apply, Equiv.symm_apply_apply]; rfl
    intro x hx; by_contra! h; apply hx; change offer _ _ _ * _ = 0; rw [offer_zero _ h,zero_mul]
 unfold updateQ; rw [he,sum_singleton]; ext1 y; rw [cut_uses Γ T g hf e, symm_transport (T:=series Γ g T) (by omega) e hS]; change symmetry (crop q V) y=symmetry V (acrossT q y); rw [symmetry_at,symmetry_at]; rfl
 rintro ⟨x,i⟩ ⟨y,j⟩ he; change x=y at he; subst y; congr!; exact Subsingleton.elim (α:=Fin 1) ..
end YM.RegulatorIR.Pupil
