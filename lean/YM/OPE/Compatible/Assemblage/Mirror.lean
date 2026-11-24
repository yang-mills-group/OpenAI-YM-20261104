import YM.OPE.Compatible.Assemblage.Next
/-!
 # Seam extension on named polynomials. Lift and trim even when number of copies changes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Mirror
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype W][DecidableEq W]{G:Gauge}{n:Side}
    (e:V ↪ W) {d c b t r u : ℝ}
abbrev Mode (V:Type) [Fintype V][DecidableEq V] := (Bud V).Mode
abbrev Words (V:Type) [Fintype V][DecidableEq V] := Poly (Bud V)
def imageM (e:V ↪ W) (p:Mode V) : Mode W:= ⟨p.val.image e,mem_univ _⟩
def invM (e:V ↪ W)(p:Mode W): Mode V:= ⟨univ.filter (fun i=> e i∈p.val),mem_univ _⟩
lemma low_read (i:Mode W)(x:V):x ∈ (invM e i).val ↔ e x∈i.val:=by simp [invM]
lemma tall (p:Mode V) : invM e (imageM e p)=p:=by apply Subtype.ext; ext i; rw [low_read]; exact mem_image_of_injective _ e.injective
lemma mono_read {p q:Mode W}(h:p.val⊆q.val) : (invM e p).val⊆(invM e q).val:=fun _x hx=> (low_read ..).2 (h ((low_read ..).1 hx))
def warm (e:V ↪ W)(p:Mode W):Prop:= imageM e (invM e p)=p
lemma heat_image (p:Mode V): warm e (imageM e p):= congr_arg _ (tall e p)
lemma heat_iff (p:Mode W): warm e p↔ ∀ x∈p.val,∃ i:V,e i=x:=by
   constructor
   · intro h x hx; obtain ⟨i,-,hi⟩:= mem_image.mp ((congr_arg Subtype.val h).symm ▸ hx: x∈ (imageM e (invM e p)).val); exact ⟨i,hi⟩
   intro h; apply Subtype.ext; ext i; constructor
   · intro hp; obtain ⟨j,hx,rfl⟩:= mem_image.mp hp; exact (low_read ..).1 hx
   intro hz; obtain ⟨a,rfl⟩:=h i hz; exact mem_image_of_mem e ((low_read ..).2 hz)
def rise (e:V ↪ W): Words V →ₗ[ℂ] Words W where
   toFun p:= Poly.inject (fun i=> if warm e i then p.part (invM e i) else 0)
   map_add' p q:= by ext i; change (if _ then (p+q).part _ else 0) = (if _ then p.part _ else 0)+(if _ then q.part _ else 0); split_ifs; rfl; simp
   map_smul' r p:= by ext i; change ite (warm e i) _ _=r*ite (warm e i) _ _; split <;> first|rfl|exact (mul_zero _).symm
lemma rises (p:Words V)(i:Mode V): (rise e p).part (imageM e i)= p.part i := (if_pos (heat_image ..)).trans (congr_arg _ (tall e _))
lemma no_rise (p:Words V)(i:Mode W)(h:¬ warm e i): (rise e p).part i=0:=if_neg h
lemma heat_fires (v:V): imageM e ((Bud V).fire v)=(Bud W).fire (e v):=Subtype.ext (image_singleton ..)
lemma heat_quiet : imageM e (Bud V).quiet=(Bud W).quiet:=Subtype.ext (image_empty ..)
def trim (e:V ↪ W): Words W →ₗ[ℂ] Words V where
   toFun p:= Poly.inject (fun i=>p.part (imageM e i))
   map_add' p q:= by ext; rfl
   map_smul' r p:=by ext; rfl
lemma sendH (p:Mode V)(x:ℂ): rise e (Poly.send p x)= Poly.send (imageM e p) x:=by
   ext i; by_cases h:warm e i
   · nth_rw 1 [← show _=_ from (show imageM e (invM e i)=i from h)]; rw [rises,Poly.part_send,Poly.part_send]; refine if_congr ?_ rfl rfl
     exact ⟨fun hp=> h.symm.trans (congr_arg _ hp),fun hp=> (congr_arg _ hp).trans (tall ..)⟩
   rw [no_rise e _ _ h,Poly.part_send,if_neg (fun (hp:i=imageM e p)=>h (hp.symm ▸ heat_image e p))]
lemma high_merge_iff (a b c:Mode V): Poly.merges (imageM e a) (imageM e b) (imageM e c)↔Poly.merges a b c:=by
   unfold Poly.merges; refine and_congr (Finset.disjoint_image e.injective) ?_; unfold imageM; rw [← Finset.image_union]; exact (Finset.image_injective e.injective).eq_iff
lemma rises_mul (p q:Words V): rise e (p*q)=rise e p*rise e q:=by
   rw [← Poly.studs p,← Poly.studs q, Finset.sum_mul, map_sum,map_sum,map_sum,Finset.sum_mul]; refine sum_congr rfl fun i _=>?_
   rw [Finset.mul_sum,map_sum,Finset.mul_sum]; refine sum_congr rfl fun j _=>?_; simp_rw [sendH] -- left stays
   by_cases he: Disjoint i.val j.val
   · let p:Mode V:= ⟨i.val∪j.val,mem_univ _⟩; have ht:Poly.merges i j p:= ⟨he,rfl⟩; rw [tagged_mul _ _ _ ht,tagged_mul _ _ _ ((high_merge_iff e ..).2 ht),sendH]
   rw [show Poly.send i (p.part i)*Poly.send j (q.part j)=0 from not_not.mp (fun h=>he (merges_of_tagged_mul h).choose_spec.1), map_zero]; symm; by_contra hp; apply he; exact (Finset.disjoint_image e.injective).mp (merges_of_tagged_mul hp).choose_spec.1
lemma loose (p:Mode W)(x:ℂ): trim e (Poly.send p x)= if warm e p then Poly.send (invM e p) x else 0:=by
    ext i; change (Poly.send p x).part (imageM e i)=_; rw [Poly.part_send]; by_cases h:warm e p; rw [if_pos h,Poly.part_send]; apply if_congr _ rfl rfl
    · exact ⟨fun he=>(tall ..).symm.trans (congr_arg _ he),fun he=> (congr_arg _ he).trans h⟩
    rw [if_neg h,if_neg (fun (hp:imageM e i=p)=>h (hp ▸ heat_image e i)),Poly.part_nil]
lemma trims_mul (p q:Words W) : trim e (p*q)= trim e p*trim e q:=by
    rw [← Poly.studs p, ← Poly.studs q,Finset.sum_mul,map_sum,map_sum,map_sum,Finset.sum_mul]; refine sum_congr rfl fun i _=>?_; rw [Finset.mul_sum,map_sum, Finset.mul_sum]; refine sum_congr rfl fun j _=>?_
    let w:=p.part i; let w':= q.part j; change trim e (Poly.send _ w * Poly.send _ w')= _
    by_cases he:warm e i∧ warm e j
    · obtain ⟨u,v⟩:= he; have hu:imageM e (invM e i)=i:=u; have hv:imageM e (invM e j)=j:=v; rw [loose,loose,if_pos u,if_pos v]; ext x; change (Poly.prod (Poly.send i _) (Poly.send j _)).part _=(Poly.prod (Poly.send (invM e i) _) (Poly.send (invM e j) _)).part _; rw [Poly.cart,Poly.cart]; refine if_congr ?_ rfl rfl; exact (by
          have hh:= high_merge_iff e (invM e i) (invM e j) x; rw [hu,hv] at hh; exact hh)
    rw [loose,loose]; by_cases hν:Disjoint i.val j.val
    · let u:Mode W:= ⟨i.val∪j.val,mem_univ _⟩; rw [tagged_mul i j u (⟨hν,rfl⟩:Poly.merges i j u),loose,if_neg]; by_cases hp:warm e i; rw [if_neg (fun h=> he ⟨hp,h⟩),mul_zero]; rw [if_neg hp,zero_mul]
      intro h; apply he; exact ⟨(heat_iff e i).2 (fun v hv=> (heat_iff e u).1 h v (Finset.mem_union_left _ hv)), (heat_iff e j).2 (fun v hv=> (heat_iff e u).1 h v (Finset.mem_union_right _ hv))⟩
    rw [show Poly.send i w*Poly.send j w'=0 from not_not.mp (fun h=>hν (merges_of_tagged_mul h).choose_spec.1),map_zero]; by_cases hp:warm e i; rw [if_neg (fun h=> he ⟨hp,h⟩),mul_zero]; rw [if_neg hp,zero_mul]
-- cost general multiplicative map pass; use both algebras truncated
lemma passM (F: Words V→ₗ[ℂ] Words W)(h:F 1=1)(hr:∀ x y,F (x*y)=F x*F y)(p:Words V)(hh:p.part (Bud V).quiet=0)(hk:(F p).part (Bud W).quiet=0):F (Poly.pass p)=Poly.pass (F p):=by
   let N:= Fintype.card V+Fintype.card W
   have he {J:Type} [Fintype J][DecidableEq J] (x:Words J)(h:x.part (Bud J).quiet=0)(hp:Fintype.card J≤ N):
       Poly.pass x=∑ i∈Finset.range (N+1), (i.factorial:ℂ)⁻¹ • x^i:= by
       refine sum_subset (range_mono (Nat.add_le_add_right hp _)) (fun i hi hh=>?_); rw [Poly.stops x h i (by simp at hh;omega),smul_zero]
   have hp(a:ℕ):F (p^a)=F p^a:=by
      induction a with
      | zero=> rw [pow_zero,pow_zero,h]
      | succ k ih=>rw [pow_succ,pow_succ,hr,ih]
   rw [he p hh (by omega),he (F p) hk (by omega),map_sum]; exact sum_congr rfl fun i _=>by rw [map_smul,hp]
lemma poly_product {A:Type}(F:Words V→ₗ[ℂ] Words W)(h:F 1=1)(hr:∀ x y,F (x*y)=F x*F y)(s:Finset A)(v:A→Words V):F (∏ i∈s,v i)=∏ i∈s,F (v i):=by induction s using Finset.induction_on with
    | empty=> simpa only [prod_empty] using h
    | @insert i s hi ih=> rw [prod_insert hi,prod_insert hi,hr,ih]
lemma field_map (F:Words V→ₗ[ℂ] Words W)(h:F 1=1)(hr:∀ x y,F (x*y)=F x*F y)(K:Box n→Words V)(s:Support n): F (field K s)=field (fun i=>F (K i)) s:=by
    unfold field; rw [map_sum]; refine sum_congr rfl fun i _=> ?_; unfold grid; split; next=> exact poly_product F h hr i K
    next=> exact map_zero F
lemma high_one : rise e 1=1:=by change rise e (Poly.send _ 1)=_; rw [sendH,heat_quiet]; rfl
lemma low_one : trim e 1=1:=by ext i; change (1:Words W).part (imageM e i)=_;rw [Poly.one_part,Poly.one_part]; apply if_congr _ rfl rfl; rw [← heat_quiet e]; exact (show Injective (imageM e) from LeftInverse.injective (show LeftInverse _ _ from tall e)).eq_iff
end YM.MergeProof.Ribbons.ManyCopies.Mirror
