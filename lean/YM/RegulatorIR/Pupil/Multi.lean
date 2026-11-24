import YM.RegulatorIR.Pupil.Dues

/-! Compact field tests and axial polarization. Use powerset before opening
any price (keeps one distinguished variation in view). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{W I: Type}{r:ℕ}

abbrev GivesT (A:BEdge G):= (Function.support A).Finite
section Support
variable {A B:BEdge G}{p:Signed}{k:G.El}
lemma gives_add (h:GivesT A)(hv:GivesT B):GivesT (A+B) := (h.union hv).subset (support_add ..) -- name
lemma gives_beast (h:GivesT A): GivesT (beast p A):= (h.preimage (revol p).injective.injOn).subset (by intro i hi; change A (rotateE p i)≠0; exact fun h=> hi (by unfold beast;rw [h];simp))
lemma gives_vbadge (h:GivesT A): GivesT (vbadge k A) := h.subset (by intro x hx; exact fun h=> hx (by unfold vbadge; rw [h,map_zero]))
lemma gives_reg {σ:Cover→ G.Color}(h:(Function.support σ).Finite) : GivesT (regalia σ):=by
 let s:= Set.prod (Function.support σ) (Set.univ:Set Axis); let p: Edge Cover→ Edge Cover:= fun i=> (i.1-step i.2,i.2); have ht:s.Finite:=h.prod (Set.toFinite _)
 refine (ht.union (ht.image p)).subset ?_;rintro i (hi:regalia σ i≠0); by_cases hx:σ i.1=0
 · have hh: σ (i.1+step i.2)≠0:=fun hg=>hi (by simp only [regalia,hg,hx,sub_self]); exact Or.inr ⟨(i.1+step i.2,i.2), ⟨hh,Set.mem_univ _⟩, by simp [p]⟩
 exact Or.inl ⟨hx,Set.mem_univ _⟩
lemma hue_finite (H:GivesT A):(Function.support (hue A)).Finite:= (H.prod (Set.toFinite (Set.univ:Set G.ColorIndex))).subset (by rintro i (hi:hue A i≠0); exact ⟨fun hh => hi (by unfold hue; rw [hh,PiLp.zero_apply]),Set.mem_univ _⟩)
lemma sum_gives (s: Finset I)(A:I→ BEdge G) (h:∀ i,GivesT (A i)): GivesT (∑ i∈s,A i):=by induction s using Finset.induction_on with
 | empty=> simp [GivesT]
 | insert a v hx ih=> rw [sum_insert hx]; exact gives_add (h a) ih
end Support
section Multi
lemma pay_summable (T:Packet I r)(F:Fin r→ I→ℝ)(h:∀ i,(Function.support (F i)).Finite): Summable fun x:Tuple I r=> T x * ∏ i,F i (x i):=by
 refine summable_of_hasFiniteSupport ((Set.Finite.pi h).subset ?_); intro x (hx : T x * _≠0); exact fun i _ hh=>hx (mul_eq_zero_of_right _ (Finset.prod_eq_zero (i:=i) (mem_univ _) hh))
lemma constructive (z: Finset (Fin r))(T:Packet I r)(X: Fin r→ I→ℝ)(h:∀ i,(Function.support (X i)).Finite):
 chargeT T (fun _=>∑ i∈z, X i)= ∑ p∈ Fintype.piFinset (fun _ : Fin r=>z),chargeT T (X ∘ p):=by
 unfold chargeT; simp_rw [Finset.sum_apply, show ∀ x:Tuple I r,(∏ i,∑ j∈z,X j (x i))= ∑ p∈Fintype.piFinset (fun _:Fin r=> z),∏ i,X (p i) (x i) from fun x=> Finset.prod_univ_sum (fun _=>z) (fun i j=> X j (x i)),mul_sum]; exact Summable.tsum_finsetSum (fun p _=> pay_summable T (X∘ p) fun j=>h (p j))
lemma rotates (T:Packet I r)(H:IsSym T)(p:Equiv.Perm (Fin r))(V:Fin r→ I→ℝ): chargeT T (V ∘ p)=chargeT T V:=by unfold chargeT; rw (occs:=.pos [1]) [← (Tuple.perm I p).tsum_eq]; apply tsum_congr;intro x; rw [show Tuple.perm I p x=x ∘ p from rfl,H p]; exact congr_arg (T x*·) (Equiv.prod_comp p (fun i=> V i (x i)))
end Multi

-- power-set operations.
def adjure (u:Finset (Fin r)→ℝ)(S:Finset (Fin r)) := ∑ x ∈ S.powerset,(-1:ℝ)^(S.card-x.card)*u x
lemma remove (u:Finset (Fin r)→ℝ)(S:Finset (Fin r))(v:Fin r)(h:v∈S): adjure u S= adjure (fun x=>u (insert v x)-u x) (S.erase v):=by
 let F:= S.erase v
 let f(x:Finset (Fin r)):= (-1:ℝ)^(F.card-x.card); let g(x:Finset (Fin r)):= (-1:ℝ)^(S.card-x.card)*u x
 have hp:F.card+1=S.card:=card_erase_add_one h
 have h₀(x)(hx:x∈ F.powerset): v∉ x:=fun hv=> Finset.notMem_erase v S ((mem_powerset.mp hx) hv)
 have h₁(x)(hx:x∈ F.powerset): g x= -(f x*u x):=by
    have hh:=Finset.card_le_card (mem_powerset.mp hx); unfold f g;rw [show S.card-x.card=(F.card-x.card)+1 by omega,pow_succ];ring
 have h₂(x)(hx:x∈ F.powerset): g (insert v x)= f x*u (insert v x):=by unfold f g; rw [card_insert_of_notMem (h₀ x hx),← hp,Nat.add_sub_add_right]
 change ∑ x ∈ S.powerset,g x=∑ x∈F.powerset,f x*(u (insert v x)-u x);rw (occs:=.pos [1]) [← show insert v F=S from insert_erase h];rw [sum_powerset_insert (notMem_erase v S),Finset.sum_congr rfl h₁, Finset.sum_congr rfl h₂]; simp_rw [sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]; abel
lemma adjure_eq {u v:Finset (Fin r)→ℝ}{S : Finset (Fin r)}(h:∀ x,x∈S.powerset → u x=v x): adjure u S=adjure v S:=Finset.sum_congr rfl fun x hx=>congr_arg (_*·) (h x hx)
lemma one_pick (p:Fin r→Fin r) (a:ℝ) : adjure (fun x=> if p∈ Fintype.piFinset fun _=>x then a else 0) univ= if (∃ f:Equiv.Perm (Fin r),p=f) then a else 0:=by
 split
 next h=> obtain ⟨f,rfl⟩:=h; unfold adjure; rw [sum_eq_single_of_mem (univ:Finset (Fin r)) (mem_powerset.mpr (Finset.Subset.refl _))]; simp
          intro y _ h; dsimp only;rw [if_neg, mul_zero]; intro e; exact h (by apply Finset.eq_univ_of_forall; intro i; obtain ⟨z,rfl⟩:= f.surjective i; exact Fintype.mem_piFinset.mp e z)
 next h=>
    have hv : ¬Surjective p:= fun he=> h ⟨Equiv.ofBijective p ⟨Finite.injective_iff_surjective.mpr he,he⟩,rfl⟩
    obtain ⟨y,hy⟩:= not_forall.mp hv; let u : Finset (Fin r)→ℝ:=fun x=> if p∈ Fintype.piFinset (fun _=>x) then a else 0; let v := univ.erase y
    change adjure u univ=0
    rw [remove u univ y (mem_univ _)];unfold adjure; apply sum_eq_zero;intro b hb; dsimp only; rw [show u (insert y b)=u b from ?_,sub_self,mul_zero]
    unfold u; have hp(w:Fin r): p w∈ insert y b ↔ p w∈ b:=by simp only [Finset.mem_insert]; exact or_iff_right (fun h=>hy ⟨w,h⟩)
    simp_rw [Fintype.mem_piFinset,hp]

lemma royal (T:Packet I r) (H:IsSym T)(X:Fin r→ I →ℝ)(h:∀ i,(Function.support (X i)).Finite): adjure (fun s=> chargeT T (fun _=>∑ i∈s,X i)) univ = (r.factorial:ℝ)*chargeT T X:=by
 unfold adjure; simp_rw [constructive _ _ X h]; let P:= (univ : Finset (Fin r→Fin r)); let Y(u:Fin r→Fin r):= chargeT T (X ∘ u); let U(s:Finset (Fin r)):= Fintype.piFinset fun _:Fin r=>s
 have ht s : ∑ p∈ U s,Y p = ∑ p∈ P,if p∈ U s then Y p else 0:=by rw [← Finset.sum_filter]; congr; ext p; simp [P]
 change ∑ x∈(Finset.univ:Finset (Fin r)).powerset,(-1:ℝ)^((Finset.univ:Finset (Fin r)).card-x.card)*(∑ p∈U x,Y p)=_;simp_rw [ht, Finset.mul_sum];rw [sum_comm]
 let f:= fun x:Equiv.Perm (Fin r)=> (x:Fin r→Fin r)
 simp_rw [show ∀ p:Fin r→Fin r,∑ s∈ (univ:Finset (Fin r)).powerset, (-1:ℝ)^((univ:Finset (Fin r)).card-s.card)*(if p∈ U s then Y p else 0) = _ from fun p=>one_pick p (Y p)] -- f not mentioned
 let Q:= P.filter (fun p=> ∃ w:Equiv.Perm (Fin r),p=(w:Fin r→Fin r)); have hv : Q = (univ:Finset (Equiv.Perm (Fin r))).image f:=by
    ext j;simp only [Q,P,mem_filter,Finset.mem_univ,true_and,Finset.mem_image]; constructor <;> rintro ⟨w,h⟩
    · exact ⟨w,h.symm⟩
    exact ⟨w,h.symm⟩
 rw [← Finset.sum_filter]; change ∑ p∈Q,Y p= _; rw [hv, sum_image]; swap; exact (show Injective f from fun i j he=> Equiv.ext (congr_fun he)).injOn
 simp_rw [fun p=> show Y (f p)=_ from rotates T H p X,Finset.sum_const, card_univ,Fintype.card_perm];simp
lemma ritual (T:Packet (Foot G) r)(H:IsSym T)(A:Fin r→BEdge G)(hp:∀ i,GivesT (A i)): adjure (fun x=> oblique T (∑ i∈x,A i)) univ=(r.factorial:ℝ)*matchT T A:=by
 let p' x:=∑ i∈x,A i
 unfold matchT; rw [← royal T H (fun i=> hue (A i)) (fun i=>hue_finite (hp i))]
 apply adjure_eq;intro x _;unfold oblique matchT;apply congr_arg;ext i j; unfold hue; simp only [Finset.sum_apply]; exact map_sum (PiLp.proj 2 (fun _ : G.ColorIndex=>ℝ) j.2 : G.Color →L[ℝ] ℝ) (fun i=> A i j.1) x
end YM.RegulatorIR.Pupil
