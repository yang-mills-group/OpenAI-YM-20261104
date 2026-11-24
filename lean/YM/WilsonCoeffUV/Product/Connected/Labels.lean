import YM.WilsonCoeffUV.Product.I.Ripple
/-!
# Pointwise product of distinct marks in the same profile chart
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{j r e k h s i a b:ℕ}{U V E W ι D:Type*}{G:Gauge}
section
-- real from Comm Norm algebra optional: only semibilinear
variable [NormedRing V] [NormedAlgebra ℝ V]
def webT (P: Ten V U i)(Q: Ten V U j)(r:ℕ): Ten V U r:= fun x=> if h:i+j=r then P (x ∘ Fin.cast h ∘ Fin.castAdd j)*Q (x∘ Fin.cast h ∘ Fin.natAdd i) else 0
def knitS (P Q: Gen V U) : Gen V U := fun r=>swirl (∑ j∈Finset.antidiagonal r, webT (P j.1) (Q j.2) r)
def woad (P Q:Pal V U):Pal V U:=fun e=>∑ j∈ Finset.antidiagonal e,knitS (P j.1) (Q j.2)
def tassel (P Q:Layers V U):Layers V U:= fun e=> ∑ j∈Finset.antidiagonal e, woad (P j.1) (Q j.2)
lemma woad_shell (P Q:Pal V U)(p:shellK i P)(q:shellK j Q): shellK (i+j) (woad P Q):=by
    intro e r h; unfold woad; rw [Finset.sum_apply]; apply Finset.sum_eq_zero; intro v hv; have he:= Finset.mem_antidiagonal.mp hv; unfold knitS; rw [Finset.sum_eq_zero]; · exact swirl_exact Blue.Smooth.zero
    intro w hw; have hx:= Finset.mem_antidiagonal.mp hw; funext x; unfold webT; rw [dif_pos hx]; by_cases hp : i+v.1 < w.1; · rw [p _ _ hp]; exact zero_mul _
    rw [q _ _ (by omega)]; exact mul_zero _
lemma woad_pure (P Q:Pal V U)(i): Pure (woad P Q i):=by
    intro r; unfold woad; rw [Finset.sum_apply]; exact Blue.Smooth.sum fun k _=> swirl_smooth _
lemma tassel_stop (P Q:Layers V U)(p:stops i P)(q:stops j Q): stops (i+j) (tassel P Q):=by
   intro e r t u; unfold tassel; simp_rw [Finset.sum_apply]; apply Finset.sum_eq_zero; intro v hv; have he:= Finset.mem_antidiagonal.mp hv; unfold woad; simp_rw [Finset.sum_apply]; apply Finset.sum_eq_zero; intro w hw; have hx:= Finset.mem_antidiagonal.mp hw; unfold knitS; rw [Finset.sum_eq_zero]; · exact swirl_exact Blue.Smooth.zero
   intro n hn; have hu:=Finset.mem_antidiagonal.mp hn; funext x; unfold webT; rw [dif_pos hu]; by_cases h:w.1+i<n.1∨i+3*w.1<n.1+2*v.1; · rw [p _ _ _ (by omega)]; exact zero_mul _
   rw [q _ _ _ (by omega)]; exact mul_zero _
lemma tassel_pure (P Q:Layers V U)(i j): Pure (tassel P Q i j):=by
   intro r; unfold tassel; simp_rw [Finset.sum_apply]; exact Blue.Smooth.sum fun k _=>woad_pure _ _ _ _
lemma woad_ply (P Q:Pal V U)(v:V→ₐ[ℝ]ℝ): ply v.toLinearMap (woad P Q)=woad (ply v.toLinearMap P) (ply v.toLinearMap Q):=by
    ext1 i; funext j; change tinct v.toLinearMap ((woad P Q) i j)= _; unfold woad; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; refine Finset.sum_congr rfl fun k _=>?_ ; unfold knitS; rw [cloak_swirl,map_sum]; apply congr_arg swirl; apply Finset.sum_congr rfl; intro l hl; funext x; have ht:= Finset.mem_antidiagonal.mp hl; unfold webT; change v (if _:_ then _ else _)= _
    rw [dif_pos ht,dif_pos ht,map_mul]; rfl

-- native aggregate center. Bends
lemma webT_tread {L:Type*}(d:Bank.Distance U)(o:U)(t:i+j=r)(x:dock U L r): let v:=x ∘ Fin.cast t ∘ Fin.castAdd j; let b:=x ∘ Fin.cast t ∘ Fin.natAdd i; tread d o x≤ tread d o v+tread d o b:=by
    subst r; intro v b; let T:=stud o x; let V:=stud o v; let B:=stud o b; let P:=league d V; let Q:=league d B
    have he k : (∃ l,T k=V l)∨(∃ l,T k=B l):= Fin.cases (Or.inl ⟨0,rfl⟩) (fun k=>Fin.addCases (m:=i) (n:=j) (fun i=>Or.inl ⟨Fin.succ i,rfl⟩) (fun i=>Or.inr ⟨Fin.succ i,rfl⟩) k) k
    have hh i j: d.gap (V i) (B j)≤P+Q:= by apply (d.tri (V i) o (B j)).trans; exact add_le_add (leg_le d V i 0) (leg_le d B 0 j)
    apply league_le d T; intro i j; rcases he i with ⟨a,ha⟩|⟨a,ha⟩ <;> rcases he j with ⟨b',hb⟩|⟨b',hb⟩ <;> rw [ha,hb]
    · exact (leg_le d V _ _).trans (Nat.le_add_right ..)
    · exact hh ..
    · rw [d.swap]; exact hh ..
    exact (leg_le d B _ _).trans (Nat.le_add_left ..)
omit [NormedAlgebra ℝ V] in
lemma webCork {V':Type*}{d:Bank.Distance V'}{t o w:ℝ}{p:V'} (u:0≤t)(P:Ten V (V'×U) i)(Q: Ten V (V'×U) j)(h:i+j=r)(hp:Cork d p t o P)(hf:Cork d p t w Q): Cork d p t (o*w) (webT P Q r):=by
   refine ⟨mul_nonneg hp.1 hf.1,fun x=>?_⟩; unfold webT; rw [dif_pos h]; apply (norm_mul_le ..).trans; set v:= x ∘ _ ∘ Fin.castAdd j; set b:=x ∘ _ ∘ Fin.natAdd i; have hV:=hp.2 v; have hB:=hf.2 b; refine (mul_le_mul hV hB (norm_nonneg _) ((norm_nonneg _).trans hV)).trans ?_; rw [mul_mul_mul_comm,←Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.1 hf.1); apply Real.exp_le_exp.mpr; rw [←mul_add,← Nat.cast_add]; exact mul_le_mul_of_nonpos_left (by exact_mod_cast webT_tread d p h x) (by linarith)
omit [NormedAlgebra ℝ V] in
lemma webBends {P:raw U V i}{Q:raw U V j}{T:Ten V (Cover×U) i}{F:Ten V (Cover×U) j}{o}(b:i+j=r)(t:Bends o P T)(h:Bends o Q F): Bends o (fun n=> webT (P n) (Q n) r) (webT T F r):=by
   obtain ⟨s,a,hS,K⟩:=t.price; obtain ⟨v,B,hv,H⟩:=h.price; refine ⟨fun x=>?_,min s v,a*B,lt_min hS hv,(K.and H).mono fun n hn=> webCork (lt_min hS hv).le _ _ b (hn.1.mono (min_le_left ..)) (hn.2.mono (min_le_right ..))⟩
   unfold webT; simp_rw [dif_pos b]; exact (t.point _).mul (h.point _)
lemma swivelBack {P:raw U V i}{T:Ten V (Cover×U) i}(t:Bends 0 P T): Bends 0 (fun n=>swirl (P n)) (swirl T):=by
   have he (j:Equiv.Perm (Fin i)): Bends 0 (fun n x=>P n (x ∘ j)) (fun x=>T (x ∘ j)):=by
       obtain ⟨s,A,h,H⟩:=t.price; refine ⟨fun i=>t.point _,s,A,h,H.mono fun n hn=>⟨hn.1,fun x=>?_⟩⟩; let p:=wrap n (0:Cover); let Q:= ((finSuccEquiv i).trans (Equiv.optionCongr j)).trans (finSuccEquiv i).symm
       have hm: stud p (x ∘ j)= stud p x ∘ Q:= by
          funext i; refine Fin.cases (by simp [Q,stud]) (fun i=> by simp [Q,stud]) i
       apply (hn.2 (x ∘ j)).trans; unfold p at hm; unfold tread; rw [hm,league_equiv]
   let Z:= (Equiv.Perm (Fin i)); let S:Finset Z:=Finset.univ
   exact Soil.Bends.μ (anzas S (fun i _=> he i)) _
lemma Bends_woad {P Q:(n:Side)→Pal V (Co n U)}{S T: Pal V (Cloth U)}(p:∀ i j,Bends 0 (fun n=>P n i j) (S i j))(q:∀ i j,Bends 0 (fun n=>Q n i j) (T i j))(e r): Bends 0 (fun n=> woad (P n) (Q n) e r) (woad S T e r):=by
   simp_rw [woad,Finset.sum_apply]; exact anzas (P:=fun (j:ℕ×ℕ) n=> knitS (P n j.1) (Q n j.2) r) (V:=V) (Finset.antidiagonal e) fun i _=> swivelBack (anzas (P:=fun j n=> webT (P n i.1 j.1) (Q n i.2 j.2) r) (Finset.antidiagonal r) (fun j hj=>webBends (Finset.mem_antidiagonal.mp hj) (p i.1 j.1) (q i.2 j.2)))
lemma Bends_tassel {P Q:(n:Side)→Layers V (Co n U)}{S T:Layers V (Cloth U)}(p:∀ i j v,Bends 0 (fun n=>P n i j v) (S i j v))(q:∀ i j v,Bends 0 (fun n=>Q n i j v) (T i j v))(e k r):Bends 0 (fun n=> tassel (P n) (Q n) e k r) (tassel S T e k r):=by
   simp_rw [tassel,Finset.sum_apply]; exact anzas (P:=fun (j:ℕ×ℕ) n=> woad (P n j.1) (Q n j.2) k r) (Finset.antidiagonal e) fun j _=> Bends_woad (P:=fun n=>P n j.1) (Q:=fun n=>Q n j.2) (p j.1) (q j.2) _ _
end
section
variable [Fintype U]
omit [Fintype U] in
lemma knit_spore (P Q:Gen ℝ U) (r): knitS P Q r=swirl (spore P Q r):=rfl
lemma woolR (P Q:Gen ℝ U): totalR (knitS P Q)= totalR (spore P Q):= finsum_congr fun _i=>swirl_paint _
omit [Fintype U] in
lemma knit_f {P Q:Gen ℝ U}(p:FiniteGen P)(q:FiniteGen Q):FiniteGen (knitS P Q):=squeezed _ (finite_spore p q)
lemma woadap (P Q:Pal ℝ U)(p: ∀ i,FiniteGen (P i))(q:∀ i,FiniteGen (Q i)): flash (woad P Q)= flash P* flash Q:=by
   ext1 n; simp only [flash,coeff_mul,coeff_mk,woad]; rw [visible_sum (fun i _=>knit_f (p i.1) (q i.2))]; exact Finset.sum_congr rfl fun i _=>(woolR ..).trans (visible_spore (p _) (q _))
omit [Fintype U] in
lemma glances (P Q:Ink (Option U))(i j:ℕ) : spanT i U (coeff j (P*Q)) = ∑ a∈Finset.antidiagonal i,∑ b∈Finset.antidiagonal j, spanT a.1 U (coeff b.1 P) * spanT a.2 U (coeff b.2 Q) := by
  simp_rw [coeff_mul,map_sum, span_time,map_mul,Polynomial.coeff_mul]; rw [Finset.sum_comm]
lemma ramp_joint (P Q:Layers ℝ U)(p:stops i P)(q:stops j Q): ramp (tassel P Q) (i+j)=ramp P i *ramp Q j:=by
    apply lamp_ext; intro e r; rw [glances,glance (tassel_stop P Q p q)]; simp_rw [glance p,glance q,tassel,Finset.sum_apply]; simp_rw [woad]; rw [visible_sum (fun i _=>finite_sum fun j _=>knit_f (finite_stops p ..) (finite_stops q ..))]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [visible_sum (fun j _=>knit_f (finite_stops p ..) (finite_stops q ..))]; exact Finset.sum_congr rfl fun _ _=> (woolR ..).trans (visible_spore (finite_stops p ..) (finite_stops q ..))
end
end YM.WilsonCoeffUV.Mer
