import YM.WilsonCoeffUV.Series.Caloric
/-!
# Polynomial tensor families

Arbitrary module-valued (sampling slots), count variables in rgb.
No volume scaling in these operators; emission normalization separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Function Matrix MvPolynomial Finset
open scoped BigOperators
variable {R R' U : Type*}

abbrev Gen (R U:Type*) := (r:ℕ)→ Ten R U r
def Pure (P:Gen R U) := ∀ r, Smooth (P r)

section arrows
variable [AddCommGroup R][Module ℝ R]
def still (P:Gen R U)(n:ℕ): Prop := ∀ j≥n,P j=0
def FiniteGen (P:Gen R U) := ∃ n,still P n
omit [Module ℝ R] in
lemma still.mono {n m}{P:Gen R U}(h:still P n)(ht:n≤m): still P m:= fun i hi=> h i (ht.trans hi)

def sever (a:U)(P:Gen R U):Gen R U:= fun k=>(k+1) • prune (P (k+1)) a
omit [Module ℝ R] in
lemma pure_sever (a:U){P:Gen R U}(h:Pure P) : Pure (sever a P):= fun r=> ((h (r+1)).prune a).smul _
omit [Module ℝ R] in
lemma finite_sever (a:U){P:Gen R U}(h:FiniteGen P) : FiniteGen (sever a P):= ⟨h.choose, fun i hi=> by rw [sever,h.choose_spec (i+1) (by omega), show prune _ _=0 from rfl]; exact smul_zero _⟩

-- cast extractor for exterior rank add.
def interweave {r t : ℕ}(P:Ten ℝ U r)(Q:Ten R U t)(s:ℕ) : Ten R U s := fun x=> if h:r+t=s then
  P (x ∘ Fin.cast h ∘ Fin.castAdd t) • Q (x ∘ Fin.cast h ∘ Fin.natAdd r) else 0
def spore (P:Gen ℝ U)(Q:Gen R U) : Gen R U := fun r=>∑ j∈antidiagonal r, interweave (P j.1) (Q j.2) r
lemma inter_zero_left {r t s : ℕ}(Q:Ten R U t): interweave (0:Ten ℝ U r) Q s=0:=funext fun x=> by simp [interweave]
lemma inter_zero_right {r t s : ℕ}(P:Ten ℝ U r): interweave P (0:Ten R U t) s=0 := funext fun x=> by simp [interweave]
lemma finite_spore {P:Gen ℝ U}{Q:Gen R U}(h:FiniteGen P)(t:FiniteGen Q) : FiniteGen (spore P Q) := by
  refine ⟨h.choose+t.choose,fun i hi=>sum_eq_zero fun j hj=>?_⟩
  by_cases hh:h.choose≤j.1; rw [h.choose_spec j.1 hh, inter_zero_left]
  rw [t.choose_spec j.2 (by have he:j.1+j.2=i:=mem_antidiagonal.mp hj; omega), inter_zero_right]
omit [Module ℝ R] in
lemma finite_add {P Q:Gen R U}(h:FiniteGen P)(t:FiniteGen Q) : FiniteGen (P+Q):= ⟨max h.choose t.choose, fun i hi=> by rw [Pi.add_apply,h.choose_spec i ((le_max_left ..).trans hi),t.choose_spec i ((le_max_right ..).trans hi)]; simp⟩
lemma finite_μ
  {P:Gen R U}(h:FiniteGen P)(c:ℝ) : FiniteGen (c•P):=⟨h.choose,fun i hi=>by rw [Pi.smul_apply,h.choose_spec i hi,smul_zero]⟩
omit [Module ℝ R] in
lemma finite_sum {I:Type*}{q:Finset I}{P:I→ Gen R U}(h:∀ i∈q,FiniteGen (P i)):FiniteGen (∑ i∈q,P i) := by
  classical
  induction q using Finset.induction_on with
  | empty=> rw [Finset.sum_empty]; exact ⟨0,fun _ _=>rfl⟩
  | @insert i q hi H=> rw [sum_insert hi]; exact finite_add (h i (mem_insert_self ..)) (H fun j hj=>h j (mem_insert_of_mem hj))
lemma squeezed (P:Gen R U)(h:FiniteGen P): FiniteGen fun i=>swirl (P i):=⟨h.choose, fun i hi=> by change swirl (P i)=0; rw [h.choose_spec i hi,swirl_exact Smooth.zero]⟩

variable [Fintype U]

def ripple (G:Matrix U U ℝ)(P:Gen R U): Gen R U:= ∑ a:U,∑ b:U,(G a b/2) • sever a (sever b P)
lemma ripple_form (G:Matrix U U ℝ)(P:Gen R U)(r) : ripple G P r=∑ a: U,∑ b:U,(G a b/2) • sever a (sever b P) r := by simp_rw [ripple,Finset.sum_apply,Pi.smul_apply]
lemma pure_ripple (G:Matrix U U ℝ){P:Gen R U}(h:Pure P) : Pure (ripple G P):= fun i=> by rw [ripple_form]; exact Smooth.sum fun a _=>Smooth.sum fun b _ =>(pure_sever a (pure_sever b h) i).smul _
lemma finite_ripple (G:Matrix U U ℝ){P:Gen R U}(h:FiniteGen P) : FiniteGen (ripple G P):= finite_sum fun a _=>finite_sum fun b _=>finite_μ (finite_sever a (finite_sever b h)) _
lemma ripple_zero_at (G : Matrix U U ℝ) (P:Gen R U)(r)(h:P (r+2)=0): ripple G P r=0 := by
  rw [ripple_form]; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro b _; simp_rw [sever,h]; funext t; simp [prune]

def arbor (G:Matrix U U ℝ)(P:Gen ℝ U)(Q:Gen R U):Gen R U:= ∑ a:U,∑ b:U,(G a b/2) • fun r=>swirl (spore (sever a P) (sever b Q) r)
lemma arbor_form (G:Matrix U U ℝ)(P:Gen ℝ U)(Q:Gen R U)(r) : arbor G P Q r=∑ a,∑ b,(G a b/2) • swirl (spore (sever a P) (sever b Q) r) := by simp_rw [arbor,Finset.sum_apply,Pi.smul_apply]
lemma arbor_pure (G:Matrix U U ℝ)(P:Gen ℝ U)(Q:Gen R U): Pure (arbor G P Q):= fun r=> by rw [arbor_form]; exact Smooth.sum fun i _=> Smooth.sum fun j _=> (swirl_smooth _).smul _
lemma finite_arbor (G:Matrix U U ℝ){P:Gen ℝ U}(h:FiniteGen P){Q:Gen R U}(q:FiniteGen Q): FiniteGen (arbor G P Q):= finite_sum fun i _=>finite_sum fun j _=>finite_μ (squeezed _ (finite_spore (finite_sever i h) (finite_sever j q))) _
lemma arbor_zero_at (G:Matrix U U ℝ)(P:Gen ℝ U)(Q:Gen R U)(s)(h:∀ x y:ℕ,x+y=s→ P (x+1)=0 ∨ Q (y+1)=0) : arbor G P Q s=0 := by
  rw [arbor_form]; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro b _
  have hh: spore (sever a P) (sever b Q) s=0 := by
    apply Finset.sum_eq_zero; intro k hk; obtain he|he := h _ _ (Finset.mem_antidiagonal.mp hk)
    · rw [sever,he, show prune _ _=0 from rfl,smul_zero,inter_zero_left]
    have hx : sever b Q k.2=0 := by rw [sever,he,show prune _ _=0 from rfl,smul_zero]
    rw [hx,inter_zero_right]
  rw [hh, swirl_exact Smooth.zero,smul_zero]
end arrows

section real
variable [Fintype U]

def totalR (P:Gen ℝ U) : POL U := ∑ᶠ i, paint i (P i)
lemma visible {P:Gen ℝ U}{n}(h:still P n): totalR P=∑ i∈range n,paint i (P i) := by rw [totalR]; exact finsum_eq_sum_of_support_subset _ fun i hi=> by contrapose! hi; simp [Function.mem_support,h i (by simpa using hi)]
lemma seen {P:Gen ℝ U}(h:FiniteGen P): Function.HasFiniteSupport fun i=>paint i (P i) := Set.Finite.subset (s:=Set.Iio h.choose) (Set.finite_Iio _) (fun i h'=> show _ from by contrapose! h'; simp [Function.mem_support,h.choose_spec i (by simpa using h')])
lemma visible_add {P Q:Gen ℝ U}(h:FiniteGen P)(he:FiniteGen Q) : totalR (P+Q)=totalR P + totalR Q := by unfold totalR; simp_rw [Pi.add_apply,map_add]; exact finsum_add_distrib (seen h) (seen he)
lemma visible_μ {P:Gen ℝ U}(h:FiniteGen P)(c:ℝ): totalR (c•P)=c • totalR P := by
  rw [visible h.choose_spec,visible (P:=c•P) (n:=h.choose) (fun i hi=> by rw [Pi.smul_apply,h.choose_spec i hi,smul_zero]),Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> by rw [Pi.smul_apply,map_smul]
lemma visible_sum {I:Type*}{q: Finset I}{P:I→ Gen ℝ U}(h:∀ i∈q,FiniteGen (P i)) : totalR (∑ i∈q,P i)=∑ i∈q,totalR (P i) := by
  classical
  induction q using Finset.induction_on with
  | empty=> simp [totalR]
  | @insert i q hi ih=> simp_rw [sum_insert hi]
                        have he j hj:=h j (Finset.mem_insert_of_mem hj)
                        rw [visible_add (h i (mem_insert_self ..)) (finite_sum he),ih he]
lemma visible_sever {P:Gen ℝ U}(h:FiniteGen P)(hp:Pure P)(a:U) : totalR (sever a P)=pderiv a (totalR P) := by
  rw [visible (h.choose_spec.mono (Nat.le_succ _)),Finset.sum_range_succ',map_add,map_sum]
  rw [visible (P:=sever a P) (n:=h.choose) (fun i hi=> by rw [sever,h.choose_spec (i+1) (by omega),show prune _ _=0 from rfl,smul_zero]), shell (P 0) (fun j=>j.elim0),pderiv_C,add_zero];
  apply Finset.sum_congr rfl; intro i _; rw [peel _ (hp _),sever,map_nsmul]
private lemma rectangle {V:Type*} [AddCommMonoid V]{n t:ℕ} (F:ℕ×ℕ→V) (h:∀ j:ℕ×ℕ, n≤j.1 ∨ t≤j.2→F j=0) : ∑ i∈range (n+t),∑ j∈antidiagonal i,F j= ∑ i∈range n,∑ j∈range t,F (i,j) := by
  classical
  have hd : ((range (n+t)):Set ℕ).PairwiseDisjoint Finset.antidiagonal := fun a _ b _ hab=> Finset.disjoint_left.mpr fun j hj hj'=>hab ((mem_antidiagonal.mp hj).symm.trans (mem_antidiagonal.mp hj'))
  rw [←sum_biUnion hd,← Finset.sum_product']
  symm; refine sum_subset ?_ ?_
  · intro ⟨i,j⟩ hh; simp only [mem_product,mem_range] at hh
    exact mem_biUnion.mpr ⟨i+j,mem_range.mpr (Nat.add_lt_add hh.1 hh.2),mem_antidiagonal.mpr rfl⟩
  intro j _ hg; apply h; simp only [mem_product,mem_range,not_and_or,not_lt] at hg; exact hg
lemma paint_inter {P:Gen ℝ U}{Q:Gen ℝ U} (k:ℕ×ℕ){s}(h:k.1+k.2=s) : paint s (interweave (P k.1) (Q k.2) s)=paint _ (P k.1)*paint _ (Q k.2) := by
  subst s; rw [←palms_weld]; congr 1; funext; simp [interweave,weld]
lemma visible_spore {P Q:Gen ℝ U}(h:FiniteGen P)(e:FiniteGen Q): totalR (spore P Q) = totalR P * totalR Q := by
  have hs (k:ℕ×ℕ){r}(t:k∈antidiagonal r): paint r (interweave (P k.1) (Q k.2) r)=paint _ (P k.1)*paint _ (Q k.2):=paint_inter k (mem_antidiagonal.mp t)
  let n:=h.choose; let t:=e.choose
  have hv : still (spore P Q) (n+t):= by
    intro i hi; apply Finset.sum_eq_zero; intro j hj
    have he : j.1+j.2=i:=mem_antidiagonal.mp hj; by_cases hm:n≤j.1; rw [h.choose_spec _ hm, inter_zero_left]; rw [e.choose_spec _ (show t≤j.2 by omega), inter_zero_right]
  rw [visible hv,visible h.choose_spec,visible e.choose_spec]; simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [←rectangle (n:=n) (t:=t) (fun k=> paint _ (P k.1)*paint _ (Q k.2)) (fun i hh=> by cases hh with
    | inl h' => rw [h.choose_spec _ h',map_zero,zero_mul]
    | inr h'=> rw [e.choose_spec _ h',map_zero,mul_zero])];
  exact Finset.sum_congr rfl fun i _=> by rw [spore,map_sum]; exact Finset.sum_congr rfl fun j hj=> hs j hj
lemma visible_ripple (G:Matrix U U ℝ){P:Gen ℝ U}(h:FiniteGen P)(p:Pure P): totalR (ripple G P)= traceLap G (totalR P) := by
  let H a b := finite_μ (finite_sever a (finite_sever b h)) (G a b/2)
  unfold ripple traceLap
  rw [visible_sum (fun i _=>finite_sum fun j _=>H i j),windowLap_apply]
  apply Finset.sum_congr rfl; intro i _; rw [visible_sum (fun j _=> H i j)]; apply Finset.sum_congr rfl; intro j _
  rw [visible_μ (finite_sever _ (finite_sever _ h)),visible_sever (finite_sever _ h) (pure_sever _ p),visible_sever h p]; rfl
lemma visible_arbor (G:Matrix U U ℝ){P Q:Gen ℝ U}(h:FiniteGen P)(p:Pure P)(g:FiniteGen Q)(q:Pure Q): totalR (arbor G P Q)=
    ∑ a:U,∑ b:U,(G a b/2) • (pderiv a (totalR P)*pderiv b (totalR Q)) := by
  let H (a b:U):=squeezed _ (finite_spore (finite_sever a h) (finite_sever b g))
  let ht a b:= finite_μ (H a b) (G a b/2); rw [arbor,visible_sum (fun i _=>finite_sum fun j _=>ht i j)]; apply Finset.sum_congr rfl; intro i _; rw [visible_sum (fun j _=>ht i j)]; apply Finset.sum_congr rfl; intro j _; rw [visible_μ (H i j)]; congr 1
  rw [show totalR (fun r=>swirl (spore (sever i P) (sever j Q) r))=totalR (spore (sever i P) (sever j Q)) from ?hh, visible_spore (finite_sever i h) (finite_sever j g), visible_sever h p, visible_sever g q];
  case hh=> unfold totalR; exact finsum_congr fun j=>swirl_paint _
end real
end YM.WilsonCoeffUV.Blue
