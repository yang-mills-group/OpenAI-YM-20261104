import YM.Pert.Triangle.Feynman
import YM.Pert.Triangle.OddTest
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Wick Function Set Matrix MvPolynomial Receipt UVNext.FreeStress Next.Rank.Normal Finset Extra.FD
open scoped Classical Topology
variable {G:Gauge}

private abbrev Other := Fin 2
private abbrev Site := Fin 3
private abbrev Firsts (p : Slot G→₀ℕ) := (Σ k : p.support,Fin (p k.val))
private abbrev Marks (p : Slot G→₀ℕ) := Firsts p ⊕ (Other × Other)
private def endpoint {p : Slot G→₀ℕ} : Marks p→Site := Sum.elim (fun _=>0) (fun a=> if a.1=0 then 1 else 2)
private def grades {p : Slot G→₀ℕ} : Marks p→ℕ
  | Sum.inl k => k.1.val.1
  | Sum.inr _ => 0
private def allot (p : Slot G→₀ℕ) (U V : Probe G 0) : (j:Marks p)→Probe G (grades j)
  | Sum.inl k => coordinateLeg k.1.val
  | Sum.inr a => if a.1=0 then U else V
private def symbolChart (p : Slot G→₀ℕ) (U V : Probe G 0) (j) := symbol (grades j) (allot p U V j)
private def bracket (U : Probe G 0) := Maxwell.symbol 0 U ^ 2
set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4000 in
private lemma two_product {p : Slot G→₀ℕ} (U V : Probe G 0) :
    block endpoint grades (allot p U V) = triangle (Wick.monBasis G p) (bracket U) (bracket V) := by
  have e (a:Firsts p) : (symbol _ (allot p U V (Sum.inl a)):WickPol G) = X a.1.val := symbol_coordinate ..
  have f (i:Site) : ∏ a:Firsts p,(if endpoint (Sum.inl a)=i then symbolChart p U V (Sum.inl a) else 1) = if i=0 then monBasis G p else 1 := by
      by_cases hi : i=0
      · subst i; unfold symbolChart
        rw [if_pos rfl];simp only [endpoint,Sum.elim_inl,↓reduceIte,e,Fintype.prod_sigma]
        simp only [prod_const,card_univ,Fintype.card_fin]
        change _ = MvPolynomial.monomial p (1:ℂ)
        rw [monomial_eq,map_one,one_mul,Finsupp.prod]
        exact (Finset.prod_attach p.support (fun a=>MvPolynomial.X (R:=ℂ) a ^ (p a)))
      · exact if_neg hi ▸ (Finset.prod_eq_one (fun _ _=>if_neg (Ne.symm hi)))
  have h(i : Site) : block endpoint grades (allot p U V) i=
      (if i=0 then monBasis G p else 1) *
      (∏ a:Other, (if endpoint (Sum.inr (α:=Firsts p) (a,0))=i then symbolChart p U V (Sum.inr (a,0)) else 1)^2) := by
    unfold block; rw [prod_filter,Fintype.prod_sum_type,Fintype.prod_prod_type]
    dsimp only [symbolChart] at f
    rw [f i]
    let v (a:Other) := (if (if a=0 then 1 else 2)=i then Maxwell.symbol 0 (if a=0 then U else V) else 1)
    apply congrArg (fun k:WickPol G=> (if i=0 then monBasis G p else 1) *k)
    change (∏ a:Other,∏ _:Other,v a) = ∏ a:Other,(v a)^2
    exact prod_congr rfl (fun a _=> by rw [prod_const,card_univ,Fintype.card_fin])
  funext i
  rw [h]
  change _ * (∏ a:Other,(if (if a=0 then 1 else 2)=i then (Maxwell.symbol 0 (if a=0 then U else V)) else 1)^2) = _
  have prodTwo : ∀ f:Other→WickPol G, (∏i:Other,f i) = f 0*f 1 := fun f=> Fin.prod_univ_two _
  rw [prodTwo]
  have hz : (1:Other) ≠0:=by decide
  have h10 : (1:Site)≠0:=by decide
  have h20:(2:Site)≠0:=by decide
  have h21:(2:Site)≠1:=by decide
  fin_cases i
  all_goals simp only [Fin.zero_eta,Fin.mk_one, show (2:Site)=⟨2,by decide⟩ from rfl] at h20 h21 ⊢
  all_goals simp_all only [if_true,if_false,one_pow,eq_self,true_and, triangle_zero,triangle_one,triangle_two, ite_true, h10,h20,h21,Ne.symm h10,Ne.symm h20,Ne.symm h21, Ne.symm hz, hz,one_mul,mul_one] <;> try rfl

-- projection of a diagram to first mark
private lemma must_attach {p:Slot G→₀ℕ} {P : Equiv.Perm (Marks p)} (hcard : Fintype.card (Firsts p) ≤ 3) (hr : Trace endpoint univ P)
 : ∃ i:Marks p, endpoint i=1 ∧ endpoint (P i) =2 := by
  have he (i: Other × Other) : endpoint (Sum.inr (α:=Firsts p) i) = (1:Site) ∨ endpoint (Sum.inr (α:=Firsts p) i)=2 := by by_cases h:i.1=0 <;> simp [h,endpoint]
  by_contra! H
  have hp (a):∃ q:Firsts p,P (Sum.inr a)=Sum.inl q := by
    cases hh:P (Sum.inr a) with
    | inl k => exact ⟨k,rfl⟩
    | inr b =>
       have hx:=hr.2.1 (Sum.inr a) (mem_univ _)
       rw [hh] at hx
       obtain ha|ha := he a; obtain hb|hb:=he b
       · exact False.elim (hx (hb.trans ha.symm))
       · exact False.elim (H _ ha (hh ▸ hb))
       obtain hb|hb:=he b
       · exact False.elim (H _ hb (by rwa [show P (Sum.inr b)=Sum.inr a by rw [← hh]; exact calls _ hr _]))
       exact False.elim (hx (hb.trans ha.symm))
  choose f hf using hp
  have q:= Fintype.card_le_of_injective f (fun a b h=> Sum.inr.inj (P.injective ((hf a).trans ((congrArg _ h).trans (hf b).symm))))
  have : Fintype.card (Other × Other)=4 := by rw [Fintype.card_prod,Fintype.card_fin]
  rw [this] at q
  omega
private lemma pull_to_right {p:Slot G→₀ℕ} {u:Marks p} {P : Equiv.Perm (Marks p)} (hu:endpoint u=1) (wu:endpoint (P u)=2):
     ∃ a b, u=Sum.inr (0,a) ∧ P u = Sum.inr (1,b) := by
        obtain u|⟨a,b⟩:=u
        · change (0:Site)=1 at hu; norm_num at hu
        cases e : P (Sum.inr (α:=Firsts p) (a,b)) with
        | inl q => rw [e] at wu; change (0:Site)=2 at wu; norm_num [Fin.ext_iff] at wu
        | inr q =>
          rw [e,endpoint] at wu; unfold endpoint at hu
          dsimp only [Sum.elim_inr] at wu hu
          have ht := show q.1=0 ∨ q.1=1 from (by decide : ∀ i:Other,i=0 ∨ i=1) q.1
          exact ⟨b,q.2,congrArg Sum.inr (Prod.ext (by by_contra h'; rw [if_neg h'] at hu; norm_num [Fin.ext_iff] at hu) rfl),congrArg _ (Prod.ext (ht.resolve_left (by rintro h;rw [if_pos h] at wu; norm_num [Fin.ext_iff] at wu)) rfl)⟩
variable {x:Points 3} (hx:x∈conf 3)
private lemma graph_zero {p:Slot G→₀ℕ} (hcard:Fintype.card (Firsts p)≤3) (U V:Probe G 0) (hUV : legKernel U V (x 1-x 2)=0)
      (P : Equiv.Perm (Marks p)) (hP : Trace endpoint univ P) : ∃ u, endpoint u < endpoint (P u) ∧ legKernel (allot p U V u) (allot p U V (P u)) (x (endpoint u)-x (endpoint (P u)))=0 := by
     obtain ⟨u,hu,wu⟩ := must_attach hcard hP
     obtain ⟨a,b,heu,hew⟩:=pull_to_right hu wu
     refine ⟨u,show endpoint u < _ from by rw [hu,wu]; decide, ?_⟩
     rw [hew,heu]; change legKernel U V ((x (1:Site))-(x (ite ((1:Other)=0) 1 2)))=0
     rw [if_neg (by decide : (1:Other)≠0),hUV]
include hx
set_option maxHeartbeats 1500000 in
private lemma liftedPair {p:Slot G→₀ℕ} (hcard:Fintype.card (Firsts p)≤3) (U V:Probe G 0) (hUV : legKernel U V (x 1 - x 2)=0) :
    Wick.moment G x (block endpoint grades (allot p U V)) = 0 := killRegister endpoint grades x hx (allot p U V) (graph_zero hcard U V hUV)
omit hx in
private lemma triangle_pair (A B C:WickPol G) (x:Points 3) :
    triplet G x A B C=Wick.moment G x (triangle A B C) := rfl
lemma stringPair {p:Slot G→₀ℕ} (hcard:Fintype.card (Firsts p)≤3) (U V:Probe G 0)
    (hUV : legKernel U V (x 1 - x 2)=0) :
    triplet G x (monBasis G p) (bracket U) (bracket V) = 0 := by rw [triangle_pair (G:=G),← two_product]; exact liftedPair hx hcard U V hUV
omit hx in
private lemma cardSlots (p : Slot G→₀ℕ) (hp : Finsupp.weight costKey p ≤ 6) : Fintype.card (Firsts p) ≤ 3 := by
  have hE (i:Slot G) : 2 ≤ costKey i := by unfold costKey; omega
  suffices h : 2 * Fintype.card (Firsts p) ≤ Finsupp.weight costKey p from (by omega)
  rw [Fintype.card_sigma]; simp only [Fintype.card_fin,Finsupp.weight_apply,Finsupp.sum]
  rw [Finset.mul_sum]
  rw [show (∑i:(p.support), 2*p i.val) = ∑i∈p.support,2*p i from Finset.sum_attach p.support (fun i=> 2*p i)]
  exact (Finset.sum_le_sum fun i _=> show 2 * p i ≤ p i • costKey i from (Nat.mul_le_mul_right _ (hE i)).trans_eq (Nat.mul_comm ..))
include hx
lemma throughPair {p : WickPol G} (hp : p ∈ through G 6) (U V : Probe G 0) (hUV : legKernel U V (x 1 - x 2)=0) :
    triplet G x p (bracket U) (bracket V)=0 := by
      conv_lhs=>rw [MvPolynomial.as_sum p]
      simp_rw [map_sum,LinearMap.sum_apply]
      apply sum_eq_zero; intro j hj
      rw [show MvPolynomial.monomial j (R:=ℂ) (MvPolynomial.coeff j p)= (p.coeff j) • monBasis G j from (by rw [show monBasis G j=MvPolynomial.monomial j (1:ℂ) from rfl,smul_monomial]; simp)]
      simp only [_root_.map_smul,LinearMap.smul_apply, stringPair hx (cardSlots _ ((mem_restrictSupport_iff ℂ).mp hp hj)) U V hUV, smul_zero]
omit hx in
lemma freeMinus :
    reduceEq (uMinus G) = (2:ℂ)⁻¹ • (∑ i, ∑ u:G.ColorIndex, bracket (Triangle.probe false i u)) := by
  change reduceEq (_*_)= _
  rw [MvPolynomial.smul_eq_C_mul,_root_.map_mul,show reduceEq (C ((2:ℂ)⁻¹))=C ((2:ℂ)⁻¹) from AlgHom.commutes ..]
  congr 1
  exact by simp only [uMinus,_root_.map_sum,_root_.map_pow,bracket,reduced_fan]
lemma shift_at_outer {p:WickPol G} (hp:p∈through G 6) :
    Wick.moment G x (triangle p (reduceEq (uMinus G)) (reduceEq (uMinus G)))=0 := by
   change triplet G x p _ _=0
   rw [freeMinus]
   simp only [_root_.map_smul,LinearMap.smul_apply, smul_eq_mul]
   apply mul_eq_zero_of_right
   apply mul_eq_zero_of_right
   simp only [map_sum,LinearMap.sum_apply]
   have h' : x 1≠x 2 := fun w=> (show (1:Fin 3) ≠2 from by decide) ((hx:Injective x.ofLp) w)
   let N := triplet G x p
   let P i a := Triangle.probe (G:=G) false i a
   have hi (i j:Fin 3) (a b:G.ColorIndex): N (bracket (P i a)) (bracket (P j b))=0 :=
       throughPair hx hp (P i a) (P j b) (fan_kernel _ _ _ _ _ (sub_ne_zero.mpr h'))
   exact sum_eq_zero fun i _=>sum_eq_zero fun a _=>sum_eq_zero fun j _=>sum_eq_zero (fun b _=> hi j i b a)

end YM.Pert.Triangle
