import YM.Trace.Fock.Expansion
noncomputable section
set_option autoImplicit false
namespace YM.Trace.Shell
open Boundary YM Function Filter Set Complex MeasureTheory
open scoped Topology BigOperators InnerProductSpace Pointwise
variable {U : Type*} [AddCommGroup U] [Module ℂ U]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "pole" => MultilinearMap ℂ (fun _ : ι=> U) ℂ
private def sign (b : Fin 2) : ℝ := if b=(0:Fin 2) then -1 else 1
private def z (v : ι→ U) (s : ι→Fin 2) : U := ∑ i : ι, (sign (s i):ℂ) • v i
private lemma nontrap (k : ι → ι) (e : Equiv.Perm ι) (hE : ∀ a, e a=k a) : let L (s : ι→ Fin 2) := ∏ i : ι, sign (s i);
      let Lk (s : ι→ Fin 2) := ∏ i : ι, sign (s (k i));
      (∑ s : ι → Fin 2, (L s * Lk s : ℂ))= 2^(Fintype.card ι) := by
   intro L Lk
   have h (s : ι → Fin 2) := calc Lk s = ∏ i, sign (s (e i)) := by simp_rw [hE]; rfl
                                  _ = L s := Equiv.prod_comp e (fun i => sign (s i))
   rw [show (fun s : ι→Fin 2=> (L s:ℂ)*Lk s) = fun s=> 1 from funext ?eq]
   rotate_left  
   · intro s
     rw [h s]; unfold L; rw [← ofReal_mul, ← Finset.prod_mul_distrib]
     convert congr_arg Complex.ofReal (Finset.prod_eq_one (fun i (_:i∈Finset.univ)=> ?_)) using 1 <;> simp [sign]
     split_ifs <;> norm_num
   simp

private lemma odd_sign (s : ι→Fin 2) (i : ι) : let q j := if j=i then Equiv.swap (0:Fin 2) 1 else Equiv.refl _;
       let e := Equiv.piCongrRight q
       let L (s : ι→ Fin 2) := ∏ i : ι, sign (s i)
       L (e s) = - L s := by
   classical
   intro q e L
   unfold L
   have h (u : Fin 2): sign ((Equiv.swap 0 1) u) = -sign u := by fin_cases u <;> simp [sign]
   have he (j : ι) : sign (Equiv.piCongrRight q s j)=update (fun i => sign (s i)) i (-(sign (s i))) j := by
      rw [Equiv.piCongrRight_apply]; dsimp only [Pi.map_apply]; by_cases hj : j=i
      · simp [hj,q,h]
      simp [q,hj]
   simp_rw [show ∀ j, sign (e s j)= _ from he]
   calc _ = -(sign (s i)) * ∏ x ∈ Finset.univ \ {i}, sign (s x) := Finset.prod_update_of_mem  (Finset.mem_univ _) _ _
        _ = -(sign (s i) * ∏ x ∈ Finset.univ \ {i}, sign (s x)) := by rw [neg_mul]
        _ = _ := by rw [← Finset.prod_update_of_mem (Finset.mem_univ i)]; simp
private lemma trap (k : ι → ι) (hk : ¬Function.Surjective k) : let L (s : ι→ Fin 2) := ∏ i : ι, sign (s i)
      let Lk (s : ι→ Fin 2) := ∏ i : ι, sign (s (k i));
      (∑ s : ι→Fin 2, ((L s * Lk s):ℂ)) = 0 := by
   obtain ⟨i,hi⟩ := not_forall.mp hk
   intro L Lk
   let q j := if j=i then Equiv.swap (0:Fin 2) 1 else Equiv.refl _
   let e := Equiv.piCongrRight q
   have hv (s : ι→ Fin 2) : Lk (e s) = Lk s := Finset.prod_congr rfl fun j _ => by simp_all only [e,q,Equiv.piCongrRight_apply,Pi.map_apply]; have hj (a : ι) (ha : k a=i) := hi ⟨a,ha⟩; rw [if_neg (hj _ ),Equiv.refl_apply]
   have hh (s) := odd_sign s i
   have h := e.sum_comp (fun r => ((L r*Lk r):ℂ))

   simp only [show ∀ s, L (e s)=-(L s) from hh,hv,ofReal_neg,neg_mul, Finset.sum_neg_distrib] at h
   linear_combination -(h)/2

lemma polar_diagonal (F : pole) (v : ι→ U) : let L (s : ι → Fin 2) := ∏ j : ι, sign (s j)
  ∑ s : ι→ Fin 2, (L s:ℂ) * F (fun _ => z v s) = 2^(Fintype.card ι) * (∑ e : Equiv.Perm ι, F (v ∘ ⇑e)) := by
   intro L
   let Lk (k : ι → ι) (s : ι → Fin 2) := ∏ i : ι, sign (s (k i))
   classical
   simp only [z,F.map_sum,Finset.mul_sum]
   rw [Finset.sum_comm]
   have he (k : ι→ι) : (∑ s : ι → Fin 2, ((L s:ℂ)*(Lk k s))) = (if Function.Surjective k then (2:ℂ)^Fintype.card ι else 0) := by
     split_ifs with h
     · exact nontrap k (Equiv.ofBijective k h.bijective_of_finite) fun _=>rfl
     exact trap k h
   let Q (k : ι→ι) := F (v ∘ k)
   change (∑ k, ∑ i, ↑(L i) * F (fun j => (sign (i (k j)):ℂ) • (v ∘ k) j) ) = _
   simp_rw [F.map_smul_univ] -- under binders
   have hl k : ∀ s : ι→ Fin 2, (∏ i, (sign (s (k i)):ℂ)) = ↑(Lk k s) := fun s => Complex.ofReal_prod ..|>.symm
   simp_rw [hl,smul_eq_mul,← mul_assoc, ← Finset.sum_mul, he]
   let W : Equiv.Perm ι ≃ {k : ι→ι // Function.Surjective k} := {
     toFun e := ⟨e,e.surjective⟩
     invFun k := Equiv.ofBijective k.val k.2.bijective_of_finite
     left_inv _ := Equiv.ext (fun x=> rfl)
     right_inv _ := Subtype.ext (funext (fun x=> rfl)) }
   have hs k : (if Function.Surjective k then (2:ℂ)^Fintype.card ι else 0) * Q k = (2:ℂ)^Fintype.card ι * if Function.Surjective k then Q k else 0 := by
       split_ifs <;> simp
   change (∑ k, _ * Q k) = _
   simp_rw [hs,← Finset.mul_sum]; congr 1
   have hw := W.sum_comp (fun r=> Q r.val)
   have hh (k : Equiv.Perm ι) : Q (W k).val=F (v ∘ ⇑k) := rfl
   rw [Finset.sum_ite]; simp only [Finset.sum_const_zero,add_zero]
   simp only [hh] at hw; rw [← Finset.sum_subtype (_: Finset (ι→ι)) (by simp : ∀ x, x∈Finset.univ.filter (fun (j:ι→ι) => Function.Surjective j) ↔ Function.Surjective x)] at hw; exact hw.symm


lemma polar_vanish (F : pole) (v : ι → U) (hl : ∀ (e : Equiv.Perm ι), F (v ∘ ⇑e)=F v)
    (hd : ∀ r : ι → ℝ, F (fun _ => ∑ i : ι, (r i:ℂ) • v i)=0) : F v=0 := by
   suffices h : (2:ℂ)^(Fintype.card ι) * Fintype.card (Equiv.Perm ι) * F v=0 by
       exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero _ two_ne_zero) (by exact_mod_cast Fintype.card_ne_zero))
   rw [mul_assoc]; rw [← nsmul_eq_mul]; rw [← show ((Finset.univ: Finset (Equiv.Perm ι)).card:(ℕ)) = Fintype.card (Equiv.Perm ι) from rfl, ← Finset.sum_const, show (∑ (_:Equiv.Perm ι), F v)= _ from Finset.sum_congr rfl (fun i _=>hl i|>.symm), ← polar_diagonal F v]
   simp only [z,hd]; exact Finset.sum_eq_zero (fun _ _ => mul_zero _)

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {n m : ℕ}
lemma jet_add (p : Mom) (x y : SlotField m) : jet p (x+y)=jet p x+jet p y := by
   ext1 i; unfold jet; simp [map_add,smul_add,Finset.sum_add_distrib,add_apply]

abbrev Mixed := (Fin n → SlotField m)
noncomputable def productMany (v : Mixed (n:=n) (m:=m)) (x : Cords n) := rawTensor (fun i=>jet (x i) (v i))
@[fun_prop] lemma many_measurable (h : Mixed (n:=n) (m:=m)) : Measurable (productMany h) := by
   unfold productMany rawTensor; refine (PiLp.continuous_toLp 2 (fun _: (Fin n→Mode m) => ℂ)).measurable.comp (f:=fun (p : Cords n) (I : Fin n→Mode m) => ∏ i, jet (p i) (h i) (I i))
       (measurable_pi_iff.mpr (fun i => by fun_prop))
lemma many_memLp (h : Mixed) : MemLp (productMany (n:=n) (m:=m) h) 2 (νpow n) := by
   refine (memLp_two_iff_integrable_sq_norm (many_measurable ..|>.aestronglyMeasurable)).2 ?_
   unfold productMany; simp_rw [tensor_sq]
   apply Integrable.fintype_prod (f:=fun i p=> ‖jet p (h i)‖^2)
   intro i
   exact jet_sq (h i)
private lemma productI (x : Cords n) (v : Mixed) (J : Fin n→Mode m) (i : Fin n) (a : SlotField m)
     (d : DecidableEq (Fin n)): productMany (@Function.update (Fin n) _ d v i a) x J = jet (x i) a (J i) *
       ∏ j ∈ (Finset.univ:Finset (Fin n)) \ {i}, jet (x j) (v j) (J j) := by
    change (∏ j, jet (x j) (@Function.update (Fin n) _ d v i a j) (J j))=_
    rw [show (fun j=> jet (x j) (@Function.update (Fin n) _ d v i a j) (J j))= (@Function.update _ (fun _:Fin n => ℂ) (instDecidableEqFin _) (fun j => jet (x j) (v j) (J j)) i (jet (x i) a (J i))) from by
       funext j; by_cases h : j=i; simp [h]; simp [Function.update,h]]
    suffices d = instDecidableEqFin _ by
       subst d
       exact Finset.prod_update_of_mem (s:=Finset.univ) (i:=i) (Finset.mem_univ i) (fun j => jet (x j) (v j) (J j)) _
    exact Subsingleton.elim _ _ --
private lemma many_add  (x : @Mixed n m) (i : Fin n) (f g : SlotField m) p (d : DecidableEq (Fin n)): productMany (@update (Fin n) _ d x i (f+g)) p =
      productMany (@update (Fin n) _ d x i f) p + productMany (@update (Fin n) _ d x i g) p := by
       apply PiLp.ext; intro J
       simp only [PiLp.add_apply, productI p x J,jet_add,add_mul]
private lemma many_scale  (x : @Mixed n m) (i : Fin n) (f : SlotField m) (c : ℂ) p (d : DecidableEq (Fin n)): productMany (@update (Fin n) _ d x i (c • f)) p = c • productMany (@update (Fin n) _ d x i f) p := by
       apply PiLp.ext; intro J
       simp only [PiLp.smul_apply, productI p x J,jet_scale,smul_eq_mul,mul_assoc]
private noncomputable def sector (x : @Mixed n m) : Wave m n := MemLp.toLp (μ:=νpow n) _ (many_memLp x)
private lemma sector_eq (x : @Mixed n m) : (⇑(sector x) : Cords n→Fiber m n) =ᵐ[νpow n] productMany x := (many_memLp _).coeFn_toLp
private lemma sector_add  (x : @Mixed n m) (i : Fin n) (f g : SlotField m) : sector (update x i (f+g)) = sector (update x i f) + sector (update x i g) := by
  refine Lp.ext (p:=2) (μ:=νpow n) (E:=Fiber m n) (α:=Cords n) ?_
  filter_upwards [sector_eq (update x i (f+g)), Lp.coeFn_add (p:=2) (μ:=νpow n) (E:=Fiber m n) (α:=Cords n) (f:= ((sector (update x i f)))) ((sector (update x i g))),
   sector_eq (update x i f), sector_eq (update x i g)] with p hp hK hu hv
  rw [hp,hK,Pi.add_apply,hu,hv]
  exact many_add x i f g p _
private lemma sector_scale  (x : @Mixed n m) (i : Fin n) (f : SlotField m) (c:ℂ) : sector (update x i (c • f)) = c • sector (update x i f) := by
  refine Lp.ext (p:=2) (μ:=νpow n) (E:=Fiber m n) (α:=Cords n) ?_
  filter_upwards [sector_eq (update x i (c • f)),Lp.coeFn_smul (p:=2) (μ:=νpow n) (E:=Fiber m n) (α:=Cords n) c ((sector (update x i f))),
     sector_eq (update x i f)] with p hp hK hu
  rw [hp,hK,Pi.smul_apply,hu]; exact many_scale x i f c p _
noncomputable def several (n m) : MultilinearMap ℂ (fun _:Fin n=> SlotField m) (Wave m n) where
     toFun := sector
     map_update_add' {_d} x i f g := by have H : _d=instDecidableEqFin _ := Subsingleton.elim _ _; subst _d; exact sector_add x i f g
     map_update_smul' {_d} x i c f := by have H : _d=instDecidableEqFin _ := Subsingleton.elim _ _; subst _d; exact sector_scale x i f c
lemma several_coe_eq (v : @Mixed n m) : (↑↑(several n m v):Cords n→Fiber m n) =ᵐ[νpow n] productMany v := by exact sector_eq v
lemma several_diag (h : SlotField m) : several n m (fun _=> h)= slot h n := Lp.ext (p:=2) (μ:=νpow n) (E:=Fiber m n) (α:=Cords n) (by change (⇑(several n m _):Cords n→_) =ᵐ[νpow n] (⇑(slot h n):Cords n→_); exact (several_coe_eq ..).trans (evaluate_slot h|>.symm))

noncomputable def barSlots (v : @Mixed n m) : Mixed (m:=m) (n:=n) := fun i j => Probe.bar (v i j)
noncomputable def pairLeft (b : Wave m n) : MultilinearMap ℂ (fun _:Fin n=>SlotField m) ℂ where
   toFun x := inner ℂ (several n m (barSlots x)) b
   map_update_add' {_d} x i a c := by
      have HE : _d= instDecidableEqFin _ := Subsingleton.elim _ _; subst _d
      let hb (v : SlotField m) : SlotField m := fun j=> Probe.bar (v j)
      have he (u : SlotField m) : barSlots (update x i u) = update (barSlots x) i (hb u) := by
         funext k j; by_cases h : k=i
         · simp only [h,update_self,barSlots,hb]
         simp [barSlots,hb,h]
      have hS := fun (u : SlotField m) => he u
      rw [hS,hS,hS, ← inner_add_left,← (several n m).map_update_add,show hb (a+c)=hb a+hb c from by
         ext1 j; simp [hb,map_add]] -- rw repeats maybe
   map_update_smul' {_d} x i r u := by
      have HE : _d= instDecidableEqFin _ := Subsingleton.elim _ _; subst _d
      let hb (v : SlotField m) : SlotField m := fun j=> Probe.bar (v j)
      have he (u : SlotField _) : barSlots (update x i u) = update (barSlots x) i (hb u) := by
         funext k j; by_cases h : k=i
         · simp only [h,update_self,barSlots,hb]
         simp [barSlots,hb,h]
      rw [he,he,show hb (r • u) = star r • hb u from by
           ext j p; dsimp only [hb,Pi.smul_apply]; simp [Probe.bar_at,smul_apply,star_mul'],
          (several n m).map_update_smul,inner_smul_left,starRingEnd_apply,star_star,smul_eq_mul]
noncomputable def pairRight (b : Wave m n) : MultilinearMap ℂ (fun _:Fin n=>SlotField m) ℂ where
   toFun x := inner ℂ b (several n m x)
   map_update_add' {_d} x i a c := by
      have HE : _d= instDecidableEqFin _ := Subsingleton.elim _ _; subst _d
      rw [(several n m).map_update_add,inner_add_right]
   map_update_smul' {_d} x i r a := by
      have HE : _d= instDecidableEqFin _ := Subsingleton.elim _ _; subst _d
      rw [(several n m).map_update_smul,inner_smul_right,smul_eq_mul]
end YM.Trace.Shell
