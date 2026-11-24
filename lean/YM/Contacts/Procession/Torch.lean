import YM.Contacts.Procession.Tin
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Pulse Pulse.Form Finset Sun
open Milling Milling.Forge Milling.Garf Matrix MvPolynomial
open scoped Topology BigOperators Classical Matrix ContDiff
variable {T α β γ : Type}[AddCommGroup T]{B k i j v p r e:ℕ}
lemma core_focus_zero (x:Boys i (T×α)): focus 0 x=Fin.cons (0,none) (core T α ∘ x):= by unfold focus; simp_rw [Function.comp_def, adder,add_zero]
lemma poem_scoop {F:Pulse.Field (Fin (i+1)) (Live T α)}(h:Poem F): Poem (scoop F):= by
   intro p x; simp only [scoop,core_focus_zero, Pi.smul_apply]; let e:= notch (0,none) F; exact congr_arg ((i+1:ℕ)•·) (h.notched (0,none) p (core _ _ ∘ x))
variable [Fintype T][Fintype α][Fintype β]
private lemma erase_sum {X Y:Type}[Fintype X][Fintype Y] (p:X ↪ Y)(f:Y→ℝ)(h:∀ i,i∉ Set.range p → f i=0): ∑' i,f i=∑' i,f (p i):= Eq.symm (p.injective.tsum_eq (fun i hi=> by by_contra he; exact hi (h _ he)))
lemma nightQ {F:Pulse.Field (Fin (i+1)) (Live T α)} (x:T×α→ℝ)(h:Poem F): aeval (star 0 x) (pderiv (0,none) (verse F)) = House.design (scoop F) x:= by
   let I:=Live T α; let J:=core T α
   let f(y:Fin i→I):= notch (n:=i) (0,none) F y* ∏ j,star 0 x (y j); let p:(Fin i→T×α) ↪ (Fin i→I):= ⟨(J ∘ ·),fun _ _ h=>funext fun i=> J.injective (congr_fun h i)⟩; letI:DecidableEq (Fin i):=fun _ _=> Classical.propDecidable _
   rw [verse_pderiv h,map_nsmul]; change _ • (House.design _ (star 0 x))= _; rw [House.design_spec,House.design_spec, ← tsum_fintype (L:=.unconditional _),←tsum_fintype (L:=.unconditional _)]; rw [erase_sum p f (fun k hk=>?_ )]; rotate_left
   · suffices h':∃ j,(k j).2=none by
       obtain ⟨j,xj⟩:= h'; unfold f; rw [prod_eq_zero (mem_univ j),mul_zero]; obtain ⟨a,ha⟩ : ∃ a,k j=(a,none):=⟨(k j).1,Prod.ext rfl xj⟩; simp [ha]
     by_contra! he; choose w hw using fun i=>Option.ne_none_iff_exists'.mp (he i); exact hk ⟨fun i=>((k i).1,w i),funext fun i=> Prod.ext rfl ((hw _).symm)⟩
   rw [nsmul_eq_mul,← tsum_mul_left]; apply tsum_congr; intro v; simp_rw [scoop,core_focus_zero,Pi.smul_apply,nsmul_eq_mul]; exact (mul_assoc ..).symm -- maybe w arg simp
lemma slopeP (P:Plate (Live T α))(x:T×α→ℝ) : HasDerivAt (fun a:ℝ=> aeval (star a x) P) (aeval (star 0 x) (pderiv (0,none) P)) 0:= by
   induction P using MvPolynomial.induction_on with
   | C c=> simpa using (hasDerivAt_const (0:ℝ) c)
   | add p q h hh=> simp_rw [map_add]; exact h.add hh
   | mul_X q i ih=>
      have he : HasDerivAt (fun a:ℝ=> aeval (star a x) (MvPolynomial.X i :Plate (Live T α))) (aeval (star 0 x) (pderiv (0, none) (MvPolynomial.X i :Plate (Live T α)))) 0 := by
        simp_rw [aeval_X,pderiv_X]; rcases i with ⟨i,_|y⟩
        · by_cases h:i=0
          · subst i; simpa using (hasDerivAt_id' (0:ℝ))
          simp [Pi.single_apply, h,eq_comm]; exact hasDerivAt_const ..
        simp only [Pi.single_apply,Prod.mk.injEq, reduceCtorEq,and_false, ↓reduceIte, map_zero]; exact hasDerivAt_const ..
      simp_rw [Derivation.leibniz, smul_eq_mul,map_add,map_mul]; have ht:=ih.mul he; exact ht.congr_deriv (by ring)
lemma designPower (f:Pulse.Field (Fin k) α)(x y): House.design f (y • x)= (y:ℝ)^k*House.design f x:= by simp only [House.design_spec,Pi.smul_apply,smul_eq_mul, Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin,mul_sum]; exact sum_congr rfl fun i _=> mul_left_comm ..
open PertExtension.Series Radial Ion
lemma design_eq {F H: Pulse.Field (Fin k) α}(h:Poem F)(hh:Poem H)(he: House.design F=House.design H): F=H:= by
    let f:= House.design F; have hq : AnalyticAt ℝ f 0:= House.design_ana ..; have hv(x):jet f k x=House.design F x:= (radiant hq k k (designPower F) x).trans (if_pos rfl); have ht:= Lumen.recital_exact f H hh hq (he ▸ hv); rw [Lumen.recital_exact f F h hq hv] at ht; -- private Lumen.recital, ext and delta
    funext y; let w i:α→ℝ:=Pi.single (y i) 1; change _ = _; have hz:= DFunLike.congr_fun ht w; change YM.Stationary.recording F w=YM.Stationary.recording H w at hz
    have ht(R:Pulse.Field (Fin k) α): YM.Stationary.recording R w= R y:= by
       rw [YM.Stationary.recording_apply, sum_eq_single y]; · simp [w]
       · intro i hi hh; obtain ⟨j,hj⟩:= Function.ne_iff.mp hh; rw [prod_eq_zero (mem_univ j) (Pi.single_eq_of_ne hj _),zero_mul]
       simp
    rwa [ht,ht] at hz
end YM.Contacts.Procession.Xenon
