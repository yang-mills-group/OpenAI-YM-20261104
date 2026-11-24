import YM.Frontier6.Bouquet.Anise.Page

/-!
# Evaluating tensors against rescaled bills, direction-wise or full slot
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Tensor Anise
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P:Place}[FiniteDimensional ℝ P]{n:ℕ}{r A:ℝ}{Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]
lemma tensor_charge (h:A≥0)(hr:0<r){V:T P Y n} (he:∀ x:Fin n→ P,(∀ i, ‖x i‖≤ r) → ‖V x‖≤ A): r^n * ‖V‖ ≤ A:=by
    have hz:‖V‖≤ A/r^n:=by
       refine ContinuousMultilinearMap.opNorm_le_bound (div_nonneg h (pow_pos hr n).le) (fun x=>?_)
       let q(i:Fin n):P:= (r/‖x i‖) • x i; let R(i:Fin n):=‖x i‖/r; have hh(i): x i=R i • q i:=by
           by_cases hi:x i=0; simp only [R,q,hi,smul_zero]; unfold q R; rw [smul_smul,show ‖x i‖/r*(r/‖x i‖)=1 by field_simp,one_smul] -- need hi norm≠0
       have hq(i):‖q i‖≤ r:=by
           by_cases hi:x i=0; simp only [q,hi,smul_zero,norm_zero]; exact hr.le
           apply le_of_eq; unfold q; rw [norm_smul,Real.norm_of_nonneg (div_nonneg hr.le (norm_nonneg _)),div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hi)]
       let c:=∏ i:Fin n,R i; have hp : V x=c • V q := (congr_arg V (funext hh)).trans (V.map_smul_univ ..) -- syntax?
       have hc:0≤c:= Finset.prod_nonneg (fun i _=> div_nonneg (norm_nonneg _) hr.le)
       rw [hp,norm_smul,Real.norm_of_nonneg hc]; refine (mul_le_mul_of_nonneg_left (he q hq) hc).trans_eq ?_; unfold c R; rw [Finset.prod_div_distrib,Finset.prod_const,card_univ,Fintype.card_fin]; ring
    rw [mul_comm]; exact (le_div_iff₀ (pow_pos hr _)).mp hz
lemma train_fn (f:Full P)(p:Fin n→ P): (train P (List.ofFn (fun i=>(p i).val)) f:P→ℂ)=(fun x=> iteratedFDeriv ℝ n f x p):=by
   rw [train_list]; unfold pedal; rw [List.map_ofFn]; have hp:(fun i=>ontoSpace P (p i).val)=p:=funext fun i=>on_home _; rw [show ((ontoSpace P) ∘ _)=p from hp, path_fn]
def Checks (P:Place)[FiniteDimensional ℝ P](R:Set Room)(f:Full P)(d:ℕ)(C:ℝ):Prop := ∀ v:Multiset Room, v.card≤ d→(∀ x∈v,x∈R)→∀ z,‖train P v f z‖≤C
def Accounts (P:Place) (r:ℝ): Set Room:= {x:Room|x∈ P∧‖x‖≤r}
lemma Checks.sup (f:Full P)(d:ℕ){C:ℝ}{R:Set Room}(he:Checks P R f d C) (z:P): ‖f z‖≤C:=by simpa only [trains_zero] using he 0 (by simp) (by simp) z
lemma Checks.nonneg {f:Full P}{d:ℕ}{C:ℝ}{R:Set Room}(he:Checks P R f d C): 0≤C:=(norm_nonneg (f 0)).trans (Checks.sup f d he 0)
lemma Checks.charges (f:Full P)(d:ℕ){C:ℝ}(hr:0<r)(he:Checks P (Accounts P r) f d C): Charge d r f C:=by
    intro i hi x hx;
    refine tensor_charge he.nonneg hr (fun y hy=>?_); rw [show iteratedFDeriv ℝ i (f:P→ℂ) x y= _ from (congr_fun (train_fn f y) x).symm]
    refine he _ (by simpa using hi) ?_ _; intro z hz; obtain ⟨k,rfl⟩:= List.mem_ofFn.mp (Multiset.mem_coe.mp hz); exact ⟨(y k).property,hy k⟩
lemma path_charge (f:Full P)(d:ℕ){C:ℝ}(hr:0≤r)(he:Charge d r f C) (u:List P) (h:u.length≤d)(hp:∀ i∈u,‖i‖≤r) (z:P): ‖path u f z‖≤ C:=by
    let n:=u.length; let g:(Fin n→ P):=u.get; have ht: u = List.ofFn g:=(List.ofFn_get ..).symm
    rw [ht,path_fn]; apply (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le le_rfl (hm:=fun i=>hp _ (List.get_mem ..))).trans -- rw annotations?
    simpa only [card_univ,Finset.prod_const,Fintype.card_fin,mul_comm _ (r^_)] using he _ h z (mem_univ _) -- orientation
lemma charges_path (f:Full P)(d:ℕ){C:ℝ}(hr:0≤r)(he:Charge d r f C){U:Set Room}(h:∀ x∈U,‖x‖≤r): Checks P U f d C:=by
    intro v hv hp z; let u:=(v.map (ontoSpace P)).toList
    have he' i (hi:i∈u):‖i‖≤r:=by
       obtain ⟨x,hx,rfl⟩:= Multiset.mem_map.mp (Multiset.mem_toList.mp hi); exact (on_budget (P:=P)).trans (h _ (hp _ hx))
    apply path_charge f d hr he u _ he' z; simpa only [u,Multiset.length_toList,Multiset.card_map] using hv
end YM.Frontier6.Bouquet
