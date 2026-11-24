import YM.FVA2.Dframe.Pillar
/-! # Allocation formulas for the exact finite-regulator comparison
Assembly `Change.convertSources` vs multi convolution in Xspace realm.
No truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Dframe.Constants
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Land MS.High MS.Wind MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Puff.Mom MS.Swirl PowerSeries
open scoped Topology ContDiff BigOperators Classical
variable {U V:Type} {Q:Type*}[CommSemiring Q]{n d k:ℕ}{G:Gauge}{w: Q}
section list
variable {a: U→Type}[LinearOrder U][Fintype U][∀ i,Fintype (a i)]
variable (f:(∀ i:U,a i))
def allow (l:List U): Finset (∀ i,a i):= Finset.filter (fun g:_=> ∀ i,i∉l→g i=f i) Finset.univ
lemma at_foot : allow f []={f}:= by ext x; simp [allow, funext_iff]
lemma allowed {l:List U}(u:U) (h:u∉(l:List U)) (z:a u) (i: (∀ i,a i)): i∈allow (update f u z) l ↔ i∈allow f (u::l) ∧ i u=z:= by
    constructor
    · intro w; simp only [allow, Finset.mem_filter, Finset.mem_univ,true_and] at w ⊢; simp only [List.mem_cons,not_or] ; exact ⟨ fun i ⟨hu,h⟩=> by rw [w i h,update_of_ne hu], by rw [w u h,update_self]⟩
    rintro ⟨w,H⟩; simp only [allow,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_cons,not_or] at w ⊢; intro p hp; by_cases hv:p=u; · subst p; rw [H,update_self]
    rw [w p ⟨ hv,hp ⟩,update_of_ne hv]
lemma exists_from (L:List U) : f ∈ allow f L:= by simp [allow]
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local infixl:70 " ● " => Actors.core Trunk
lemma coherent (F H: Change.Ser) : μ ( F ● H ) = μ F * μ H:= PowerSeries.ext fun i=> by rw [coeff_mul]; simp_rw [coeff_mk]; rfl
lemma pay (F:V→ Change.Ser)(s:Finset V): μ (∑ i∈s,F i)=∑ i∈s,μ (F i):= PowerSeries.ext fun i=> by rw [map_sum,coeff_mk]; simp_rw [coeff_mk]; rw [Finset.sum_apply]
abbrev ink (i : (∀ j,a j))(j:U) : Sigma a:= ⟨j,i j⟩
lemma castUp (v: Sigma a → Change.Ser)(L:List U)(P:List (Sigma a)→Change.Ser)(h:L.Nodup): μ (Change.convertSources v L P)= ∑ x∈allow f L,(∏ i∈ L.toFinset, μ (v ⟨i,x i⟩)) * μ (P (L.map (ink x))) := by
    induction L generalizing P f with
    | nil=> rw [Change.convertSources,at_foot,Finset.sum_singleton,List.map_nil,List.toFinset_nil, Finset.prod_empty,one_mul]
    | cons i L ih=>
       obtain ⟨ht,hL⟩:= List.nodup_cons.mp h
       unfold Change.convertSources; simp_rw [ pay, coherent, fun j=> ih (update f i j) (fun us=>P (⟨i,j⟩::us)) hL ]; -- issue `j` unbound; use calc
       let S(j:a i):= allow (update f i j) L; let A:= allow f (i::L); have H: A=Finset.univ.biUnion S:= by ext x; simp only [ Finset.mem_biUnion, Finset.mem_univ,true_and, S, allowed f i ht ]; exact ⟨ fun h=> ⟨x i,h,rfl⟩,fun h=> h.elim fun w hv=> hv.1 ⟩
       have hD:Set.PairwiseDisjoint (Set.univ) S:=by intro j _ k _ h; apply Finset.disjoint_left.mpr; exact fun s H w=> h ( ( (allowed f i ht j s).mp H ).2.symm.trans ((allowed f i ht k s).mp w).2 )
       rw [ show allow f (i::L)=Finset.univ.biUnion S from H, Finset.sum_biUnion (by simpa only [Finset.coe_univ] using hD) ]; refine Finset.sum_congr rfl (fun j _=>?_); rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x hx=>?_); obtain he:= ((allowed f i ht j x).mp hx).2; rw [List.toFinset_cons,List.map_cons, Finset.prod_insert (by simpa using ht),ink,he, mul_assoc]; -- ink rewrite inside map L may defeq
-- univ Note v(tau)∀; exp.
lemma to_univ (v:Sigma a→ Change.Ser)(P:List (Sigma a)→Change.Ser) (f: (∀ i: U,a i)) : μ (Change.convertSources v Finset.univ.toList P)=∑ x:(∀ i,a i),(∏ i:U, μ (v ( ink x i ))) * μ (P (Finset.univ.toList.map (ink x))) := by
    rw [castUp f _ _ _ Finset.univ.nodup_toList]; simp [allow,ink]
end list
lemma admits (f:Fin n→ PowerSeries Q)(γ: PowerSeries Q): PowerSeries.coeff d ((∏ i,f i)*γ)=∑ i∈Normalize.tally d n,(∏ j:Fin n,PowerSeries.coeff (i (some j)) (f j))* PowerSeries.coeff (i none) γ:= by
 let H(i:Option (Fin n)):= i.elim γ f
 rw [mul_comm, show γ *(∏ i,f i)=∏ i,H i from (Fintype.prod_option H).symm, PowerSeries.coeff_prod ]; exact Finset.sum_congr rfl (fun i _=> (Fintype.prod_option _).trans (mul_comm ..))
-- scalar law
lemma actual_subst (p q:Cn) (h:Rooted q): PowerSeries.mk (substitute q (fun j=> coeff j p))= p.subst q:= PowerSeries.ext fun i=> by
    rw [coeff_mk,rules, FPS.coeff_substituted p (show constantCoeff q=0 from (coeff_zero_eq_constantCoeff_apply _).symm.trans h), ← Nat.range_succ_eq_Iic]; -- name wrong?
    exact Finset.sum_congr rfl (fun x _=> mul_comm ..)
end YM.FVA2.Dframe.Constants
