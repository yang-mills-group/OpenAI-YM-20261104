import YM.XSpace.Galop
/-! # Positioned point-array costs both zeroth and first at any profile -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter PowerSeries Trace Graph3 Photo Cirrus Normalize Retirement Structure1 AxesTangent Lattice Finset
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:ℕ}(W: Initialize G)(V: Normalize.Store G)(d:ℕ)(x:Sample n)(p: Tags G d n)
lemma plate0 : cooked W V d x 0 p=live W d x 0 (visor W V x.F d ∘ p):=by rw [cooks,tally, finsuppAntidiag_zero,Finset.sum_singleton]; congr 1; ext1 i; rw [pulseU, Finsupp.zero_apply, coeff_zero_eq_constantCoeff_apply,const_deck];rfl
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4600 in
lemma scans0 : Senses (conf n) (fun i=> cooked W V d i 0 p) (fun i=> scene i d p):=by
  intro z hz
  have he(j: Fin n): Reads d (F:=Gate z) (fun i=>visor W V (grab i) d (p j)) (p j):=by have hv:= cue_cost W V d (p j); unfold Reads at *; exact hv.comp (liftG z)
  let Y (x:Sample n):= visor W V (grab x) d; have hz':= lights (F:=Gate z) d p (fun x:Sample n=> Y x ∘ p) he (fun i:Sample n=> live W d i 0) (scene z d) (fun q=> notices W d q z hz); exact hz'.congr (fun i=>(plate0 W V d i p).symm)
private def sole : Option (Fin n)→Days n := fun i=> Finsupp.single i 1
private lemma toll1 : Injective (sole (n:=n)):=by intro i j he; by_contra! h; have hh:0=(1:ℕ):= (Finsupp.single_eq_of_ne h).symm.trans (show sole (n:=n) j i=1 by rw [← he]; exact Finsupp.single_eq_same); omega
private lemma totals : tally 1 n= Finset.univ.image sole:=by
  ext1 v; rw [totaled,Finset.mem_image]; refine ⟨fun h=>?_,?_⟩; swap; · rintro ⟨i,_,rfl⟩; simp [sole]
  have he: Pages.Volume v=1:=by rw [Pages.Volume,Finsupp.weight,LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply,Finsupp.sum_of_support_subset v (Finset.subset_univ _) _ (by simp)]; simpa using h
  obtain ⟨i,rfl⟩:= Chiral.rank1_support v he; exact ⟨i,Finset.mem_univ _,rfl⟩
lemma plate1 : cooked W V d x 1 = Positioned W V d x:=by
  ext1 p; rw [cooks, Positioned, mixer]; let v:=live W d x; let T:=deck (V.layout W (grab x) d); let A(y: Days n):=v (y none) (pulseU y T p); change (∑ j∈tally 1 n,A j)=_; rw [totals,sum_image toll1.injOn,Fintype.sum_option]; have he : pulseU (sole (n:=n) none) T p = visor W V (grab x) d ∘ p:=by ext1 i; simp only [pulseU,sole,Finsupp.single_eq_of_ne (Option.some_ne_none i), T,coeff_zero_eq_constantCoeff_apply,const_deck];rfl
  rw [show A (sole none)=v 1 (visor W V (grab x) d ∘ p) from by unfold A; rw [he,sole,Finsupp.single_eq_same]]; apply congr_arg (_+·); refine Finset.sum_congr rfl fun i _=>?_ ; unfold A; rw [show sole (some i)=jumpDay n 1 i from rfl,drift,jumpDay,Finsupp.single_eq_of_ne (Option.some_ne_none _).symm]; unfold T; rw [coeff_zero_eq_constantCoeff_apply, const_deck,pos_decked _ (by decide)]
lemma scans1 : Senses (conf n) (fun i=> cooked W V d i 1 p) (fun i=> checked1 W V d i p):= by simp_rw [plate1]; exact reaches1 W V d p
end YM.XSpace.Rose
