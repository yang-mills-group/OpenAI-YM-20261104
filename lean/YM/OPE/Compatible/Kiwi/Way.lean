import YM.OPE.Compatible.Kiwi.Rush
/-! # Wick product estimates forest. Merge two ordered sets -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew Maxwell Maxwell.Free
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J V:Type}{ℓ:Filter V}[LinearOrder I][LinearOrder J]{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
open Finset
variable (A:J→J→ℝ) (x:J→Module.Dual ℝ X)
lemma gum_lift (v:I→J)(h:StrictMono v)(s:Finset I): fauna A x (s.image v)=fauna (fun i j=> A (v i) (v j)) (x∘v) s :=by
    induction s using Finset.strongInduction with |_ s ih
    obtain rfl|hh:=s.eq_empty_or_nonempty
    · simp only [Finset.image_empty,fanE]
    let i:= s.min' hh; have hp:= innerA hh; have he:First (v i) (s.image v):=⟨mem_image_of_mem _ hp.1, fun j hj=>by obtain ⟨t,ht,rfl⟩:= mem_image.mp hj; exact h.monotone (hp.2 _ ht)⟩; let S:= s.erase i; have hs: S ⊂ s:=erase_ssubset hp.1; rw [pier A x he,pier _ _ hp]
    have hv(j:I)(s:Finset I): (s.image v).erase (v j)=(s.erase j).image v:= (Finset.image_erase h.injective s _).symm
    rw [hv,sum_image, ih S hs]; apply congr_arg₂ (·-·); rfl
    refine sum_congr rfl fun j hj=>?_ ; rw [hv, ih _ (Finset.ssubset_of_subset_of_ssubset (erase_subset j S) hs)]
    exact fun i _ j _ hξ=>h.injective hξ
lemma gum_merge (s t:Finset J)(h:∀ i∈s,∀ j∈t,i<j)(hh:∀ i∈s,∀ j∈t,A i j=0): fauna A x (s∪t)= fauna A x s *fauna A x t:=by
     induction s using Finset.strongInduction with | _ s ih
     obtain rfl|he:=s.eq_empty_or_nonempty; simp only[Finset.empty_union,fanE,one_mul]
     let a:=s.min' he; let S:=s.erase a; have hm:= innerA he; have ht:S⊂s:=erase_ssubset hm.1; have hp: S⊆s:= erase_subset ..; have hz(i)(hi:i∈s):i∉t:=fun q=> lt_irrefl i (h i hi i q)
     have hs:First a (s∪t):=⟨mem_union_left _ hm.1,fun j hj=>(mem_union.mp hj).elim (fun w=>hm.2 _ w) (fun W=>le_of_lt (h _ hm.1 _ W))⟩
     have hD:Disjoint S t:= Finset.disjoint_left.mpr (fun {ι} _ha hv'=>hz _ (hp _ha) hv') -- implicit ?
     have hE(t' : Finset J)(hp:t'⊂s): fauna A x (t' ∪ t)= fauna A x t'*fauna A x t:= ih t' hp (fun i hi=> h i ((Finset.ssubset_iff_subset_ne.mp hp).1 hi)) (fun i hi=> hh i ((Finset.ssubset_iff_subset_ne.mp hp).1 hi))
     have hV {i:J}(hp:i∉t)(s:Finset J) : (s∪t).erase i=s.erase i∪t:=by ext j; by_cases h:j=i; subst i;simp [hp]; simp [h]
     rw [pier A x hs,pier A x hm, hV (hz _ hm.1) s, sum_union hD, sum_eq_zero (s:=t) (fun i hi=>by rw [hh _ hm.1 _ hi,zero_smul]),add_zero,hE _ ht]; rw [sub_mul, mul_assoc,sum_mul]; apply congr_arg₂ (·-·); rfl; apply sum_congr rfl; intro i hi; rw [hV (hz _ (hp hi)) S, hE _ (Finset.ssubset_of_subset_of_ssubset (erase_subset i S) ht), smul_mul_assoc]
end YM.OPE.Prairies
