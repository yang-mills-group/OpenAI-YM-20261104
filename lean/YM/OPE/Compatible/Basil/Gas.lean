import YM.OPE.Compatible.Basil.Pitcher
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Fire
/-!
# Punctured thin mark. Keep sign and partition. No approximation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Push.AbsoluteSums.Gas Ursell Trees
variable {c:Side}{ι:Type}[DecidableEq ι]
def consort (D:ι→Support c)(u v:ι→ℝ)(s:Finset ι):ℝ:=if separated (blocked D) s then ∑ i∈s,u i*∏ j∈s.erase i,v j else 0
lemma solvation (D:ι→Support c)(u v:ι→ℝ)(hu:Summable u)(hv:Summable v)(hD:∀ i,(D i).Nonempty) :
  Summable (consort D u v) ∧ HasSum (fun i=> u i * Gas.total (blocked D) (cut D (D i) v)) (∑' s, consort D u v s):=by
    classical
    let a (i:ι)(s:Finset ι):= if separated (blocked D) s ∧ i∈s then u i*∏ j∈s.erase i,v j else 0
    let b (i:ι)(s:Finset ι):=u i* Gas.value (blocked D) (cut D (D i) v) s
    have he i (s:Finset ι) (hi:i∉s) : a i (insert i s)= b i s :=by
       unfold a b Gas.value
       rw [erase_insert hi]
       split_ifs with hx hk
       · apply congr_arg (_*·); apply prod_congr rfl; intro j hj
         have hh:i≠j:= by rintro rfl;exact hi hj
         have hz:= hx.1 i (mem_insert_self ..) j (mem_insert_of_mem hj) hh
         exact (if_pos (show Disjoint (D i) (D j) from Finset.disjoint_left.mpr fun k ha hb=> hz (Or.inr ⟨k,ha,hb⟩))).symm
       · exact (hk fun l hl j hj=> hx.1 l (mem_insert_of_mem hl) j (mem_insert_of_mem hj)).elim
       · by_contra! hh; have hF:=right_ne_zero_of_mul (Ne.symm hh)
         have ha j (hj:j∈s) : Disjoint (D i) (D j):=by by_contra hN;exact hF (prod_eq_zero hj (show cut D _ _ j=0 from if_neg hN))
         apply hx; constructor
         · intro p hp j hj hg; rcases mem_insert.mp hp with h_p|h_p <;> rcases mem_insert.mp hj with h_j|h_j
           · exact (hg (h_p.trans h_j.symm)).elim
           · subst p;exact not_or_intro hg (fun ⟨_,h₁,h₂⟩ => Finset.disjoint_left.mp (ha j h_j) h₁ h₂)
           · subst j;exact not_or_intro hg (fun ⟨_,h₁,h₂⟩ => Finset.disjoint_left.mp (ha p h_p) h₂ h₁)
           · exact (show separated (blocked D) s from by assumption) p h_p j h_j hg
         exact mem_insert_self ..
       · rw [mul_zero]
    have hf i (s:Finset ι)(hi:i∈s): b i s=0:=by
       unfold b Gas.value; split
       · rw [prod_eq_zero hi (show cut _ _ _ _=0 from if_neg fun h=> (hD i).ne_empty (by simpa using h)),mul_zero]
       rw [mul_zero]
    let M (p:ι×Finset ι):= a p.1 p.2; let T (p:ι×Finset ι):= b p.1 p.2
    have h : Summable T :=by
       have hx:=summable_finsetProd_of_summable_nonneg (fun i=> norm_nonneg (v i)) hv.norm
       apply Summable.of_norm_bounded (hu.norm.mul_of_nonneg hx (fun _=> norm_nonneg _) (fun _=> Finset.prod_nonneg fun _ _=> norm_nonneg _))
       intro ⟨i,s⟩; unfold T b; dsimp only; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
       unfold Gas.value; split
       next hz=> rw [norm_prod]; exact prod_le_prod (fun i _=>norm_nonneg _) (fun j _=>by unfold cut; split;exact le_rfl; rw [norm_zero];apply norm_nonneg)
       rw [norm_zero]; exact prod_nonneg fun _ _=> norm_nonneg _
    let S:= {p:ι×Finset ι// p.fst ∈ p.snd}; let k:= {p:ι×Finset ι// p.fst∉p.snd};let R : k ≃ S:={ toFun:=fun p=> ⟨(p.val.1,insert p.val.1 p.val.2), mem_insert_self ..⟩, invFun:=fun p=> ⟨(p.val.1,p.val.2.erase p.val.1), by simp⟩,left_inv:=fun p=> by apply Subtype.ext; dsimp only; rw [erase_insert p.property],right_inv:=fun p=>by apply Subtype.ext; dsimp only; rw [insert_erase p.property] }
    have hk:HasSum (fun x:k=> T x.val) (∑' x,T x):= (Subtype.val_injective.hasSum_iff (fun i hi=> hf i.1 i.2 (by by_contra hn; exact hi ⟨⟨i,hn⟩,rfl⟩))).mpr h.hasSum
    have ht:HasSum (M∘ (fun i:S=>i.val)) (∑' x,T x):=R.hasSum_iff.mp (hk.congr_fun fun b=> (show M (R b).val=_ from he _ _ b.property))
    have hi : HasSum M (∑' x,T x):=(Subtype.val_injective.hasSum_iff (f:=M) (fun p hp=> if_neg fun h=> hp ⟨⟨p,h.2⟩,rfl⟩)).mp ht; have hM:=hi.summable
    have he'(s:Finset ι): (∑' i:ι,a i s)=consort D u v s:=by
       rw [tsum_eq_sum (s:=s) (fun i hi => if_neg fun h=> hi h.2)] -- arg name
       unfold consort; split_ifs
       next h=> exact sum_congr rfl fun j hj=> if_pos ⟨h,hj⟩
       next h=> exact Finset.sum_eq_zero fun i _=> if_neg fun H=> h H.1
    have hv:S→ℝ:=fun _=>0; clear hv
    refine ⟨(hM.prod_symm.prod.congr fun s=>he' s),?_⟩; have ht (i):u i* Gas.total (blocked D) (cut D (D i) v) = ∑' s,b i s:= (tsum_mul_left ..).symm
    simp_rw [← he',ht]; change HasSum (fun i=>∑' s,T (i,s)) _; rw [show (∑' s, ∑' i, a i s)=∑' p, M p from hM.tsum_comm.trans hM.tsum_prod.symm,hi.tsum_eq,h.tsum_prod]; exact h.prod.hasSum
end YM.PhysicalNext.Repeat.Aroma
