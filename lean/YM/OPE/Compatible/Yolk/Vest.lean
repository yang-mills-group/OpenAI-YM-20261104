import YM.OPE.Compatible.Yolk.Touch
/-!
# Hit budget for gluing. Includes actual footprint fidelity and reserve. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
lemma cavUn {ι:Type*}{f:ι→ℝ}{K:ℝ}(h:SumBudget f K): SumBudget (fun p:Finset ι=> if p.Nonempty then ∏ i∈p, f i else 0) (Real.exp K-1):=by
   classical
   let g p:=if (p:Finset ι).Nonempty then ∏ i∈p, f i else 0
   have he p:0≤g p:=by unfold g; split; exact Finset.prod_nonneg fun i _=>h.1 i; rfl
   refine budget_of_sum he fun s=> ?_
   let t:=s.erase ∅; change ∑ i∈s,g i≤ _
   have hh: ∑ i∈s,g i=∑ i∈t,∏ j∈i,f j:=by
      rw [show ∑ i∈s,g i=∑ i∈t,g i from ?_]; exact sum_congr rfl fun i hi=> if_pos (Finset.nonempty_iff_ne_empty.mpr (ne_of_mem_erase hi))
      exact (sum_subset (erase_subset _ _) fun i hi ht=> (eq_of_mem_of_notMem_erase hi ht).symm ▸ (show g ∅=0 from if_neg (by simp))).symm
   rw [hh]; have hp:=budget_sum (Product.set_products h) (insert ∅ t); rw [sum_insert (show ∅∉ t by simp [t]), prod_empty] at hp; linarith
variable {X Y:Support f} {k:ℕ}
def Geared (R:Rep G f) (b:ℕ→ℝ)(w:ℝ):=(∀ j,Crop R j (b j)) ∧
   ∀ x:Site f, SumBudget (fun i=>if x ∈ (R.activities.forced i).support then R.p.mass (R.activities.forced i).support (b i) else 0) w
variable {t z:ℝ}{b:ℕ→ℝ}(hb:Geared R b w) (hh:0≤t)(hp:0≤z)(ht:t≤ R.p.supportExponent)
include hb hh ht
lemma gloaming :
 SumBudget (fun i:{i:Finset ℕ // Anchor R.activities X Y i}=> Real.exp (t*coverNumber R.p.B (enrolY R.activities Y i.val)) * (∏ j∈ i.val,b j))
   (Real.exp (t*coverNumber R.p.B Y) * (Real.exp ((Y.card:ℝ)*w)-1)):=by
   let A i:=(R.activities.forced i).support
   let g i:= R.p.mass (A i) (b i); have hx i: 0≤g i:=mul_nonneg (Real.exp_pos _).le (hb.1 i).1
   let h i:=if ¬ Disjoint (A i) Y then g i else 0
   have hv: SumBudget h ((Y.card:ℝ)*w) :=by
      have he:= budget_over Y _ (fun _=>w) (fun i (_:i∈Y)=>hb.2 i)
      rw [sum_const,nsmul_eq_mul] at he
      refine budget_mono he (fun i=>by unfold h; split; exact hx i;rfl) (fun i=>?_)
      unfold h; split
      next hz=> obtain ⟨p,hp,hs⟩:=Finset.not_disjoint_iff.mp hz; apply le_trans _ (single_le_sum (f:=fun j: Site f=>if j∈ A i then g i else (0:ℝ)) (fun j _=> (hb.2 j).1 i) hs); rw [if_pos hp]
      exact he.1 i
   let e Y:=Real.exp (t*coverNumber R.p.B (Y:Support f)); let Φ:ℕ→ℝ:=e ∘ A
   refine budget_mono (budget_scale (Real.exp_pos _).le (budget_pull (fun p:{b// Anchor R.activities X Y b}=> p.val) Subtype.val_injective (cavUn hv))) (fun i=>mul_nonneg (Real.exp_pos _).le (prod_nonneg fun j _=> (hb.1 j).1)) fun i=> ?_
   have hK j (hj:j∈i.val):∃ z, z∈A j∧z∈Y:= Finset.not_disjoint_iff.mp ((mem_filter.mp (i.property.2.symm ▸ hj: j∈towY R.activities Y i.val)).2)
   have hm (l:Finset ℕ)(hl:l⊆ i.val): e (Y ∪ l.biUnion A) ≤ e Y*∏ j∈l,e (A j):=by
      induction l using Finset.induction_on with
      | empty=>simp
      | insert j l hj ih=>
        have hd:=ih ((Finset.subset_insert ..).trans hl); obtain ⟨z,hv,hz⟩:= hK j (hl (mem_insert_self ..))
        have hc: e (A j∪ (Y ∪ l.biUnion A))≤e (A j)*e (Y ∪ l.biUnion A):=by
           unfold e; rw [← Real.exp_add, ← mul_add,Real.exp_le_exp]; refine mul_le_mul_of_nonneg_left ?_ hh; exact_mod_cast meets_sum hv (mem_union_left (l.biUnion A) hz) R.p.B
        rw [biUnion_insert,union_left_comm,prod_insert hj,mul_left_comm]
        exact hc.trans (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)
   have hi : i.val.Nonempty:=i.property.1.mono (filter_subset ..)
   rw [if_pos hi]
   refine (mul_le_mul_of_nonneg_right (hm i.val le_rfl) (prod_nonneg (fun j (_:j∈i.val)=> (show 0≤b j from (hb.1 j).1)))).trans ?_
   rw [mul_assoc (e Y),← Finset.prod_mul_distrib]
   refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=>mul_nonneg (Real.exp_pos _).le (hb.1 _).1) fun j hj=> ?_) (Real.exp_pos _).le
   unfold h; rw [if_pos (Finset.not_disjoint_iff.mpr (hK j hj))]; unfold g; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (hb.1 _).1
end YM.PhysicalNext.Repeat.Aroma
