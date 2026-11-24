import YM.OPE.Compatible.Scrape.Chai
import YM.MergeProof.Maid
import YM.Push.LOCAL_SPLITTING.Atoms
/-!
# Crop Mark: expressed primary density AT allgood on X.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Pill
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Push.Local Next.Foundations
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X:Type*}{n:Side} {i j k:ℕ}{Fr:Frame G k} (T:SectionData Fr){V:Rep G n} (o:Site n){A:Hol G}{t a b c:ℝ}
local notation "F"=> Config G n
variable {P:Coefficient Fr n}
section
variable [NormedAddCommGroup X] {f:ℕ→X}{u:ℕ→ℝ}
lemma glideW (h: Summable u){N:ℕ}(hv:∀ i,‖f i‖≤u i) (hh: Summable f):
      ‖(∑' i,f i)- ∑ i∈Finset.range N,f i‖≤ (∑' i,u i)-∑ i∈Finset.range N,u i:=by
      -- metric separated f space require t2
      have hp:= h.of_nonneg_of_le (fun i=> norm_nonneg (f i)) hv
      rw [← h.sum_add_tsum_nat_add N, ← hh.sum_add_tsum_nat_add N]; simp only [add_sub_cancel_left]; apply (norm_tsum_le_tsum_norm ?_).trans; swap; · exact (summable_nat_add_iff N).mpr hp
      exact Summable.tsum_le_tsum (fun i=>hv _) ((summable_nat_add_iff N).mpr hp) ((summable_nat_add_iff N).mpr h)
end
lemma totalsW (hp:P.Format o A V)(X:Support n)(I:Finset ℕ)(h:∀ j∈I, P.support j ⊆ X): Reads A o X (0:Label G k) (∑ i∈I, P.regular i):=by
     let f:=project A o X (d:=k) -- named args? 
     have hT (x): Reads A o X (0:Label G k) x ↔ _ := reads_null_iff A k o X x
     have he (i)(hi:i∈I): Reads A o X (0:Label G k) (P.regular i):= hT _|>.2 ⟨hp.identity_null i,fun hz=>hp.projects i (fun j hj=>hz j (h i hi hj))⟩
     induction I using Finset.induction_on with
     | empty=> rw [Finset.sum_empty]; rw [reads_null_iff]; exact ⟨rfl,fun _ _ => ⟨contDiffAt_const,fun k _ => by simp⟩⟩
     | insert i u hv ih=>
          rw [Finset.sum_insert hv]; have hu(j)(hj:j∈u):= h j (Finset.mem_insert_of_mem hj); let ai:= Finset.mem_insert_self i u; let H:= he i ai; let f:= ∑ j∈u,P.regular j
          have hg:Reads A o X (0:Label G k) f:= ih hu (fun j hj=> he _ (Finset.mem_insert_of_mem hj))
          have hz':Reads A o X (0:Label G k) (0:F→ℂ):= by rw [reads_null_iff]; exact ⟨rfl,fun _ _ => ⟨contDiffAt_const,fun k _ => by simp⟩⟩
          simpa only [sub_zero,zero_sub,sub_neg_eq_add,neg_zero] using! reads_sub H (reads_sub hz' hg)
open Finset
lemma heightsX (hp:P.Format o A V)(X:Support n)(I:Finset ℕ)(h:∀ j∈I, P.support j ⊆ X) (hb:P.remBound o V a b):let f:= ∑ i∈I,P.regular i; V.p.Regular X f ∧ V.p.supBounds o X f b:=by
      obtain ⟨c,d,hc,hd,hP,hV,⟨u,hq,hU⟩,w,hX,hW⟩:=hb
      obtain ⟨he,hK⟩:=regular_bound_sum I P.regular u (fun i hi=>⟨regular_larger (hp.smooth _) (h i hi),bound_larger (hU i) (h i hi)⟩) -- inspect
      refine ⟨he,bound_weaken hK ?_⟩; let v i:= V.p.mass (P.support i) (u i); have ht:= (Summable.sum_le_tsum I (fun i _=> hq.1 i) hq.2.1).trans hq.2.2; exact (sum_le_sum (fun j _=>V.p.loMass _ _ (hU j).1)).trans (ht.trans (le_trans (le_add_of_nonneg_right hd) hP))
abbrev clump (B:BudgetPoint)(r:ℕ):= r*(4*B.B+2)+2*B.B
def Crop (R:Rep G n)(o:Site n)(r:ℕ):Support n:= halo (clump R.p r) {o}
lemma perry {f:ℕ→ℝ}(hf: Summable f){x:ℝ}(hx:0<x):∃ N:ℕ, (∑' i,f i)-∑ i∈range N,f i≤x:=by
    have hh: Tendsto (fun i:ℕ=> (∑' i,f i)-∑ j∈range i,f j) atTop (𝓝 0):= by simpa only [sub_self] using (tendsto_const_nhds (x:= ∑' i,f i)).sub hf.hasSum.tendsto_sum_nat
    exact (hh.eventually (ge_mem_nhds hx)).exists -- edit
lemma chargesM (hp:P.Format o A V)(hb:P.remBound o V a b)(r:ℕ)(ε:ℝ)(he:0<ε): ∃ (I:Finset ℕ),(∀ i∈I,P.support i⊆Crop V o r) ∧ ∀ U:F,
 ‖(∑' i,P.maskedTerm V i U)- ∑ i∈I,P.maskedTerm V i U‖≤ ε+Real.exp (-V.p.supportExponent*r)*b:=by
      obtain ⟨c,d,hc,hd,hP,hV,⟨u,hq,hU⟩,w,hX,hW⟩:=hb; have hu: Summable u:=hq.2.1.of_nonneg_of_le (fun i=> (hU i).1) (fun i=>V.p.loMass _ _ (hU i).1); let x(i):= coverNumber V.p.B (P.support i)
      obtain ⟨N,hN⟩:= perry hu he; let J:=range N; let I:= J.filter (fun i=> x i ≤r); let H:= J\I; let y:= Real.exp (-V.p.supportExponent*r); let T (i):= V.p.mass (P.support i) (u i); have hi:I⊆J:= filter_subset _ _
      have ht (i)(hh:i∈H): u i≤ y*T i:=by
         have hx:r< x i:=Nat.lt_of_not_le (fun h=> (mem_sdiff.mp hh).2 (mem_filter.mpr ⟨(mem_sdiff.mp hh).1,h⟩)); unfold T y BudgetPoint.mass; rw [← mul_assoc, ← Real.exp_add]; refine le_mul_of_one_le_left (hU i).1 (Real.one_le_exp ?_); have hf:r ≤ x i:=hx.le
         rw [neg_mul]; linarith only [show V.p.supportExponent*r ≤ _ from mul_le_mul_of_nonneg_left (show (r:ℝ) ≤ (coverNumber V.p.B (P.support i):ℝ) from Nat.cast_le.mpr hf) V.p.exponent_pos.le]
      have hv : ∑ i∈H,u i ≤ y*b:= (sum_le_sum ht).trans (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((Summable.sum_le_tsum H (fun i _=>hq.1 i) hq.2.1).trans (hq.2.2.trans (le_trans (le_add_of_nonneg_right hd) hP))) (Real.exp_nonneg _))
      refine ⟨I,fun i heu z hz=> halo_spec.mpr ⟨o, mem_singleton_self _, (Corona.extent (P.support i) V.p.B (hp.origin i) hz).trans (by let h := (mem_filter.mp heu).2; exact add_le_add_left (Nat.mul_le_mul_right _ h) _)⟩,fun U=>?_⟩
      let f(i):= P.maskedTerm V i U
      have hz(i): ‖f i‖ ≤ u i:=by
          unfold f Coefficient.maskedTerm; by_cases hx:Healthy V.p.threshold (P.support i) U
          · rw [masked_eq _ _ _ _ hx]; exact (hU i).2 U hx [] (by simp) (by simp)
          rw [masked_ne _ _ _ _ hx,norm_zero]; exact (hU i).1
      have hH:= ((norm_sum_le ..).trans (sum_le_sum (s:=H) (fun i _=>hz i))).trans hv; have hx':(∑' i,f i)-∑ i∈I,f i=(∑' i,f i)-(∑ i∈J,f i) +∑ i∈H,f i:=by rw [← sum_sdiff hi]; abel
      change ‖(∑' i,f i)-_‖≤_; rw [hx']; exact (norm_add_le ..).trans (add_le_add ((glideW hu hz (Summable.of_norm_bounded hu hz)).trans hN) hH)
end YM.OPE.Pill
