import YM.OPE.Compatible.Eyrie.Tilt
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.Extra.SOURCE_HISTORIES.Dressing
import YM.MergeProof.Maid
/-! # Boundary norms including marked gas, arbitrary period, actual representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Eyrie
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid
open SectorNext.Vacuum Extra.Histories MergeProof MergeProof.Accent Finset
open scoped Topology Classical BigOperators
variable {G:Gauge}{n:Side}{l k:ℕ}{R:Rep G n} (U:Config G n) {P δ β σ ξ κ :ℝ}(h:R.Lawful P δ β σ ξ)
include h
lemma plumK (he:ξ ≤ 1) (i:ℕ): ‖dressed R i U‖≤1:=by
       obtain ⟨v,-,H,-⟩:= dressed_budget h; have hx:Summable fun b=> ‖coat R i b U‖:= (H i).absolute U
       apply (norm_tsum_le_tsum_norm hx).trans; refine hx.tsum_le_of_sum_le ?_; intro s; let A:=R.activities; let D:=flags R.p.threshold U; let X(j):=(A.forced j).support; let Y(j):=(A.forced j).inventory; have hy(j): (Y j).Nonempty:=(A.forced j).inventory_ne; have he'(i): Y i ⊆ X i:=(A.forced i).inventory_sup; let V:=s.filter fun j=> i∈j∧ R.activities.admissible R.p U j; obtain ⟨b,hb,hY⟩:=h.labels.boundK
       let e:=V.biUnion id; let f:=V.image fun j=>j.erase i
       have he (j:Finset ℕ)(hj:j∈V): i∈j∧ R.activities.admissible R.p U j:= (mem_filter.mp hj).2
       let F:= e.powerset.filter (accounted X Y (D \ Y i))
       have hf:f ⊆ F:= by
            rintro j hj; obtain ⟨q,hq,rfl⟩:= mem_image.mp hj; obtain ⟨ht,hT⟩:=he q hq; have hw : accounted X Y D q:=by convert hT using 1; unfold accounted X Y D A Activities.admissible; congr!
            exact mem_filter.mpr ⟨mem_powerset.mpr fun k hk=> mem_biUnion.mpr ⟨q,hq,mem_of_mem_erase hk⟩,by convert reaccounts X Y hw he' _ ht using 1; congr!; ext; simp only [mem_erase]⟩
       have hK:= cover_power (γ:=0) (w:=1) X Y he' hy le_rfl b (fun i=> (hb i).1) (fun x I=> ?_) (D\Y i) e; swap
       · simp only [zero_mul,Real.exp_zero,mul_one]; apply le_trans _ (((hY x).2.1.sum_le_tsum I (fun j _=> (hY x).1 j)).trans ((hY x).2.2.trans ‹ξ ≤ 1›)); apply sum_le_sum; intro j hh
         by_cases hz:x∈Y j
         · rw [if_pos hz,if_pos (he' j hz)]; exact BudgetPoint.loMass _ _ _ (hb j).1
         rw[if_neg hz]; exact (hY x).1 j
       simp only [neg_zero, zero_mul, ite_self,Real.exp_zero,mul_one] at hK
       rw [(show ∑ j∈s, ‖coat R i j U‖=∑ j∈V, ‖coat R i j U‖ from (sum_subset (filter_subset ..) (fun j hj ht=> by rw [coat,if_neg (mt (fun z=>mem_filter.mpr ⟨hj,z⟩) ht),norm_zero])).symm)]
       apply le_trans _ hK; refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hf (fun j _ _=> prod_nonneg fun i _=> (hb i).1)); unfold f; rw[sum_image]
       · exact sum_le_sum fun j hj=>by rw [coat, if_pos (he _ hj),norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=> (Complex.norm_real _).trans_le ((hb j).2 _))
       intro j hj k hk heq; change j.erase i=k.erase i at heq; rw [← insert_erase (he _ hj).1, ← insert_erase (he _ hk).1,heq]
variable {o:Site n}{F: Labels.Frame G k}(B:SectionData F){T:Coefficient F n}
lemma Penn (he:ξ ≤ 1){w x Ω:ℝ}(hT:T.remBound o R w x) (hw:w≤1)(hv:‖T.exponentialEntry o B R U‖ ≤ Ω): ‖T.density o B R U‖ ≤ Real.exp (R.exponent U) * (Ω+x):=by
       have hB:= rem_dominated hT; unfold Coefficient.density Rep.eval; rw[dress_eq h hB U]; refine (norm_add_le ..).trans ?_; rw [norm_mul,norm_mul, Complex.norm_real, Complex.norm_real,norm_mul,Real.norm_of_nonneg (Real.exp_pos _|>.le),mul_add]
       refine add_le_add (mul_le_mul (b:=Real.exp (R.exponent U)) ((mul_le_mul_of_nonneg_left (gas_le_one R.activities he h.labels U) (Real.exp_pos _|>.le)).trans (mul_one _).le) hv (norm_nonneg _) (Real.exp_pos _|>.le)) (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _|>.le))
       obtain ⟨a,c,hA,hC,hD,-,-,b,hb,hY⟩:= hT; refine (norm_tsum_le_tsum_norm ((dress_abs h hB).absolute U)).trans ?_; apply le_trans _ (hb.2.2.trans ((mul_le_of_le_one_left hC hw).trans (le_trans (le_add_of_nonneg_left hA) hD))); exact Summable.tsum_le_tsum (fun i=> by rw[norm_mul]; exact (mul_le_mul ((hY i).2 U) (plumK U h he _) (norm_nonneg _) (hY i).1).trans ((mul_one _).trans_le (BudgetPoint.loMass _ _ _ (hY i).1))) ((dress_abs h hB).absolute U) hb.2.1
end YM.OPE.Eyrie
