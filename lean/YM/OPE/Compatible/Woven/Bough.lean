import YM.OPE.Compatible.Woven.Briars
/-!
# Volume anchor accounting via extending marks and stamping back to anchor. Extending with anchor at 0 preserves zero Taylor moments; settling multiplies by cost over child displacements and offsets count. Equivalent trans tensor later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Tree Next.Free Bloch Exterior Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Planned.PrimaryIntegral295.Trellis
open scoped Topology BigOperators Classical
variable {r n:ℕ} {L: Side} {G:Gauge}
-- anchor displacements view full x s; pin scalar branch only one root. 
def riseZ (x: Bin (r+1)):Bin r:= lace _ fun i=> stepOut x i.succ-stepOut x 0
def wreath (r:ℕ):Cover× Bin r≃Bin (r+1) where
    toFun p:= lace _ (Fin.cons p.1 (fun i=> p.1 + stepOut p.2 i))
    invFun x := (stepOut x 0,riseZ x)
    left_inv p := by
       ext1; simp [lace,stepOut]
       unfold riseZ; apply (lace _ |>.apply_eq_iff_eq_symm_apply).2;ext1 i; unfold stepOut;simp
    right_inv x:= by
       apply (lace _|>.apply_eq_iff_eq_symm_apply).2;ext1 i; refine Fin.cases ?_ (fun j=>?_) i; simp
       unfold riseZ stepOut; simp
lemma header (x: Cover)(p:Bin r): stepOut (wreath r (x,p)) 0=x :=rfl
lemma flowPart (x: Cover)(p:Bin r)(i:Fin r): stepOut (wreath r (x,p)) i.succ=x+stepOut p i:= by unfold wreath stepOut; simp
lemma flattenZ (x:Cover)(p:Bin r): riseZ (wreath r (x,p))=p:=congr_arg Prod.snd ((wreath r).symm_apply_apply _)
lemma measureRise (x:Bin (r+1)): notch (riseZ x) ≤ (r+1) * notch x:=by
    let f(i:Fin r):= size (stepOut x i.succ); let g:= size (stepOut x 0)
    have hp: size (riseZ x) ≤ (∑ i:Fin r,f i)+r*g:=by
       rw [couple_size,show r*g= ∑ i:Fin r, (fun _=>g) i by simp]; rw [← Finset.sum_add_distrib]; apply sum_le_sum; intro i _; unfold riseZ stepOut; rw [(lace _).symm_apply_apply]; change size (stepOut x i.succ-stepOut x 0) ≤ _; rw [sub_eq_add_neg]; exact (size_add ..).trans (by rw [size_neg])
    unfold notch; rw [couple_size (r:=r+1),Fin.sum_univ_succ];change _≤ (r+1)*(1+(g+ ∑ i:Fin r,f i)); linarith only [hp, Nat.zero_le r, Nat.zero_le g, Nat.zero_le (r*(∑ i:Fin r,f i))]
lemma poiseRise (x: Bin (r+1))(m:ℕ): poise m (riseZ x) ≤ ((r+1:ℕ):ℝ)^m*poise m x:=by
   unfold poise; rw [← mul_pow,← Nat.cast_mul]; gcongr; apply measureRise
lemma plow (p:Bin r): notch (wreath r (0,p))=notch p:=by
    unfold notch; rw [couple_size (r:=r+1),couple_size (r:=r),Fin.sum_univ_succ]; simp_rw [flowPart,header]; simp [size]
variable {X:Type*}[NormedAddCommGroup X]
def upland (p:Bin r→X)(x:Bin (r+1)):= if stepOut x 0=0 then p (riseZ x) else 0
def midland (p:Bin (r+1)→ X)(x:Bin r):=∑' i: Cover,p (wreath r (i,x))
lemma upland_bill {A m}{p:Bin r→X}(h:Sack (poise m) p A): Sack (poise m) (upland p) A:=by
   let k(y:Cover):ℝ:= if y=0 then 1 else 0
   have he: Sack 1 k 1:=by
      refine ⟨fun _=>by simp, summable_of_ne_finset_zero (s:={0}) ?_, ?_⟩
      · intro i hi; change i∉({0}:Finset Cover) at hi; simp at hi; simp [k,hi]
      rw [tsum_eq_single 0]; simp [k]
      intro i hi; simp [k,hi]
   let P:= wreath r
   have hg: Sack ((poise m) ∘ P) ((upland p) ∘ P) A:=by
      let t (i:Cover)(j:Bin r):= (((poise m) ∘ P) (i,j))*‖(upland p ∘ P) (i,j)‖
      have hx(i) (j): t i j=k i * (poise m j*‖p j‖):= by
         unfold t P comp k upland; rw [header,flattenZ]
         split
         next h'=> subst i; unfold poise; rw [plow];simp
         next h'=> simp
      let g j:= poise m j*‖p j‖; let v (i:Cover× Bin r):= k i.1*g i.2
      have hh:(fun i=> ((poise m) ∘ P) i *‖(upland p ∘ P) i‖)=v:=funext fun i=> hx i.1 i.2
      unfold Sack; rw [hh]; have hz : SumBudget k 1 := by simpa [Sack,k, SumBudget, apply_ite] using he
      have ht:Summable v:= hz.2.1.mul_of_nonneg h.2.1 hz.1 h.1
      refine ⟨fun i=> mul_nonneg (hz.1 _) (h.1 _),ht,?_⟩; rw [ht.tsum_prod]; simp only [v,tsum_mul_left,tsum_mul_right]; exact (mul_le_mul hz.2.2 h.2.2 (tsum_nonneg h.1) zero_le_one).trans_eq (one_mul _)
   simpa [comp_def] using hg.adroit P.symm
lemma midland_cash {m A}{p:Bin (r+1)→X}(h:Sack (poise m) p A): Sack (fun i:Bin (r+1)=>poise m (riseZ i)) p (((r+1:ℕ):ℝ)^m*A):=by
   let c:=((r+1:ℕ):ℝ)^m; let t x:= poise m x*‖p x‖; have hc:0≤c:=pow_nonneg (Nat.cast_nonneg _) _
   have hp:SumBudget (fun x=> c*t x) (c*A):=⟨fun x=>mul_nonneg hc (h.1 _), h.2.1.mul_left _,(by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 hc)⟩
   refine Work.F08.budget_minor hp (fun i=> mul_nonneg (zero_le_one.trans (poise_one m _)) (norm_nonneg _)) (fun i=>(mul_le_mul_of_nonneg_right (poiseRise i m) (norm_nonneg (p i))).trans_eq (mul_assoc ..))
lemma midland_bill [CompleteSpace X]{m A}{p:Bin (r+1)→X}(h:Sack (poise m) p A): Sack (poise m) (midland p) (((r+1:ℕ):ℝ)^m*A):=by
    have hp := (midland_cash h).adroit (wreath r); apply Sack.draw _ (poise_one m)
    rw [show (fun i => poise m (riseZ i)) ∘ (wreath r)=(fun i=>poise m i.2) by ext1 ⟨a,i⟩; simp [comp, flattenZ]] at hp; exact hp
end YM.OPE.Flume
