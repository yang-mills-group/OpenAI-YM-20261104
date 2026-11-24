import YM.OPE.Compatible.Glim.Pulp
/-! # Taylor under an oriented gauge.Ward enough. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {I J E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
abbrev Hush (v:E→ℝ)(j:ℕ):Prop:=∀ x:E,∀ k:ℕ,k<j→jet v k x=0
lemma ro_c (j:ℕ)(v:E→ℝ)(hp:ContDiffAt ℝ ω v 0)(h:Hush v j): Cape (fun (t:ℝ) x=> (t^j)⁻¹*v (t • x)) (Pawn.mold v j):=by
    obtain ⟨δ,C,hδ,hC,hq⟩:= Radial.deposition v (j+2) (hp.of_le le_top); refine ⟨tallJ j v,fun _=>le_rfl, ⟨δ,C,j+3,hδ,hC,?_⟩⟩
    intro x t ht hm; let w:= (Radial.zone (E:=E)).w x; have hw: ‖x‖ ≤ w:= by simp [w,Radial.zone]
    have hh:= hq x t ht ((mul_le_mul_of_nonneg_left hw ht.le).trans hm); simp only [quitt, JetS.atK,Pi.sub_apply]; have hz:=pow_pos ht j; rw [← mul_le_mul_iff_of_pos_left hz]; nth_rw 1 [← abs_of_pos hz, ← Real.norm_eq_abs]; rw [← norm_mul,mul_sub, ←mul_assoc,mul_inv_cancel₀ hz.ne',one_mul]
    rw [show t^j*(jet v j x+t • (jet v (j+1) x)+(t^2) • (jet v (j+2) x))=Zone.eval (jet v) (j+2) t x from ?_]; rotate_left; · unfold Zone.eval; rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ, sum_eq_zero (fun i hi=>by rw[h x i (mem_range.mp hi),smul_zero])]; simp only[smul_eq_mul];ring
    apply hh.trans; change C*‖x‖^(j+3) * _ ≤ t^j*(C*w^_* 1*t^3);rw [show t^j*(C*w^(j+3)*1*t^3)= C*w^(j+3)*t^(j+2+1) by ring]; gcongr
omit [FiniteDimensional ℝ E] in lemma QuietH (j:ℕ)(v:E→ℝ)(hp:ContDiffAt ℝ ω v 0)(h:Hush v (j+1))(z:E): Hush (bat z v) j:=by
    intro x k ht; rw [← vast v k hp, show jet v (k+1)=0 from funext fun i=> h _ _ (by omega), fderiv_zero]; rfl
abbrev Mining (p:ScriptJ E)(v:ℝ→E):=mine (p∘v)
lemma Signal (j:ℕ)(v:E→ℝ)(hp:ContDiffAt ℝ ω v 0)(h:Hush v j)(x:ℝ→E)(hx:Gael x): Reads (fun t:ℝ=> (t^j)⁻¹*v (t • x t)) (Mining (Pawn.mold v j) x):= retire continuous_one (ro_c j v hp h) hx
lemma miningAdd (p q:ScriptJ E)(v:ℝ→E)(hp:p.B)(hq:q.B)(hv:Gael v): Mining (p+q) v= Mining p v+ Mining q v:=by
     apply Gael.chooses ((Reads.cong ((Fitted.arose _ _ hv hp).take.sum ((Fitted.arose _ _ hv hq).take))) ?_); filter_upwards with i; change (p _+q _).atK i=(p _).atK i + (q _).atK i; rw [rates_add]; rfl
lemma MiningM (p q:ScriptJ E)(v:ℝ→E)(hp:p.B)(hq:q.B)(hv:Gael v): Mining (p*q) v= Mining p v* Mining q v:= Fitted.slopes (p:=p∘v) (Fitted.arose v p hv hp) (Fitted.arose v q hv hq)
lemma MiningN (p:ScriptJ E)(v:ℝ→E)(hp:p.B)(hv:Gael v): Mining (-p) v= -(Mining p v):=by
    apply Gael.chooses ((Reads.cong (Fitted.arose _ _ hv hp).take.neg) ?_); filter_upwards with i; rw [show ((-p) ∘ v) i= -(p (v i)) from rfl]; simp only [rates_neg];rfl
lemma MiningU (p:I→ScriptJ E)(S:Finset I)(f:I→ℝ→ℝ)(v:ℝ→E)(hv:Gael v)(h:∀ i∈S,ScriptJ.B (p i))(hp:∀ i∈S, Reads (f i) (Mining (p i) v)): Reads (∑ i∈S,f i) (Mining (∑ i∈S,p i) v):=by
     induction S using Finset.induction_on with
     | empty=> rw [Finset.sum_empty,Finset.sum_empty,show Mining _ v= (0:Token) from (show Mining (0:ScriptJ E) v=0 from Gael.chooses (Reads.selves 0))]; exact Reads.constants _
     | insert i S hi ih=> rw[sum_insert hi,sum_insert hi,miningAdd _ _ _ (h _ (mem_insert_self ..)) (sumBat _ _ (fun i hi=> h _ (mem_insert_of_mem hi))) hv]; exact (hp i (mem_insert_self ..)).sum (ih (fun i hi=> h _ (mem_insert_of_mem hi)) (fun i hi=>hp _ (mem_insert_of_mem hi)))
lemma PryRead (j:ℕ)(v:E→ℝ)(hp:ContDiffAt ℝ ω v 0)(h:Hush v j)(z:E)(x:ℝ→E)(hx:Gael x): Reads (fun t:ℝ=> ((t^j)⁻¹*t)*bat z v (t • x t)) (Mining (Pry z (Pawn.mold v j)) x):=by cases j with
    | zero=> rw [pry_m0 _ hp,MiningM _ _ _ (show ScriptJ.B (Un E) from Bfray _) (tallJ _ _) hx]; have he : Reads (fun x:ℝ=>x) (Mining (Un E) x):=by rw [show Mining (Un E) x= ski from Gael.chooses (Reads.selves ski)]; exact readsId
             simp only [pow_zero,inv_one,one_mul]; let F:= bat z v; exact he.pile (retire continuous_one (Pawn.calm ((picked _ hp z).of_le le_top)) hx) -- args
    | succ j=> rw [pry_mold _ _ hp]; apply (Signal j _ (picked _ hp z) (QuietH j _ hp h z) x hx).cong; filter_upwards [Tested.eventually_pos] with i (hi:0 < i); rw [pow_succ]; field_simp
end YM.OPE.Variance
