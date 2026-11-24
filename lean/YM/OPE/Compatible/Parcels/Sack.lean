import YM.Work.F08.Width
/-!
# Book for virtual kernels. All terms under same precise exponent, for ANY ranks below fixed budgets. Doesn't demand constructed representatives on physical lattice already satisfy tr-pred. Unbundled functions: use exact carrier estimates; real for interaction polynomials preferred but library on X. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG
open scoped Topology Classical BigOperators
variable {I J K:Type*}
variable {X:Type*}[NormedAddCommGroup X]{Y:Type*}[NormedAddCommGroup Y]
-- sack v(i) charges cover/stencil weights. Use explicit tolls, not norm to avoid inf cost above penalties.
def Sack (u:I→ℝ) (x:I→X)(A:ℝ):Prop := SumBudget (fun i=>u i*‖x i‖) A
namespace Sack
variable {p q:I→X} {A B t:ℝ} {u v:I→ℝ}
lemma coins (h:Sack u p A):0 ≤ A:=(tsum_nonneg h.1).trans h.2.2
lemma single (h:Sack u p A)(i:I) : u i*‖p i‖≤ A:= (h.2.1.le_tsum _ (fun _ _=>h.1 _)).trans h.2.2
lemma minor (h:Sack u p A) (hu:0 ≤ v)(hp:v ≤ u)(hv:A≤ B):Sack v p B:=by
    have he := Work.F08.budget_minor (f:=fun i=> v i*‖p i‖) h (fun i=>mul_nonneg (hu i) (norm_nonneg _)) (fun i=>mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _))
    exact ⟨he.1,he.2.1,he.2.2.trans hv⟩
lemma tips (h:Sack u p A)(hv:A≤ B):Sack u p B:=⟨h.1,h.2.1,h.2.2.trans hv⟩
lemma slim {f:I→Y}(h:Sack u p A)(hx:0≤u)(hf:∀ i,‖f i‖≤‖p i‖): Sack u f A:= Work.F08.budget_minor h (fun i=> mul_nonneg (hx i) (norm_nonneg _)) (fun i=> mul_le_mul_of_nonneg_left (hf i) (hx i))
lemma splits (h:Sack u p A)(hx:Sack u q B)(hu:0 ≤ u) : Sack u (p+q) (A+B):=by
    let g i:= u i *‖p i‖; let f i:= u i * ‖q i‖
    have he : SumBudget (g+f) (A+B):=by refine ⟨fun i=> add_nonneg (h.1 i) (hx.1 i),h.2.1.add hx.2.1,h.2.1.tsum_add hx.2.1 |>.trans_le (add_le_add h.2.2 hx.2.2)⟩
    apply Work.F08.budget_minor he (fun i=>mul_nonneg (hu i) (norm_nonneg _)); intro i; change u i*‖p i+q i‖ ≤ _ + _; exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (hu i)).trans_eq (mul_add ..)
lemma scale_line [NormedSpace ℝ X](h:Sack u p A)(x:ℝ): Sack u (x • p) (‖x‖*A):=by
    let g i:= u i * ‖p i‖
    unfold Sack; rw [show (fun i=> u i*‖(x • p) i‖)=(fun i=> ‖x‖*g i) from funext fun i=>by rw [Pi.smul_apply,norm_smul];unfold g;ring]
    refine ⟨fun i=> mul_nonneg (norm_nonneg _) (h.1 i), h.2.1.mul_left _,?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (norm_nonneg _)
lemma zero (h:0≤A) (u:I→ℝ): Sack u (0:I→X) A:=by simp [Sack,SumBudget,h]
lemma subsumes (h:Sack u p A)(hx:Sack u q B) (hi:0 ≤ u): Sack u (p-q) (A+B):=by
   have he:= h.splits (p:=p) (q:=-q) (by simpa only [Sack,Pi.neg_apply,norm_neg] using hx) hi; rwa [sub_eq_add_neg]
omit [NormedAddCommGroup Y] in -- optional
lemma finGather {T:Type*} (i:Finset T) (v:T→ I→X)(B:T→ℝ) (h:∀ t∈i,Sack u (v t) (B t))(hu:0≤u): Sack u (∑ t∈i,v t) (∑ t∈i,B t):=by
   classical
   induction i using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact zero le_rfl _
   | insert k i hk ih=> rw [Finset.sum_insert hk,Finset.sum_insert hk]; exact (h _ (Finset.mem_insert_self ..)).splits (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj)) hu
lemma mass (h:Sack u p A)(hu:1 ≤ u): SumBudget (fun i=> ‖p i‖) A:= Work.F08.budget_minor h (fun _=>norm_nonneg _) (fun i=> le_mul_of_one_le_left (norm_nonneg _) (hu i))
lemma water [CompleteSpace X] (h:Sack u p A)(hu:1≤u): Summable p:= (h.mass hu).2.1.of_norm
lemma adroit (h:Sack u p A)(e:J ≃ I):Sack (u ∘ e) (p ∘ e) A:=by
   let f i:=u i*‖p i‖; exact ⟨fun j=>h.1 (e j), e.summable_iff.mpr h.2.1, (Equiv.tsum_eq e f).trans_le h.2.2⟩
lemma multiplex {f:J→Y}{g:I×J→ℝ}{v:J→ℝ}{z:I×J→X} (hz:Sack u p A) (hg:Sack v f B)(h:∀ x,g x*‖z x‖ ≤ (u x.1*‖p x.1‖) * (v x.2*‖f x.2‖)) (hZ:0≤g) : Sack g z (A*B):=by
    let T i:=u i*‖p i‖;let H i:=v i*‖f i‖;let c (i:I×J):= T i.1*H i.2
    have hh : Summable c:= hz.2.1.mul_of_nonneg hg.2.1 hz.1 hg.1
    refine Work.F08.budget_minor (g:=c) ⟨fun i=> mul_nonneg (hz.1 _) (hg.1 _),hh,?_⟩ (fun i=>mul_nonneg (hZ i) (norm_nonneg _)) h
    rw [hh.tsum_prod]; simp only [c,tsum_mul_left,tsum_mul_right]; exact mul_le_mul hz.2.2 hg.2.2 (tsum_nonneg (show 0≤H from hg.1)) hz.coins
end Sack
end YM.OPE.Flume
