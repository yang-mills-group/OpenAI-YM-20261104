import YM.AllOrder.Ink.Brush
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Field
variable {ι:Type} (F:ι→Field α)
-- glm
omit [Fintype α]
/-- Σ of charges, no sharing external centers. -/
def sum (F:ι→Field α): Field α where
 Ty := (i:ι) × (F i).Ty
 slip i:= (F i.fst).slip i.snd
 fee i:= (F i.fst).fee i.snd
variable {U:ι→ℝ}(hf:∀ i,(F i).Good a (U i) k)(h:SumBudget U C)
include h hf
lemma keep : (Field.sum F).Good a C k:= ⟨fun i=>(hf i.1).length i.2,sumBudget_sigma (fun i=>(hf i).pay) h⟩

-- primitives
omit h hf in
lemma cone {ι : Type} {f:ι→ℝ} (H : Summable fun i=>‖f i‖): Summable f := H.of_norm

omit h hf
end Field
-- to reenable inst
namespace Field
variable {ι:Type} (F:ι→Field α){U:ι→ℝ}(hf:∀ i,(F i).Good a (U i) k)(h:SumBudget U C) (ha:0≤a)
include h hf ha
lemma collection (z:Site n)(x:rule α n): (Field.sum F).site n z x=∑' i,(F i).site n z x:= (show Summable (fun i:(Field.sum F).Ty=> (Field.sum F).fee i * invoice z ((Field.sum F).slip i) x) from (Field.cone ((keep F hf h).earns ha z x).2.1)).tsum_sigma
omit h hf in
lemma Good.total {A:Field α}(H : A.Good a D k): ∀ z:Site n,∀ x:rule α n, Summable (fun i:(A.Ty)=> A.fee i * invoice z (A.slip i) x):= fun z x=> Field.cone (H.earns ha z x).2.1
lemma contribution (n:Side)[Fintype ι] : (Field.sum F).table n=∑ i,(F i).table n:= by
 unfold table; ext1 x; rw [Finset.sum_apply,Finset.sum_comm,Finset.sum_apply]; simp_rw [collection F hf h ha _ x, Finset.sum_apply, tsum_fintype]
-- absolute commodity tests sigma onward (use collection)
omit h hf
variable (A:Field α) (H:A.Good a D k)
def scale (B:Field α) (t:ℝ): Field α where
  Ty := B.Ty
  slip := B.slip
  fee := t • B.fee
omit ha
include H
omit [Fintype α] in
lemma scale_good (t:ℝ): (scale A t).Good a (|t| *D) k:= by
  refine ⟨H.length,?_⟩; let f := fun i=> |t| * A.price a i; rw [show (scale A t).price a=f from funext (fun i=> by simp only [price,scale,f,Pi.smul_apply,smul_eq_mul,abs_mul,mul_left_comm])]; exact budget_scale (abs_nonneg _) H.pay
omit H
omit [Fintype α] in
lemma scale_table (t:ℝ)(n:Side): (scale A t).table n=t • A.table n:= by
 rw [table,table,Finset.smul_sum]; refine Finset.sum_congr rfl (fun i _=>?_); ext1 x; unfold scale site; simp only [Pi.smul_apply,smul_eq_mul,← tsum_mul_left,mul_assoc]

def void (α:Type) : Field α:= ⟨Empty,Empty.elim,Empty.elim⟩
omit [Fintype α] in
lemma silent : (void α).Good a 0 k:= by refine ⟨fun i=> i.elim,?_⟩; change SumBudget (fun i:Empty=>_) 0; exact ⟨fun i => Empty.elim i,Summable.of_finite,by simp⟩
omit [Fintype α] in
lemma dormant (n:Side): (void α).table n=0:=by unfold void table site; simp; exact mul_zero _
end Field
end YM.AllOrder.Ink
