import YM.AveragedStep.Recursion.Switch
/-!
# Finitely many operations on fields (at each announced step/order) paid
in *honest coefficient currency*. Real linear here, complex splitting separately
when needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
abbrev Spray (I:Type*):=I→₀ℝ
variable {I J X : Type*}[AddCommGroup X][Module ℝ X]
def offer (V:I→X):Spray I→ₗ[ℝ] X:= Finsupp.linearCombination ℝ V
@[simp] lemma offer_single (i:I)(w:ℝ)(V:I→X):offer V (Finsupp.single i w)=w • V i:=Finsupp.linearCombination_single ..
lemma offer_def (V:I→X)(s:Spray I): offer V s= ∑ i ∈ s.support,s i • V i:=rfl
lemma offer_add (V W:I→X)(s:Spray I):offer (V+W) s = offer V s + offer W s :=by simp_rw [offer_def,Pi.add_apply,smul_add,Finset.sum_add_distrib]
lemma offer_sub (V W:I→X)(s:Spray I):offer (V-W) s = offer V s - offer W s :=by simp_rw [offer_def,Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]
lemma offer_smul (t:ℝ)(V:I→X)(s:Spray I):offer (t • V) s = t • offer V s :=by simp only [offer_def,Pi.smul_apply,Finset.smul_sum,smul_comm t]
lemma offer_sum (T:Finset J)(V:J→I→X)(s:Spray I):offer (∑ i∈T,V i) s =∑ i∈T,offer (V i) s:=by
 simp only [offer_def,Finset.sum_apply,Finset.smul_sum]; exact Finset.sum_comm

def leftS {I J:Type*}(f:I→J): Spray I→ₗ[ℝ] Spray J:=offer (fun i=>Finsupp.single (f i) (1:ℝ))
lemma offer_left (f:I→J)(s:Spray I)(V:J→X):offer V (leftS f s)=offer (V∘f) s:=by
 rw [leftS,offer_def _ s,map_sum,offer_def]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,offer_single,one_smul];rfl

-- A coefficient bill: equivalent to absolute sum at materializing precision,
-- don't require assignments continuous even though old alphabet contains full tori.
structure Signed (p:I→Prop)(s:Spray I)(K:ℝ):Prop where
 pos : 0≤K
 pay (L:ℝ)(W:I→ℝ) : 0≤L → (∀ i,p i → |W i| ≤ L) → |offer W s| ≤ K*L
lemma Signed.enrich {p q:I→Prop}{s:Spray I}{K B:ℝ}(h:Signed p s K)(he:∀ i,p i→q i)(hk:K≤B) :Signed q s B:=⟨h.pos.trans hk,fun L W hL H=> (h.pay L W hL (fun i hp=>H i (he i hp))).trans (mul_le_mul_of_nonneg_right hk hL)⟩
lemma Signed.zero (p:I→Prop):Signed p 0 0:=⟨le_rfl,by simp⟩
lemma Signed.single (p:I→Prop){i:I}(h:p i)(B:ℝ):Signed p (Finsupp.single i B) |B|:=by
 refine ⟨by positivity,fun L W hL H=>?_⟩
 rw [offer_single,smul_eq_mul,abs_mul]; gcongr; exact H i h
lemma Signed.scale {p:I→Prop}{s:Spray I}{K:ℝ}(h:Signed p s K)(B:ℝ):Signed p (B • s) (|B| *K):=by
 refine ⟨mul_nonneg (abs_nonneg _) h.pos,fun L W hL H=>?_⟩; rw [map_smul,smul_eq_mul,abs_mul,mul_assoc]; gcongr; exact h.pay L W hL H
lemma Signed.plus {p:I→Prop}{s t:Spray I}{K A:ℝ}(h:Signed p s K)(ht:Signed p t A): Signed p (s+t) (K+A):=by
 refine ⟨add_nonneg h.pos ht.pos,fun L W hL H=>?_⟩; rw [map_add,add_mul]; exact (abs_add_le ..).trans (add_le_add (h.pay L W hL H) (ht.pay L W hL H))
lemma Signed.minus {p:I→Prop}{s t:Spray I}{K A:ℝ}(h:Signed p s K)(ht:Signed p t A): Signed p (s-t) (K+A):=by
 refine ⟨add_nonneg h.pos ht.pos,fun L W hL H=>?_⟩; rw [map_sub,add_mul]; exact (abs_sub ..).trans (add_le_add (h.pay L W hL H) (ht.pay L W hL H))
lemma Signed.sum {p:I→Prop}(T:Finset J)(t:J→Spray I)(A:J→ℝ)(h:∀ j∈T,Signed p (t j) (A j)):
    Signed p (∑ j∈T,t j) (∑ j∈T,A j):=by
 refine ⟨Finset.sum_nonneg (fun i hi=>(h _ hi).pos),fun L W hL H=>?_⟩; rw [map_sum,Finset.sum_mul]; exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i hi=>(h _ hi).pay L W hL H))
lemma Signed.left (p:I→Prop){s:Spray I}{K:ℝ}(h:Signed p s K)(f:I→J)(q:J→Prop)(hf:∀ i,p i→q (f i)):Signed q (leftS f s) K:=by
 exact ⟨h.pos,fun L W hL H=> (offer_left f s W).symm ▸ h.pay L _ hL (fun i hi=>H _ (hf _ hi))⟩

-- No Envelope demands dropped at application. Evaluate finite stencils
-- in, and after, actual top report; same (re-)gauge and normalizations.
variable {c g:Side}{G:Gauge}{S:StepData c g}(F:Forest S.ratio)(hS:S.patch.Branches S.kernel G)
include hS in
lemma offer_report (t:ℝ)(x:Site c)(W:I→TopologyQ F G→ℝ)(h:∀ i, Envelope (W i))(s:Spray I):
    report F t x (fun z=>offer (fun i=> W i z) s)=offer (fun i=>report F t x (W i)) s:=by
 simp_rw [offer_def]
 rw [report_sum F x hS]; swap; · intro i hi; exact (Envelope.const _).mul (h i)
 exact Finset.sum_congr rfl fun i _=> report_scale F x t (s i) _
end YM.AveragedStep.SD
