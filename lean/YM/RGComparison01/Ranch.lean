import YM.RGComparison01.AuxSpell
/-!
# Centred coefficient agreement interface at Auxiliary

 Supply polynomially weighed op norm on the unscaled, generated tensors
 (or pay through scaled values at 0). NO physical push identity
 stipulated in this coefficient hypothesis.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice MeasureTheory
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Work.G05
open AuxDesk AuxJets AuxFabric AuxStage AuxBeam AuxCover
open PhysicalNext PhysicalNext.Repeat Metric
open Tensor
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {w v d h : ℝ} {j k n m r q q' a b : ℕ} {x : E}

/-- `Spline`: polynomial content guaranteed; RG02 doesn't have to
 assume a derivative estimate of the sum on the real-axis window. -/
structure Spline (k:ℕ) (f:E→ℝ) : Prop where
  smooth (n:WithTop ℕ∞) : ContDiff ℝ n f
  degree i (hi : k < i) x : iteratedFDeriv ℝ i f x=0

namespace Spline
variable {f g : E→ℝ} (y : ℝ)
lemma weaken (h : Spline j f) (hv:j ≤ k):Spline k f:= ⟨h.smooth,fun i hi=> h.degree i (lt_of_le_of_lt hv hi)⟩
lemma vacant (k : ℕ) : Spline k (fun _ : E=> y) := ⟨fun _=> contDiff_const,fun i hi x=> by
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0); rw [iteratedFDeriv_succ_const]; rfl ⟩
lemma add (h : Spline j f) (hp : Spline j g) : Spline j (f+g):= ⟨fun n=> (h.smooth n).add (hp.smooth n),fun i hi x=> by rw [iteratedFDeriv_add_apply (h.smooth _|>.contDiffAt) (hp.smooth _|>.contDiffAt), h.degree _ hi, hp.degree _ hi,add_zero]⟩
lemma smul (h : Spline j f) (a : ℝ) : Spline j (a • f):= ⟨fun n=> (h.smooth n).const_smul a,fun i hi x=> by rw [iteratedFDeriv_const_smul_apply (h.smooth _|>.contDiffAt),h.degree _ hi,smul_zero]⟩
lemma sub (h : Spline j f) (H : Spline j g) : Spline j (f-g):=by rw [show f-g=f+(-1:ℝ) • g from by simp [sub_eq_add_neg] ]; exact h.add (H.smul _)
lemma mul (h : Spline j f) (H : Spline k g) : Spline (j+k) (fun i=> f i*g i):= by
  refine ⟨fun i=> (h.smooth i).mul (H.smooth i),fun i hi x=>?_⟩
  apply norm_le_zero_iff.mp
  apply (norm_iteratedFDeriv_mul_le (h.smooth (_ : WithTop ℕ∞)) (H.smooth _) x (n:=i) le_rfl).trans; rw [Finset.sum_eq_zero]
  intro p hp; rw [Finset.mem_range] at hp; by_cases he:j < p
  · rw [h.degree _ he]; simp
  rw [H.degree _ (by omega)]; simp
lemma shift (h : Spline j f) (x:E): Spline j (fun y=> f (x+y)):= ⟨fun n=> (h.smooth n).comp (contDiff_const.add contDiff_id),fun i hi y=> by rw [iteratedFDeriv_comp_add_left,h.degree _ hi]⟩
lemma through (h : Spline j f) (L:F→L[ℝ] E): Spline j (f ∘ L):= ⟨fun n=> (h.smooth n).comp L.contDiff,fun i hi x=> by rw [linear_pull L (h.smooth _|>.contDiffAt),h.degree _ hi]; rfl⟩
lemma sum {ι:Type} (I:Finset ι) (v:ι→E→ℝ) (h:∀ i∈I,Spline j (v i)) : Spline j (fun y=> ∑ i∈I,v i y) := by
  induction I using Finset.induction_on with
  | empty => simp; exact vacant ..
  | @insert k s hi ih => simp_rw [Finset.sum_insert hi]; exact (h k (Finset.mem_insert_self ..)).add (ih (fun i hi=> h i (Finset.mem_insert_of_mem hi)))
lemma linear (L:E→L[ℝ] ℝ) : Spline 1 L:= by
  refine ⟨fun _=> L.contDiff,fun i hi x=>?_⟩
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  apply norm_le_zero_iff.mp; rw [← norm_iteratedFDeriv_fderiv]
  rw [show fderiv ℝ L=fun _=> L from funext fun x=> ContinuousLinearMap.fderiv _]
  obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : i≠0); rw [iteratedFDeriv_succ_const]; exact le_of_eq (norm_zero)
section finite
variable [FiniteDimensional ℝ E]
lemma diag (A : Tensor.T E ℝ k): Spline k (Tensor.diagonal A):= by
  induction k with
  | zero => rw [show Tensor.diagonal A=(fun _=> A 0) from funext fun _=> congr_arg A (Subsingleton.elim ..)]; exact vacant ..
  | succ k ih=>
     let B:= Module.finBasis ℝ E
     let b i : E→L[ℝ] ℝ:= (B.coord i).toContinuousLinearMap
     have ht x: Tensor.diagonal A x = Tensor.diagonal (A.curryLeft x) x := by
       apply congr_arg A; ext1 i; refine Fin.cases ?_ (fun j=> ?_) i <;> simp
     let T (x:E) (i):= (Tensor.diagonal (A.curryLeft (B i)) x)* (b i x)
     have he: Tensor.diagonal A=(fun x=> ∑ i,T x i):= by
       funext x; rw [ht]; rw [show A.curryLeft x=∑ i,b i x • A.curryLeft (B i) from ?_]; unfold T Tensor.diagonal; rw [_root_.sum_apply]; refine Finset.sum_congr rfl fun i _=> ?_; rw [_root_.smul_apply]; exact mul_comm ..
       conv_lhs => rw [show A.curryLeft x=A.curryLeft (∑ i,b i x • B i) from congr_arg _ (B.sum_repr x).symm]
       rw [map_sum]; simp_rw [map_smul]
     rw [he]; exact sum Finset.univ _ fun i _=> (ih _).mul (linear (b i))
end finite

-- Cancellations tested using the SAME plan after cuts. Grade k used only
-- for coefficient labels, not same as derivative job.
def Field (D n:ℕ) (A:Co E) := ∀ i ≤ n, Spline D (A i)
namespace Field
variable {A B : Co E}
lemma weaken (h:Field k n A) (hv:k ≤ j): Field j n A:= fun i hi=> (h i hi).weaken hv
lemma scalar (k n : ℕ) (a : ℝ): Field k n (Points.scalar (E:=E) a):= fun _ _=> vacant ..
lemma add (h : Field j n A) (p: Field j n B) : Field j n (A+B):= fun i hi=> (h i hi).add (p i hi)
lemma smul (h : Field j n A) (x:ℝ) : Field j n (x • A):= fun i hi=> (h i hi).smul _
lemma roots {v:Type} (s : Finset v) (f:v → AuxStage.Co E) (h:∀ i∈s, Field j n (f i)) : Field j n (∑ i∈s,f i) := by
  intro i hi; have he p (hp:p∈s) := h p hp i hi; rw [Finset.sum_apply]; rw [show (∑ j∈s,f j i)=fun x=>∑ j∈s,f j i x from funext fun x=> Finset.sum_apply ..]
  exact sum s _ he
lemma weave (h:Field j n A) (p:Field k n B): Field (j+k) n (Points.weave A B):= by
  intro i hi; apply sum; intro q hq; have hp:= Finset.mem_range.mp hq; exact (h _ (by omega)).mul (p _ (by omega))
lemma powPoly (h:Field j n A) (k:ℕ) : Field (j*k) n (Points.powPoly A k) := by induction k with|zero=> exact scalar (E:=E) _ _ 1|succ k ih=>  rw [Points.powPoly,Nat.mul_succ]; exact ih.weave h
lemma pacify (h:Field j n A) (g:ℝ→ℝ) (p:ℝ) (k:ℕ) : Field (j*k) n (AuxStage.pacify g A p k) := by
  apply roots; intro i hi; have he:=Finset.mem_range.mp hi; exact smul (weaken (powPoly (add h (scalar j n (-p))) i) (Nat.mul_le_mul_left _ (by omega))) _
section path
variable [FiniteDimensional ℝ E]
lemma ritualP (f:ℝ×E→ℝ) (q n:ℕ) : Field (n+q) n (AuxFabric.ritual f q) := by
  intro i hi
  let Q := coeff f (i+q) 0; let L:= ContinuousLinearMap.inr ℝ ℝ E
  let V x:=Tensor.diagonal Q ((1,(0:E))+L x); have hv:Spline (i+q) V:= ((Spline.diag Q).shift _).through L
  refine Spline.weaken (f:=ritual f q i) ?_ (Nat.add_le_add_right hi _)
  rw [show ritual f q i= V from funext fun x=> congr_arg _ (show ((1:ℝ),x)=(1,(0:E))+L x from by simp [L])]; exact hv
lemma Laced {ι:Type} [Fintype ι] [DecidableEq ι] (Q:Matrix ι ι ℝ) (f W V: Poll.Body ι → ℝ×E→ℝ) (n q q':ℕ): Field (n+(q'+q*n)) n (AuxFabric.intent Q f W V q q' n) := by
  refine roots _ _ (fun i hi=> ?_)
  refine smul ?_ _; intro j hj; have he := Finset.mem_range.mp hi
  apply (ritualP _ (q'+q*i) n j hj).weaken (Nat.add_le_add_left (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : i≤n)) _) _)
end path
end Field
lemma all_taxes (h : Spline n f) (u : ℝ) {x : E} (hx : ‖x‖ < u) (ha:u ≤ 1)
    (hv:∀ i ≤ n, normJ i f 0 * u^i ≤ w): Brush k ((n+1:ℕ)*w) u⁻¹ f x:= by
  let j:= n+k+1; have hJ : k ≤ j:= by omega
  have hK : n+1≤ j:= by omega
  have hz:0<u:= (norm_nonneg _).trans_lt hx; have he:= (mul_nonneg (norm_nonneg (iteratedFDeriv ℝ 0 f 0)) (by positivity)).trans (hv 0 (Nat.zero_le n))
  have ht := PhysicalNext.Repeat.Shellac.pools hz ha hK (f:=f) (C:=0) le_rfl he (fun _ _=> (h.smooth _).contDiffAt) (fun i hi _ x _=> ?_) (fun i hi=> hv _ (by omega)) x (mem_ball_zero_iff.mpr hx)
  · simpa only [zero_mul,zero_add] using ht.smaller hJ
  unfold normJ; rw [h.degree _ hi,norm_zero]
end Spline
end YM.RGComparison01
