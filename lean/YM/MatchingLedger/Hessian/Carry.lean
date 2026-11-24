import YM.MatchingLedger.Hessian.Cells

/-!
# Local terms of quadratic forms and their prices

Makes the weighted currency independent of unchosen finite bases on label forms. Sum, sym,
seq support count via `Corona.halo_size`, smallest location freezes only ROOT not retargeting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Spring
open Function Filter Lattice Wilson RG Exterior Precision Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Finset
variable {n : Side}
variable {E : Type} [NormedAddCommGroup E]

def felt (r:ℝ) (o : Site n) (A : Site n→ E) := ∑ i, ‖A i‖ * beam r i o
lemma felt_nn (r : ℝ)(o:Site n)(A: Site n→E) : 0≤felt r o A:= Finset.sum_nonneg (fun _ _=> mul_nonneg (norm_nonneg _) (beam_pos ..).le)
lemma felt_entry (o x:Site n) (r:ℝ)(A: Site n→E) : ‖A x‖ * beam r x o ≤ felt r o A:= Finset.single_le_sum (f:=fun i=> ‖A i‖*beam r i o) (fun _ _=> mul_nonneg (norm_nonneg _) (beam_pos ..).le) (Finset.mem_univ x)

lemma tilt {r:ℝ} (hr:0≤r)(k o : Site n) (A : Site n→E): felt r o A≤ felt r k A * beam r k o:= by
  unfold felt; rw [Finset.sum_mul]; simp_rw [mul_assoc]; exact Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (beam_merge hr i _ _) (norm_nonneg _)

lemma funded {r:ℝ}(o : Site n)(M:ℕ) {A : Site n→E} (hr : r≤ 1) {B:ℝ} (hB: 0≤ B) (he : Function.support (fun i=> ‖A i‖) ⊆ ↑(halo M {o})) (h:∀ i,‖A i‖ ≤ B) : felt r o A ≤ B*(M+M+1:ℝ)^4 * Real.exp M:= by
  unfold felt
  have ht : 0≤B*Real.exp M:= mul_nonneg hB (Real.exp_pos _).le
  rw [← Finset.sum_subset (Finset.subset_univ (halo M {o})) (fun i _ hi=> show ‖A i‖*beam r i o=0 from by rw [show ‖A i‖=0 from notMem_support.mp (fun hi'=> hi (he hi')),zero_mul])]
  apply (Finset.sum_le_sum (g:=fun _=>B*Real.exp M) (fun i hi=> mul_le_mul (h i) (Real.exp_monotone (le_trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hr) (Nat.cast_le.mpr ((separation_comm i o).trans_le (near_root.mp hi))))) (beam_pos ..).le hB)).trans
  rw [Finset.sum_const,nsmul_eq_mul]; refine (mul_le_mul_of_nonneg_right (show _≤ _ from ?_) ht).trans_eq (show (M+M+1:ℝ)^4*(B*Real.exp M)=_ from by ring)
  exact_mod_cast (le_trans (Corona.halo_size {o} M) (by simp : _ * (M+M+1)^4 = (M+M+1)^4).le)

section infinite
variable {ι : Type*} [CompleteSpace E] (A : ι→Site n→E) {z : ι → ℝ} {r : ℝ} {o : Site n} (hr:0≤r) (he:Summable z) (hf:∀ i, felt r o (A i)≤ z i)
include hr he hf
omit [CompleteSpace E] in
lemma felt_arrives (j : Site n) : Summable (fun i=> ‖A i j‖) := Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> ((le_mul_of_one_le_right (norm_nonneg _) (beam_one hr j o)).trans (felt_entry o j r (A i))).trans (hf i)) he
omit [CompleteSpace E] in
lemma felt_infinite : felt r o (fun j=> ∑' i,A i j) ≤ ∑' i,z i:= by
  let M(x:Site n):= (felt_arrives A hr he hf x).mul_right (beam r x o); unfold felt
  refine le_trans (Finset.sum_le_sum (g:=fun j=> (∑' i,‖A i j‖)* beam r j o) (fun i _=>mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (felt_arrives A hr he hf i)) (beam_pos ..).le)) ?_
  simp_rw [← tsum_mul_right]; rw [← Summable.tsum_finsetSum (fun j _=> M j)]; exact (Summable.of_nonneg_of_le (fun i=>felt_nn r o (A i)) hf he).tsum_le_tsum hf he
end infinite

variable [NormedSpace ℝ E]
def fieldRow (U : Floor n→ₗ[ℝ] E) : Site n→E := U ∘ spot
lemma summed (U: Floor n→ₗ[ℝ] E) (v:Floor n) : U v=∑ i,v i • fieldRow U i:=by nth_rw 1 [surface_basis v]; rw [map_sum]; exact Finset.sum_congr rfl (fun i _=>U.map_smul_of_tower _ _)
lemma felt_scale (r : ℝ)(o : Site n)(t : ℝ)(U : Site n→E): felt r o (fun i=> t • U i)=‖t‖*felt r o U:=by unfold felt; simp_rw [norm_smul,mul_assoc, Finset.mul_sum]

-- no triangle factors incurred on *bilinear* rows
omit [NormedSpace ℝ E] in
lemma paid_lift {F : Type}[NormedAddCommGroup F] {r : ℝ}(hr:0≤r)(o:Site n){X:Block n} (A : Site n→ E)(B : Site n→ F)(h:∀ i j, ‖X i j‖≤ ‖A i‖*‖B j‖):
    paid X r ≤ felt r o A * felt r o B:= by
  unfold paid felt; rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; refine Finset.sum_le_sum fun j _=>?_;
  rw [beam_comm r j o]; exact (mul_le_mul (h ..) (beam_merge hr i o j) (beam_pos ..).le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

section pairs
variable {F : Type}[NormedAddCommGroup F][InnerProductSpace ℝ F]

def lap (U W:Floor n→ₗ[ℝ] F) : Block n:= fun i j=> inner ℝ (fieldRow U i) (fieldRow W j)
lemma pulse_lap (U W : Floor n→ₗ[ℝ] F)(x y:Floor n): pulse (lap U W) x y= inner ℝ (U x) (W y) := by
  rw [summed U x,summed W y,sum_inner]; unfold pulse utter spur lap; refine Finset.sum_congr rfl (fun i _=>?_); rw [inner_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [real_inner_smul_left,real_inner_smul_right]; ring
lemma paid_lap {r:ℝ}(hr:0≤r) (o:Site n)(U W:Floor n→ₗ[ℝ] F): paid (lap U W) r ≤ felt r o (fieldRow U)*felt r o (fieldRow W):= paid_lift hr o _ _ (fun i _=>abs_real_inner_le_norm (fieldRow U i) _)
end pairs

-- surface map, independent of path clm; symmetry from curvature tag only downstream
variable {G : Gauge} (c : G.Color) (hc : ‖c‖=1)

def surf : Floor n→ₗ[ℝ]Directions G n where
  toFun v e:= if e.2=0 then v e.1 • c else 0
  map_add' x y:= by ext1 i; by_cases hi:i.2=0<;> simp [hi,add_smul]
  map_smul' t x:= by ext1 i; by_cases hi:i.2=0 <;> simp [hi,smul_smul]
lemma surf_apply (v:Floor n)(x:Site n)(i:Axis) : surf c v (x,i)= if i=0 then v x • c else 0:=rfl
lemma surf_spot (x:Site n) : surf c (spot x)=Pi.single (x,(0:Axis)) c := by
  funext e; rcases e with ⟨i,j⟩; rw [Pi.single_apply,surf_apply]; by_cases hi:i=x<;>by_cases hj:j=0<;>simp_all [spot,Prod.mk.injEq]
include hc
lemma surf_spot_norm (x:Site n)(i:Edge (Site n)) : ‖surf c (spot x) i‖ ≤ 1:= by unfold spot; rw [surf_apply c _ i.1 i.2]; split_ifs <;> simp_all
lemma surf_norm (x:Floor n)(i:Edge (Site n)) : ‖surf c x i‖ ≤ ‖x i.1‖:= by rw [surf_apply c _ i.1 i.2]; split_ifs <;> simp [norm_smul,hc]
end YM.MatchingLedger.Spring
