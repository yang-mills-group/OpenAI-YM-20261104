import YM.AlbaMS.Cutis.Arms

/-!
# Hodge Maxwell period and transverse- vs longitudinal-cover identities

Scalar Green. Explicit combined-vector formulas in mixed orientation (site-base
at tail). Need Ω bracket Landau with `-? X`, installed in Fritz. Rank L counts,
appears not eliminated. Use matrices including ALL modes (denorm zeros). At
this point sums native costing. Lines may later be truncated in bands.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix
open Bric Loft Inlay Inlay.Net Odom Lattice
variable {n : Side}{G:Gauge}(n)(i j : Axis)
def mono : Dir n:= pump n (lap n) - bound n*(bound n)ᵀ
def tip : Matrix (Vtx n) (Arm n) ℝ := del n i * (mouth n j)ᵀ - del n j* (mouth n i)ᵀ
lemma tip_abs : tip n i i=0:=sub_self _
lemma tip_sym : tip n i j = - tip n j i:=by unfold tip; abel
lemma mono_sym : (mono n)ᵀ=mono n:=by simp only [mono,pump, transpose_sub,transpose_mul,transpose_transpose,chip_t,lap_sym]
lemma mono_bound : mono n*bound n=0:=by rw [mono,Matrix.sub_mul,pump_lap,Matrix.mul_assoc,q_sc, sub_self]
lemma mono_mean : mono n*pump n (mean n)=0:=by
  have h : (bound n)ᵀ*pump n (mean n)=0:= by
    have hm:= congr_arg transpose (mean_bound n); rw [transpose_mul,transpose_zero, show (pump n (mean n))ᵀ=pump n (mean n) by rw [pump, chip_t,mean_t]] at hm; exact hm
  rw [mono, Matrix.sub_mul, Matrix.mul_assoc,h, Matrix.mul_zero]; simp only [pump, chip_prod, lap_mean,chip_zero,sub_zero]

private lemma pairs (F:Axis→Axis→Dir n)(h:∀ i j, F i j=F j i)(H:∀ i,F i i=0): (∑ i:Axis,∑ j:Axis, F i j)=(∑ p:PlaqAxes,F p.val.1 p.val.2)+(∑ p:PlaqAxes,F p.val.1 p.val.2):=by
  have he:(∑ x:PlaqAxes,F x.val.1 x.val.2)= ∑ i:Axis,∑ j:Axis, if i<j then F i j else 0:=by
    rw [← Fintype.sum_prod_type (fun x:Axis × Axis=>if x.1<x.2 then F x.1 x.2 else 0),← Finset.sum_filter]; exact (Finset.sum_subtype _ (p:=fun x:Axis × Axis => x.1<x.2) (by simp) (fun x=> F x.1 x.2)).symm
  rw [he]; nth_rw 3 [Finset.sum_comm]; -- test occurrences
  simp_rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ;
  rcases lt_trichotomy i j with he|he|he; simp [he,not_lt_of_ge he.le]; simp [he,H]; rw [if_neg (not_lt_of_ge he.le),if_pos he,zero_add]; exact h ..
lemma salute : (∑ p:PlaqAxes, (tip n p.val.1 p.val.2)ᵀ*tip n p.val.1 p.val.2)= mono n:=by
  let B:=∑ p:PlaqAxes, (tip n p.val.1 p.val.2)ᵀ*tip n p.val.1 p.val.2; let Q (i j:Axis) := (tip n i j)ᵀ * tip n i j
  have hh : B+B=∑ i:Axis,∑ j:Axis,Q i j:=by
    refine (pairs n Q (fun i j=>?_) (fun i=> by unfold Q; rw [tip_abs,Matrix.mul_zero])).symm; unfold Q; rw [tip_sym n i j]; simp
  let A(i j:Axis):= mouth n i * ((del n j)ᵀ * del n j) * (mouth n i)ᵀ
  let M(i j:Axis):= mouth n i * del n i * (del n j)ᵀ * (mouth n j)ᵀ
  have he i j: Q i j = A i j + A j i - (M i j + M j i):= by
    have ht i j : (mouth n i * (del n j)ᵀ)*(del n i*(mouth n j)ᵀ)= M i j:=by unfold M; rw [← Matrix.mul_assoc _ _ (mouth n j)ᵀ, Matrix.mul_assoc _ _ (del n i),show _=_ from dels_t n j i,Matrix.mul_assoc (mouth n i) (del n i) (del n j)ᵀ];
    unfold Q; rw [tip, transpose_sub, transpose_mul,transpose_mul,transpose_transpose,transpose_transpose, Matrix.sub_mul, Matrix.mul_sub,Matrix.mul_sub,ht,ht]
    unfold A; simp_rw [Matrix.mul_assoc]; abel
  have hv (F:Axis→Axis→Dir n) : (∑ i:Axis,∑ j:Axis,F j i)=(∑ i:Axis,∑ j:Axis,F i j):= Finset.sum_comm
  have hy : (∑ i:Axis,∑ j:Axis,A i j)= pump n (lap n):= by unfold A; simp_rw [← Matrix.sum_mul, ← Matrix.mul_sum]; exact stalk ..
  have hx:(∑ i:Axis,∑ j:Axis,M i j)=bound n*(bound n)ᵀ:=by unfold M; simp_rw [Matrix.mul_assoc (mouth n _* del n _), ← transpose_mul,← Matrix.mul_sum, ← transpose_sum,← Matrix.sum_mul]; rfl
  change B=mono n; apply smul_right_injective _ (show (2:ℝ)≠0 by norm_num); simp_rw [two_smul]; rw [hh]; simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, hv A, hv M, hy,hx]; unfold mono; abel

def L : Dir n:= pump n (green n)
def U : Tong n:= L n * bound n
def W : Dir n:= L n*mono n* L n
lemma LT : (L n)ᵀ=L n:=by rw [L,pump, chip_t,green_sym]
lemma WT : (W n)ᵀ=W n:=by rw [W,transpose_mul,transpose_mul,LT,mono_sym,Matrix.mul_assoc]
-- elementary matrix facts. cocycle H Pm etc.
lemma lap_L : L n * pump n (lap n)=1- pump n (mean n):= by
  have h := congr_arg transpose (lap_green n); rw [transpose_mul,lap_sym,green_sym,transpose_sub,mean_t,transpose_one] at h
  simp_rw [L,pump,chip_prod,h,chip_sub,chip_one]
lemma UL : (U n)ᵀ*bound n=1-mean n:=by rw [U,L,pump_green,transpose_mul,green_sym,Matrix.mul_assoc,q_sc]; nth_rw 1 [← green_sym,← lap_sym]; rw [← transpose_mul, lap_green,transpose_sub,mean_t,transpose_one]
lemma UM : U n* mean n=0:= by rw [U,Matrix.mul_assoc,bound_mean,Matrix.mul_zero]
lemma symmetryU : bound n * (U n)ᵀ=U n*(bound n)ᵀ:=by rw [U,L,pump_green,transpose_mul,green_sym,Matrix.mul_assoc]
lemma W_t : W n * bound n=0:=by rw [W, Matrix.mul_assoc, show L n * bound n=_ from pump_green n, ← Matrix.mul_assoc, Matrix.mul_assoc (L n), mono_bound, Matrix.mul_zero, Matrix.zero_mul]
lemma projectionU : bound n*(U n)ᵀ+ L n* mono n=1-pump n (mean n):=by rw [symmetryU]; unfold mono U; rw [Matrix.mul_sub, Matrix.mul_assoc,lap_L]; abel
lemma L_mean : L n*pump n (mean n)=0:=by rw [L]; simp_rw [pump,chip_prod,green_mean,chip_zero]
lemma W_hit : W n * mono n = L n * mono n:=by
  rw [W,Matrix.mul_assoc]; nth_rw 2 [show L n*mono n=_ from eq_sub_of_add_eq' (projectionU n)]; rw [Matrix.mul_sub, ← Matrix.mul_assoc _ (bound n), Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc (L n),mono_mean, Matrix.mul_zero, sub_zero, Matrix.mul_assoc (L n), mono_bound, Matrix.mul_zero, Matrix.zero_mul,sub_zero]
end YM.MSBar.Cutis.Winter
