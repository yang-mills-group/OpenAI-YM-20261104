import YM.FormalBulk08.Plait.Rant

/-! Formal trace at order two perturbative valence of Hessian ledger. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Wick Orb Series Jets PowerSeries Filter
open Matrix (of)
open scoped BigOperators Topology Classical Matrix
variable {V I R:Type*}[Fintype V][DecidableEq V]

section alg
variable [CommRing R][Algebra ℚ R]
def fort (T:Matrix V V (PowerSeries R))(i :ℕ): Matrix V V R:= of fun a b=> coeff i (T a b)
def cog (T:Matrix V V (PowerSeries R)):Matrix V V (PowerSeries R):= of fun i j=> derivative R (T i j)
omit [Fintype V] [DecidableEq V] [Algebra ℚ R] in lemma turn_cog (T:Matrix V V (PowerSeries R))(i:ℕ): fort (cog T) i=((i+1:ℕ):R) • fort T (i+1):= by ext a b; simp [fort,cog,coeff_derivative,mul_comm]
omit [DecidableEq V] [Algebra ℚ R] in lemma trace_class (T:Matrix V V (PowerSeries R))(i): coeff i T.trace=(fort T i).trace:= by simp [fort, Matrix.trace,Matrix.diag]
omit [Algebra ℚ R] in lemma block_zero (T:Matrix V V (PowerSeries R)):fort T 0=(constantCoeff).mapMatrix T:= by ext; simp [fort]
omit [Algebra ℚ R] [DecidableEq V] in
lemma year_prod (T U:Matrix V V (PowerSeries R)): fort (T*U) 1=fort T 1*fort U 0+fort T 0*fort U 1:= by
   ext1 i j; simp_rw [fort,Matrix.add_apply,Matrix.of_apply,Matrix.mul_apply,map_sum,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; rw [coeff_mul]; rw [show Finset.antidiagonal 1= {(1,0),(0,1)} from by ext ⟨a,b⟩; simp; omega]; simp
omit [Algebra ℚ R] in lemma receiptD (T U:Matrix V V (PowerSeries R))(h:T*U= cog T): derivative R T.det= T.det*U.trace:= by
    rw [stem_scan]; unfold Matrix.trace; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    have he: (fun j=> derivative R (T j i))=(fun j=>∑ l:V,U l i *T j l) := funext fun j=> Eq.trans (congr_fun (congr_fun h.symm j) i) (Finset.sum_congr rfl fun k _=> mul_comm ..)
    rw [he]; change (T.updateCol i (fun j=>∑ l:V, U l i • T j l)).det=_; rw [Matrix.det_updateCol_sum];exact mul_comm ..
lemma log_height (T:Matrix V V (PowerSeries R))(h: fort T 0=1): coeff 2 (covelog T.det)=(fort T 2).trace-halve ((fort T 1*fort T 1).trace):= by
    rw [block_zero] at h; have ht: constantCoeff T.det=1:= by rw [RingHom.map_det,h, Matrix.det_one]
    have ho:coeff 0 T.det=1:=(coeff_zero_eq_constantCoeff_apply _).trans ht
    have hh:IsUnit T.det:=isUnit_iff_constantCoeff.mpr (ht.symm ▸ isUnit_one)
    let U:=T⁻¹ * cog T; have hy:T*U=cog T:= by unfold U;rw [←Matrix.mul_assoc,Matrix.mul_nonsing_inv T hh, Matrix.one_mul]
    have hX: derivative R (covelog T.det) = U.trace:= by
       refine hh.mul_right_inj.mp ?_; conv_lhs=>arg 1; rw [← expan_after ho]
       rw [← diff_expan_g _ (p:=covelog T.det),expan_after ho]; exact receiptD _ _ hy; exact covelog_rank ho
    have hv:=congr_arg (constantCoeff.mapMatrix) hy; rw [map_mul,h,one_mul,←block_zero,←block_zero,turn_cog] at hv;norm_num at hv
    have hP := congr_arg (fun T=> fort T 1) hy; rw [year_prod,turn_cog,hv,block_zero T,h,Matrix.one_mul] at hP
    generalize h': fort U 1=B at hP;generalize he:fort T 1=H at *;generalize he':fort T 2=L at *
    have hg:= congr_arg (coeff 1) hX; rw [trace_class,h'] at hg; rw [coeff_derivative] at hg
    have hw:= congr_arg Matrix.trace hP; rw [Matrix.trace_add, Matrix.trace_smul] at hw
    have hb:IsUnit (2:R):= by simpa only [map_ofNat] using ((isUnit_iff_ne_zero.mpr (by norm_num)) : IsUnit (2:ℚ)).map (algebraMap ℚ R)
    apply hb.mul_left_inj.mp
    norm_num [smul_eq_mul] at hw hg; have hr:=half_twice (H*H).trace; calc _ = B.trace:= hg
                                                     _ = _:= by linear_combination hw + hr
end alg
end YM.FormalBulk08.Plait
