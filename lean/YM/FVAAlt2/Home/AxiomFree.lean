import YM.FVAAlt2.Home.Gram
/-!
# Cancellation of the lead unipotent changes on the actually used IR schedule
 Matrix.B inversion. Does *not* bound the higher coefficients! Use exact algebra
ic cancellations before multiplying regulator errors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Report
open Function Filter Set Finset Real Matrix Topology
open scoped BigOperators Topology ContDiff PowerSeries Matrix
-- abstract linear algebra of frame ordering. Use any rank filtration and keep one probe restricted to slots<d.
section
variable {I J:Type} {l:Filter J} [DecidableEq I][Fintype I] (g:I→Prop)[DecidablePred g]
local notation "M"=> Matrix I I ℝ
variable (A: Matrix I I ℝ)
def sigma0 (B : Matrix I I ℝ): M:= Matrix.of (fun i j=> if g j then if g i then B i j else 0 else if i=j then 1 else 0)
lemma pockets (x:I→ℝ)(p:I)(hx:g p) (A:M) : (x ᵥ* sigma0 g A) p= ∑ i,x i*(if g i then A i p else 0):=by simp [Matrix.vecMul,dotProduct,sigma0,hx]
lemma pocket₀ (x:I→ℝ)(p:I)(hp:¬ g p)(A:M): ( x ᵥ* sigma0 g A ) p=x p:= by rw [Matrix.vecMul,dotProduct]; simp [sigma0,hp,mul_ite]
lemma pocket_hold (x:I→ℝ)(p:I)(hx:g p) (he:∀ i,¬ g i→ x i=0) (A:M): (x ᵥ*sigma0 g A) p=(x ᵥ* A) p:= by rw [pockets _ _ _ hx]; refine Finset.sum_congr rfl fun i _=>?_ ; split_ifs <;> first|rfl|(rename_i h; rw [he i h,zero_mul,zero_mul])
lemma sigmaInv (h:A.det≠0)(hc:∀ i j, g i→¬ g j→ A i j=0): (sigma0 g A).det≠0 := by
 have he(x:I→ℝ)(hx:x ᵥ* sigma0 g A=0): x=0:= by
    have hh(i:I) (hi:¬ g i):x i=0:=by rw [← pocket₀ g x i hi A]; exact congr_fun hx i
    apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr h)); dsimp only; rw [zero_vecMul]; funext j; by_cases hv:g j; · rw [← pocket_hold g x j hv hh]; exact congr_fun hx j
    refine sum_eq_zero fun i _=>?_ ; by_cases he:g i; dsimp only; rw [hc i j he hv,mul_zero]; rw [hh i he,zero_mul]
 refine isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.vecMul_injective_iff_isUnit.mp ?_)); intro i j hx; apply sub_eq_zero.mp; apply he (i-j); dsimp only at hx; rw [ sub_vecMul, hx, sub_self ]

lemma sigmaT {x:J→M}(h:Tendsto x l (𝓝 A)): Tendsto (fun j=> sigma0 g (x j)) l (𝓝 (sigma0 g A)):= by
 apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; by_cases hi:g i <;> by_cases hj:g j <;> simp only [sigma0, hi,hj,if_true,if_false,Matrix.of_apply] <;> first|exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j)| exact tendsto_const_nhds

lemma into_inv (v:J→I→ℝ) {m:J→M}(hx:Tendsto m l (𝓝 A))(h:A.det≠0)(hv:Tendsto (fun j=> v j ᵥ* m j) l (𝓝 0)): Tendsto v l (𝓝 0):=by
 have he:Tendsto (fun j=>(m j)⁻¹) l (𝓝 A⁻¹):= (continuousAt_matrix_inv A (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ h)).tendsto.comp hx
 have hm: ∀ᶠ i in l,(m i).det≠0:= ((continuous_id.matrix_det (n:=I)|>.continuousAt (x:=A)).tendsto.comp hx).eventually (isOpen_compl_singleton.mem_nhds h)
 apply tendsto_pi_nhds.mpr; intro i
 apply Filter.Tendsto.congr' _ (f₁:=fun j=> ((v j ᵥ* m j) ᵥ*(m j)⁻¹) i) ?_ -- order
 · filter_upwards [hm] with j h; rw [vecMul_vecMul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), vecMul_one]
 refine (tendsto_finsetSum (f:=fun k j=> (v j ᵥ* m j) k * (m j)⁻¹ k i) Finset.univ (fun j _=> (tendsto_pi_nhds.mp hv j).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he j) i))).mono_right (le_of_eq ?_); congr 1; simp
end
section rank
variable {I J: Type} [DecidableEq I][Fintype I]{A B: J→ Matrix I I ℝ}{p:I} (rank:I→ℕ) {l: Filter J}
set_option linter.unusedSectionVars false
local notation "M"=> Matrix I I ℝ
lemma nested (C:M)(v:I) (ht:C.det≠0)(he:∀ i j,rank i < rank v→ rank v≤rank j→ C i j=0) (hk:∀ j x,rank v ≤rank x→(B j-1) v x=0)(hh:∀ z i,rank i<rank v→ ∀ j,( B z ) i j=(1:M) i j)(h:Tendsto A l (𝓝 C))(hx:Tendsto (fun i=>B i * A i * (B i)ᵀ) l (𝓝 C)) : Tendsto (fun i=> (B i-1) v) l (𝓝 0) := by
 let g:I→Prop:= (rank · < rank v)
 let w (i:J):=(B i-1) v
 have hb(i)(p:I)(hp:¬ g p): w i p=0:=hk _ _ (Nat.le_of_not_gt hp)
 refine into_inv (sigma0 g C) w (sigmaT g C h) (sigmaInv g C ht (fun i j hi h=> he i j hi (Nat.le_of_not_gt h))) ?_; apply tendsto_pi_nhds.mpr; intro a; by_cases ha:g a; swap
 · simp_rw [pocket₀ g _ a ha, hb _ a ha]; exact tendsto_const_nhds
 have h(i:J): ( B i * A i * ( B i )ᵀ - A i ) v a=(w i ᵥ* sigma0 g (A i)) a:= by
    rw [Matrix.sub_apply,Matrix.mul_apply,Finset.sum_eq_single a, Matrix.transpose_apply, hh i a ha a, Matrix.one_apply_eq,mul_one]; swap; · intro j _ hv; rw [Matrix.transpose_apply,hh i a ha j,Matrix.one_apply_ne' hv,mul_zero]
    swap; · simp
    rw [pocket_hold g _ a ha (hb i)]; change _=((B i-1)* A i) v a; rw [sub_mul,one_mul,Matrix.sub_apply]
 refine ((Filter.Tendsto.congr (fun i=> h i) ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hx v) a).sub (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (by assumption : Tendsto A l (𝓝 C)) v) a)))).mono_right (le_of_eq (by rw [sub_self];rfl))
end rank
end YM.FVAAlt2.Home.Report
