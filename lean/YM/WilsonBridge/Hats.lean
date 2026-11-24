import YM.WilsonBridge.FiniteDFT
/-!
# Precisely Fourier/spectral transforms of quadratic blocks
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.FiniteDFT
open MS MS.Book MS.Swirl MS.Koszul MS.Cylinder MS.City MS.Latch MS.Fleet MS.Landau
open MS.Book.Program MS.Plane Cylinder.Lab Tone Mesh MS.Native MS.Tone Lattice MS.Orbit MS.Orbit.Cog
open Function Finset
open scoped BigOperators Matrix
variable {V K I J A B : Type}[DecidableEq V][DecidableEq K][Fintype V][Fintype K]
    [Fintype I] [Fintype J]
    [DecidableEq A][Fintype A][Fintype B]
    {G:Gauge}{n:Side}
local notation "T" H => Mode H (Site n)
-- spectral = conjugate matrix on ordinary coordinates (not quadratic in contrast with `Obs` DFT uses)
omit [Fintype I] [DecidableEq V] [DecidableEq K] [Fintype V] [DecidableEq A] [Fintype A] [Fintype B] in
lemma orders_mul (e: I ≃ T V)(v: J≃ T K)(w:B≃ T A) (U:Matrix I J ℂ) (H:Matrix J B ℂ): -- cleaner omit tests
    Matrix.reindex e w (U*H)=Matrix.reindex e v U * Matrix.reindex v w H:= (Matrix.submatrix_mul_equiv ..).symm -- signature
omit [Fintype I] [Fintype J] in
def hats (e : I ≃ T V)(d: J≃ T K): Matrix I J ℂ ≃ₗ[ℂ] Matrix (T V) (T K) ℂ:= by
    let L : Matrix (T V) (T K) ℂ ≃ₗ[ℂ] Matrix (T V) (T K) ℂ:= {
        toFun H:=Fx V n*H*F K n
        invFun H:=F V n*H*Fx K n
        left_inv H:=by dsimp only; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,inv_fwd V n,Matrix.one_mul,Matrix.mul_assoc, inv_fwd K n,Matrix.mul_one ]
        right_inv H:=by dsimp only; rw [← Matrix.mul_assoc,← Matrix.mul_assoc,fwd_inv V n, Matrix.one_mul,Matrix.mul_assoc,fwd_inv K n,Matrix.mul_one ]
        map_add' U H:= by rw [ Matrix.mul_add,Matrix.add_mul ]
        map_smul' a U:= by rw [ Matrix.mul_smul,Matrix.smul_mul ]; rfl }
    exact LinearEquiv.trans (Matrix.reindexLinearEquiv ℂ ℂ e d) L -- no omit needed?
omit [Fintype I] [Fintype J] in
lemma hats_apply (e : I ≃ T V)(d: J≃ T K) (X:Matrix I J ℂ): hats e d X=Fx V n*(Matrix.reindex e d X)*F K n:= rfl
omit [Fintype I] in
lemma hats_one [DecidableEq I] (e:I ≃ T V): hats e e (1:Matrix I I ℂ)=1:= by rw [hats_apply]; simp [fwd_inv]
omit [Fintype I] [Fintype B] in
lemma hats_mul (e:I ≃ T V) (v:J≃ T K)(w: B≃ T A)(X:Matrix I J ℂ)(U:Matrix J B ℂ): hats e w (X*U)= hats e v X * hats v w U:= by simp only [hats_apply]; rw [orders_mul e v w X U]; simp only [← Matrix.mul_assoc, show ∀ (M:Matrix (T V) (T K) ℂ), M * F K n*Fx K n=M from fun M=> by rw [ Matrix.mul_assoc,inv_fwd,Matrix.mul_one] ]
-- constant mode projector for any component
open Matrix in
def mean (e:I ≃ T V): Matrix I I ℂ:= fun i j=> if (e i).1=(e j).1 then scaleZ n else 0
abbrev diagonalBlocks (q: Site n → Matrix V K ℂ) : Matrix (T V) (T K) ℂ:= Matrix.blockDiagonal q
omit [DecidableEq V] [DecidableEq K] [Fintype V] [Fintype K] in
lemma diagB (U: Site n→Matrix V K ℂ) (i j): diagonalBlocks U i j= if i.2=j.2 then U i.2 i.1 j.1 else 0:= Matrix.blockDiagonal_apply ..
omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq K] [DecidableEq A] in
lemma diagX (U: Site n → Matrix V K ℂ)(X: Site n →Matrix K A ℂ)(i j): (diagonalBlocks U * diagonalBlocks X) i j=(diagonalBlocks fun p=> U p *X p) i j:= by rw [← Matrix.blockDiagonal_mul U X]
-- harmonic
abbrev constants [DecidableEq I] : Site n→Matrix I I ℂ:= fun p=> if p=0 then 1 else 0
lemma sum_const (p:Site n) : ∑ x:Site n,Bloch.cell p x= if p=0 then vol n else 0:= by
    split_ifs with h; subst p; simp [Bloch.cell,vol]
    exact Bloch.sum_cell h
lemma sum_inv_const (p:Site n): ∑ x:Site n,Bloch.cell p (-x)= if p=0 then vol n else 0:= Eq.trans (Equiv.sum_comp (Equiv.neg _) (Bloch.cell p)) (sum_const _)
omit [Fintype I] in
lemma hats_mean (e:I≃ T V): hats e e (mean e)=diagonalBlocks constants:= by
    let M:= Matrix.reindex e e (mean e); let C : Matrix (T V) (T V) ℂ := diagonalBlocks constants
    have he (i j: T V): M i j= if i.1=j.1 then scaleZ n else 0:= by simp [M, Matrix.reindex_apply,mean]
    have hf : M * F V n= F V n * C:= by
        ext ⟨i,p⟩ ⟨j,q⟩ :1
        simp_rw [ Matrix.mul_apply,Fintype.sum_prod_type (α₁:=V),he,F,show ∀ i j:T V,C i j=_ from (fun i j=> diagB _ i j) ]; by_cases h:i=j
        · subst j; rw [Finset.sum_eq_single_of_mem i (mem_univ _), Finset.sum_eq_single_of_mem (f:=fun x:V=> ∑ x_1:Site n,(if i=x then Bloch.cell p x_1 else 0)*(if x_1=q then constants x_1 x i else 0)) i (mem_univ _)]; swap; exact fun k _ h=> by simp [Ne.symm h]
          swap; exact fun k _ h=> by simp [h]
          simp only [if_true,mul_ite, mul_zero, Finset.sum_ite_eq',Finset.mem_univ]; simp_rw [ Bloch.cell_duality _ q, ← Finset.mul_sum,sum_const ]; by_cases h:q=0; · rw [h,if_pos rfl]; rw [scale_factor n, inv_mul_cancel₀ (nonzero n)]; simp [constants,Bloch.cell]
          simp [h,constants]
        rw [Finset.sum_eq_single_of_mem i (mem_univ _), Finset.sum_eq_single_of_mem (f:=fun x:V=> ∑ x_1:Site n,(if i=x then Bloch.cell p x_1 else 0)*(if x_1=q then constants x_1 x j else 0)) i (mem_univ _)]; swap; exact fun k _ h=> by simp [Ne.symm h];
        swap; exact fun k _ h=> by simp [Ne.symm h]
        have hn (p:Site n): constants p i j= 0:= by unfold constants; split_ifs <;> simp [h]
        simp [h,hn] -- progress
    rw [hats_apply]; change Fx V n*M*F V n=C; rw [Matrix.mul_assoc,hf,← Matrix.mul_assoc,fwd_inv,Matrix.one_mul]
-- Hessian reindexed. value at momentum minus/full useful.
omit [Fintype I] [Fintype J] in
lemma measures_vertex (e:I≃ T V)(d:J≃ T K)(W:Matrix I J ℂ)(i:T V)(j:T K):
    hats e d W i j = scaleZ n * ( F V n *Matrix.reindex e d W * F K n ) (i.1,-i.2) j:= by
    have hx (t:T V): Fx V n i t= scaleZ n * F V n (i.1,-i.2) t := by
        rw [show Fx V n i t = Fx V n t i from congr_fun (congr_fun (Fx_sym V n) t) i,Fx]; congr 1; exact congr_fun (congr_fun (F_sym V n) (i.1,-i.2)) t
    simp_rw [ hats_apply, Matrix.mul_apply,hx,Finset.sum_mul, Finset.mul_sum, mul_assoc ]
omit [Fintype I] [Fintype J] in
lemma measures_cov (e:I≃ T V)(d:J≃ T K)(W:Matrix I J ℂ)(M:Matrix (T V) (T K) ℂ)(i:T V)(j:T K) (h: Matrix.reindex e d W= F V n*M*F K n): hats e d W i j= vol n * M i (j.1,-j.2):= by
    have hu: M = Fx V n * ( Matrix.reindex e d W ) * Fx K n:= by rw [h]; simp_rw [← Matrix.mul_assoc, fwd_inv,Matrix.one_mul,Matrix.mul_assoc,inv_fwd,Matrix.mul_one]
    rw [hu]; have hy (t:T K): Fx K n t (j.1,-j.2)= scaleZ n* F K n t j := by unfold Fx; rw [neg_neg]
    rw [hats_apply, Matrix.mul_apply,Matrix.mul_apply]; simp_rw [hy, Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; rw [scale_factor, mul_left_comm _ ((vol n)⁻¹),mul_inv_cancel_left₀ (nonzero n)] -- signature
end YM.WilsonBridge.FiniteDFT
