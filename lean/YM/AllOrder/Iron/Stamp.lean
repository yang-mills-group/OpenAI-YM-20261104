import YM.AllOrder.Iron.Size
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {i j k : Type} [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j] [Fintype k] [DecidableEq k]
-- influence from numerical entries; need no norm on gauge fixing inverse
lemma stage (H:Funds i)(F:Matrix j i ℝ)(G:Matrix i j ℝ)
    (hA:IsUnit (F*G).det)(hU:H*G=0)(hV:Hᵀ=H) {N:Funds i}(hN:IsUnit N.det)(hp:N=H+Fᵀ*F): H*N⁻¹*H=H:=by
 let A:=N⁻¹*H; have hh : N*A=H:= by rw [show A=N⁻¹*H from rfl, ← Matrix.mul_assoc, mul_nonsing_inv _ hN, one_mul]
 have hk : Gᵀ*H=0 := (by rw [← transpose_transpose (Gᵀ*H), transpose_mul, transpose_transpose, hV, hU, transpose_zero])
 have he : F * A=0 := by
    have hx : (F*G)ᵀ*(F*A)=0 := calc
      _ = Gᵀ *N*A := by rw [hp,transpose_mul,Matrix.mul_add,hk,zero_add]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Matrix.mul_assoc Gᵀ N,hh,hk]
    conv_lhs => rw [← Matrix.one_mul (F*A)]
    rw [← nonsing_inv_mul (F*G)ᵀ (by rwa [det_transpose]),Matrix.mul_assoc,hx, Matrix.mul_zero]
 rw [hp, Matrix.add_mul, Matrix.mul_assoc Fᵀ,he,Matrix.mul_zero,add_zero] at hh
 rw [Matrix.mul_assoc]; exact hh

omit [DecidableEq i] in
lemma post_plane [DecidableEq i]  (H:Funds i)(G:Matrix i j ℝ) (P:Matrix i k ℝ)
    (hU:H*G=0)(A:Matrix k i ℝ) (hB:A*P=1)(hC:A*G=0) (u:j⊕k ≃ i)(ho:IsUnit ((paste_sides G P).submatrix u id).det): H*P*A=H := by
   let M:=paste_sides G P; let B:=M.submatrix u id
   have he : H*P*A*M=H*M:=by
      unfold M; rw [sideProd, sideProd, Matrix.mul_assoc _ A _, hC,Matrix.mul_zero,hU, Matrix.mul_assoc _ A, hB,Matrix.mul_one]
   let T:=(H*P*A-H).submatrix u u; have hM : T*B=0:= by
      unfold T B; rw [submatrix_mul_equiv,Matrix.sub_mul,he,sub_self,submatrix_zero]; rfl
   have hX : T=0 := by
      rw [← Matrix.mul_one T, ← mul_nonsing_inv B ho, ← Matrix.mul_assoc, hM, Matrix.zero_mul]
   replace hX := congr_arg (fun M:Funds (j⊕k)=>M.submatrix u.symm u.symm) hX
   simp only [T,submatrix_submatrix,submatrix_zero,Equiv.self_comp_symm,submatrix_id_id] at hX
   exact sub_eq_zero.mp hX

lemma stands (H:Funds i)(F:Matrix j i ℝ)(G:Matrix i j ℝ)(P:Matrix i k ℝ)
    (hA:IsUnit (F*G).det)(hU:H*G=0)(hV:Hᵀ=H) {N:Funds i}(hN:IsUnit N.det)(hp:N=H+Fᵀ*F)
    (A:Matrix k i ℝ)(hB:A*P=1)(hC:A*G=0)(u:j⊕k ≃ i)(ho:IsUnit ((paste_sides G P).submatrix u id).det)
    (D:Funds k)(hk:D=Pᵀ*H*P)(hZ:IsUnit D.det): D⁻¹ = A*N⁻¹*Aᵀ:= by
   have he:= post_plane H G P hU A hB hC u ho
   have hx : D*A=Pᵀ*H:=by rw [hk,Matrix.mul_assoc Pᵀ H P,Matrix.mul_assoc,he]
   have hr : Dᵀ=D:=by rw [hk,transpose_mul,transpose_mul,hV,transpose_transpose,Matrix.mul_assoc]
   have hv : Aᵀ*D=H*P:=by simpa only [transpose_mul,hV,hr,transpose_transpose] using (congr_arg Matrix.transpose hx)
   have hf: D*(A*N⁻¹*Aᵀ)*D=D:=calc
     _=(Pᵀ*H)*N⁻¹*(H*P):= by rw [← hx,←hv]; simp only [Matrix.mul_assoc]
     _ = Pᵀ*(H*N⁻¹*H)*P:=by simp only [Matrix.mul_assoc]
     _ = D:= by rw [stage H F G hA hU hV hN hp,hk]
   have hg:= congr_arg (fun B=>D⁻¹*B*D⁻¹) hf
   change D⁻¹*(D*(A*N⁻¹*Aᵀ)*D)*D⁻¹ = _*_*_ at hg; simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul D hZ, Matrix.one_mul] at hg; rw [Matrix.mul_assoc _ D D⁻¹,mul_nonsing_inv D hZ, Matrix.mul_one] at hg; exact hg.symm
end YM.AllOrder.Iron
