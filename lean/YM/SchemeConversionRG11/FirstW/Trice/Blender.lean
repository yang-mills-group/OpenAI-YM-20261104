import YM.SchemeConversionRG11.FirstW.Trice.Flight
import YM.Pert.Triangle.Feynman
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open Next.Rank.Normal MvPolynomial
open scoped Topology ContDiff BigOperators Classical
variable {I:Type*} {G:Gauge}
section gauge
variable (Q: Next.Rank.Normal.Symmetric I) {J:Type*}[Fintype J]
lemma blendedTwo (i j : I) : blend Q 0 (X i*X j)=Q.cov i j:=by rw [blended,slit_X, Pi.zero_apply,zero_mul,zero_add, show MvPolynomial.C _= (Q.cov i j) • (1:poly I) from by simp [smul_eq_C_mul],map_smul,Next.Rank.Normal.fresh]; simp
lemma baked (i j k l:I): blend Q 0 (X i*X j*X k*X l)=Q.cov i j*Q.cov k l+Q.cov i k* Q.cov j l+ Q.cov i l* Q.cov j k:=by
 simp only [mul_assoc,blended,Pi.zero_apply,zero_mul,zero_add]; let J(i j:I):poly I:=MvPolynomial.C (Q.cov i j)
 have hw: slit (Q.cov i) (X j*(X k* X l))= J i j * (X k * X l)+J i k *(X j* X l)+J i l*(X j* X k):= by rw [slit_prod,slit_prod,slit_X]; unfold J; ring
 rw [hw]; simp only [J,C_mul',map_add,map_smul,blendedTwo,smul_eq_mul]
-- lift any linear form whose occurrences in finite J
end gauge
variable {n :ℕ}
structure Bend (G:Gauge)(n:ℕ) where
 B: Badge G
 j: Fin n
 b: Bool
abbrev prob (w:Bend G n) := probe w.b w.B.1 w.B.2
def dynasty (w:Bend G n) := rename (Prod.mk w.j) (symbol 0 (prob w))
def lux (x:Points n)(u v: Bend G n):ℂ:= if u.j=v.j then 0 else (legKernel (prob u) (prob v) (x u.j-x v.j):ℝ)
abbrev Coin (t:Bend G n)(j:Fin (legDim G 0)) : ℂ:= ↑(prob t (frame G 0 j))
def lensP (t:Bend G n)(i:Fin (legDim G 0)): Fin n ×Slot G:=(t.j, ⟨0,i⟩)
lemma dynastyP (w:Bend G n): dynasty w= ∑ j:Fin (legDim G 0),Coin w j • MvPolynomial.X (lensP w j) := by unfold dynasty symbol; simp_rw [map_sum,map_mul, rename_X]; exact Finset.sum_congr rfl fun i h=> by rw [rename_C,C_mul'];rfl
variable {p:Points n}(h:p∈conf n)
lemma pearl (u v: Bend G n){x:E4}(e:x≠0): legKernel (prob u) (prob v) x=(∑ i:Fin (legDim G 0),∑ j:Fin (legDim G 0), (prob u) (frame G 0 i)*prob v (frame G 0 j)*legKernel (coordinateLeg (lensP u i).2) (coordinateLeg (lensP v j).2) x) := by
 let P (w:Bend G n)(i:Fin (legDim G 0)):=prob w (frame G 0 i)
 have hv(w:Bend G n): prob w= ∑ i:Fin (legDim G 0),P w i • coordinateLeg (lensP w i).2:= by exact Receipt.probe_by_components 0 _
 let L:= Maxwell.pairing (G:=G) (j:=0) (l:=0) (show x∈away from e)
 change L (prob u) (prob v) = ∑ i,∑ j, P u i*P v j* L _ _
 nth_rw 1 [hv u,hv v]; simp only [map_sum,LinearMap.sum_apply]
 have he (a b:ℝ)(s t:Probe G 0): L (a • s) (b • t)= a*b*L s t:= by simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]; ring
 rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> he (P u i) (P v j) (coordinateLeg (lensP u i).2) (coordinateLeg (lensP v j).2)
include h
lemma lux_eq (u v:Bend G n): lux p u v= ∑ i:Fin (legDim G 0),∑ j:Fin (legDim G 0), Coin u i * Coin v j * (frameX h).cov (lensP u i) (lensP v j) := by
 by_cases hp:u.j=v.j; · simp [lux,hp,frameX,lensP]
 unfold lux; rw [if_neg hp,pearl u v (sub_ne_zero.mpr (h.ne hp))]; simp_rw [ofReal_sum,ofReal_mul,frameX,lensP,if_neg hp]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; rfl
lemma lit_2 (u v: Bend G n) : blend (frameX h) 0 (dynasty u * dynasty v) = lux p u v := by rw [lux_eq h,dynastyP,dynastyP];simp_rw [Finset.sum_mul, Finset.mul_sum]; simp only [smul_mul_assoc,mul_smul_comm, map_sum, map_smul,blendedTwo,smul_eq_mul]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> by ring
lemma lit_4 (u v w z: Bend G n) : blend (frameX h) 0 (dynasty u * dynasty v*dynasty w*dynasty z) = lux p u v*lux p w z+ lux p u w*lux p v z + lux p u z * lux p v w := by
 simp only [dynastyP,Finset.sum_mul,Finset.mul_sum];
 conv_lhs =>
    arg 2
    rw [Finset.sum_comm]; arg 2; intro w
    rw [Finset.sum_comm]; arg 2; intro v
    rw [Finset.sum_comm]
 conv_lhs=>
    arg 2; rw [Finset.sum_comm]; arg 2; intro v
    rw [Finset.sum_comm]
 conv_lhs=> arg 2; rw [Finset.sum_comm]
 simp only [smul_mul_assoc, mul_smul_comm, map_sum, map_smul,baked,smul_eq_mul, mul_add,Finset.sum_add_distrib]
 -- sum alignment helper tails
 let H:= frameX (G:=G) h
 let e(a b:Bend G n)(i j:Fin (legDim G 0)):=Coin a i*Coin b j*H.cov (lensP a i) (lensP b j)
 rw [lux_eq h u v, lux_eq h w z, lux_eq h u w,lux_eq h v z,lux_eq h u z,lux_eq h v w]; simp_rw [Finset.sum_mul,Finset.mul_sum]; -- inspect
 apply congrArg₂ (·+·)
 · apply congrArg₂ (·+·)
   · exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun c _=>Finset.sum_congr rfl fun d _=> by ring
   conv_rhs => arg 2; intro i; rw [Finset.sum_comm]
   exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun c _=>Finset.sum_congr rfl fun d _=> by ring
 conv_rhs=>
    arg 2; intro a
    rw [Finset.sum_comm]
    arg 2; intro b
    rw [Finset.sum_comm]
 exact Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=>Finset.sum_congr rfl fun c _=>Finset.sum_congr rfl fun d _=> by ring
omit h
lemma mixed_probe (a b: Badge G){x:E4}(hx:x≠0): legKernel (probe true a.1 a.2) (probe false b.1 b.2) x= if a.2=b.2 then mixed a.1 b.1 x else 0:= by
 let P:= Maxwell.pairing (G:=G) (j:=0) (l:=0) (show x∈away from hx)
 -- show kernels curl as in Triangle.ShellFan
 have hp (u v i j:Axis) : P (UVNext.FreeStress.curlProbe (UVNext.FreeStress.initialPlace u v) a.2) (UVNext.FreeStress.curlProbe (UVNext.FreeStress.initialPlace i j) b.2)= if a.2=b.2 then bareCurl u v i j x else 0:= by unfold UVNext.FreeStress.curlProbe P; rw [Maxwell.raw_mixed _ _ _ _ _ _ _ _ hx]; simp only [Tensor.coeff_apply_zero,pow_zero,one_mul]
 change P _ _ = _
 unfold Triangle.probe; rw [map_smul,map_sum]; simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,smul_eq_mul]; simp_rw [hp]; split_ifs with h
 · simp only [mixed]; simp_rw [Finset.mul_sum]; -- lhs reversed indices
   have e(f:Axis→Axis→Axis→Axis→ℝ): (∑ i:Axis,∑ j:Axis,∑ k:Axis,∑ l:Axis,f i j k l)=∑ k:Axis,∑ l:Axis,∑ i:Axis,∑ j:Axis,f i j k l:= by simpa only [Fintype.sum_prod_type] using! Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun p q:Axis×Axis=> f p.1 p.2 q.1 q.2)
   rw [e (fun i j k l=> ((2:ℝ)⁻¹ * (fan false b.1 i j * ((2:ℝ)⁻¹ * (fan true a.1 k l * bareCurl k l i j x)))))]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>Finset.sum_congr rfl fun k _=>Finset.sum_congr rfl fun l _=> by ring
 simp only [mul_zero, Finset.sum_const_zero]
end YM.RG11.FirstW.Branch
