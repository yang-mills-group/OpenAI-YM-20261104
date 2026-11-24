import YM.FormalBulk08.Wick.Filament

/-! Allow invertible changes already at order zero. Formula compares
normalized moments; determinant ratio at order zero is explicit. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series PowerSeries Matrix
open scoped BigOperators
variable {R V U : Type*} [CommRing R] [Algebra ℚ R] [Fintype V] [DecidableEq V] (T D : Saddle R V)
variable (L M : Matrix V V R) (hl : L*M=1) (hm : M*L=1) (h : L.transpose * D.P * L = T.P)
include hl hm h
omit [Algebra ℚ R] in
lemma slide_cov : L*T.q*L.transpose = D.q := by
   have he : (L*T.q*L.transpose)*D.P=1 := by
      have hc : D.P=M.transpose*T.P*M := by rw [←h,←mul_assoc,←mul_assoc,←transpose_mul,hl,transpose_one,one_mul,mul_assoc,hl,mul_one]
      rw [hc,←mul_assoc,←mul_assoc,mul_assoc _ L.transpose,←transpose_mul,hm,transpose_one,mul_one,mul_assoc L,mul_eq_one_comm.mpr T.inv,mul_one,hl]
   calc _ = (L*T.q*L.transpose)* (D.P*D.q) := by rw [D.inv,mul_one]
        _ = _ := by rw [←mul_assoc,he,one_mul]
omit hl hm in
lemma slide_base : mixRows L D.base=T.base := by
   let x (i:V) := MvPolynomial.X (R:=R) i
   let p (P : Matrix V V R) (y : V→Glyphs R V): Glyphs R V := ∑ i,∑ j, MvPolynomial.C (halve (P i j))*y i*y j
   have he : (mixRows L D.base)= -p D.P fun i=> ∑ j,MvPolynomial.C (L i j)*x j := by simp [mixRows,x,p,Saddle.base]
   rw [he,show T.base= -p T.P x from rfl,←h];congr 1
   unfold p;unfold halve; simp_rw [Matrix.mul_apply, transpose_apply,Finset.sum_mul,Finset.mul_sum,_root_.map_sum, Finset.sum_mul]
   -- rotate sums of same V
   have sw (f : V→V→V→V→Glyphs R V) : ∑ a,∑ b,∑ c,∑ d,f a b c d=∑ d,∑ c,∑ b,∑ a,f a b c d := by
      simp_rw [Finset.sum_comm (f:=fun c d=> f _ _ c d)]
      simp_rw [Finset.sum_comm (f:=fun b d=> ∑ c,f _ b c d)]
      rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro d _
      simp_rw [Finset.sum_comm (f:=fun b c => f _ b c d)]
      rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro c _; rw [Finset.sum_comm]
   rw [sw];apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _; apply Finset.sum_congr rfl;intro a _;apply Finset.sum_congr rfl; intro b _; simp only [map_mul];ring
lemma slide_series (F : Plate R V) : beam T.call (PowerSeries.map (mixRows L).toRingHom F)=beam D.call F := by
   have he := slide_cov T D L M hl hm h
   have hp (i j:V):D.q i j=∑ u,∑ v,L i u*L j v*T.q u v := by
       rw [← he];simp_rw [Matrix.mul_apply,transpose_apply,Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
   ext1 n; simp only [coeff_beam, coeff_map]; exact slide_trail T.q D.q L T.ok D.ok hp _
end YM.FormalBulk08.Wick
