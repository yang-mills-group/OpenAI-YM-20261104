import YM.SchemeConversionRG11.FirstW.Invoice.Axes
/-! Transfer quadratic and cubic stencil before taking mesh limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW.Deck
open Function Filter MeasureTheory ProbabilityTheory Set Lattice Pert Warp Topology Maxwell
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {r d : ℕ} (p : Players G r d) (o : Full.Grid n r) (h : ℝ)
lemma funds2 (B : FullT G n →ₗ[ℝ] FullT G n →ₗ[ℝ] ℝ) (A C : FullT G n) : B A C = ∑ u:Pr G n,∑ v:Pr G n, B (snow u) (snow v)*bead u A *bead v C := by
  nth_rw 1 [beads A]; nth_rw 1 [beads C]; simp only [map_sum,map_smul, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun j _=> by ring
lemma funds3 (B : Sky G (Per n)) (A C D : FullT G n) : B A C D = ∑ u:Pr G n,∑ v:Pr G n,∑ w:Pr G n, B (snow u) (snow v) (snow w)*bead u A*bead v C*bead w D := by
  rw [show B A C D = ∑ u:Pr G n,bead u A* B (snow u) C D from (by nth_rw 1 [beads A]; simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,smul_eq_mul])]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [funds2 _ _ _,Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _=>by ring
abbrev charged (f : FullT G n→ℝ) := ∫ x:Ribs G n r d,(↑(f (spanT x.fst)):ℂ)*spend (teams o h) (feed p) x ∂hall G n r d h
lemma two_cost (B : FullT G n→ₗ[ℝ] FullT G n→ₗ[ℝ] ℝ) (hp : ∀ x y : Pr G n,x.2=y.2 → B (snow x) (snow y)=0) : charged p o h (fun A=>B A A) = ∑ x:At G r d, ∑ y:At G r d, (B (cloudK h o x) (cloudK h o y):ℝ) * ZeroR o h (dict y (dict x p)) := by
  haveI := hall_G G n r d h
  let Y u := pick r d (bead (G:=G) (n:=n) u)
  let μ := hall G n r d h
  let f (u v:Pr G n) (x : Ribs G n r d):ℂ := ↑(B (snow u) (snow v))*(Y u x*(Y v x * spend (teams o h) (feed p) x))
  have he (u v:Pr G n) : Integrable (f u v) μ := price_tame (hall G n r d h) (Orb.Tame.mul (Orb.Tame.constant _) (Orb.Tame.mul (Orb.Tame.clm _) (Orb.Tame.mul (Orb.Tame.clm _) (spend_A ..))))
  have hi : charged p o h (fun A=>B A A) = ∫ x, ∑ u,∑ v,f u v x ∂μ := integral_congr_ae (Eventually.of_forall fun x =>by dsimp only; rw [funds2 B (spanT x.fst) _]; simp [f,Y, pick_roll, Finset.sum_mul,mul_assoc])
  have hh (u v:Pr G n) : (∫ x,f u v x ∂μ) = ↑(B (snow u) (snow v))* row2 h o p (bead u) (bead v) := integral_const_mul ..
  have hp0 u v: (↑(B (snow u) (snow v)):ℂ)*(pool (bead u) (bead v):ℝ)=0 := by
    by_cases he:u.2=v.2; · simp only [hp u v he,Complex.ofReal_zero,zero_mul]
    rw [pool_eq0 u v he,Complex.ofReal_zero,mul_zero]
  rw [hi,integral_finsetSum _ (fun u _=>integrable_finsetSum _ fun v _=>he u v)]
  simp_rw [integral_finsetSum _ (fun _ _=>he ..), hh, row2_print,mul_add,←mul_assoc,hp0,zero_mul,zero_add,Finset.mul_sum,←mul_assoc]
  let R (u v:Pr G n) x y := ↑(B (snow u) (snow v))* ↑(bead u (cloudK h o x))* ↑(bead v (cloudK h o y))* ZeroR o h (dict y (dict x p))
  conv_lhs => arg 2; intro u; rw [Finset.sum_comm]; arg 2; intro x; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]; arg 2; intro x; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [funds2 B]; simp only [Complex.ofReal_sum,Complex.ofReal_mul, Finset.sum_mul]
lemma abc_comm {I J : Type*} [Fintype I] [Fintype J] (r : I→I→I→J→J→J→ℂ) : ∑ i:I,∑ k:I,∑ t:I,∑ x:J,∑ y:J,∑ z:J,r i k t x y z = ∑ x:J,∑ y:J,∑ z:J,∑ i:I,∑ k:I,∑ t:I,r i k t x y z := by
  -- commute inner
  let f (i : I×I×I) (j : J×J×J):=r i.1 i.2.1 i.2.2 j.1 j.2.1 j.2.2
  have hd :(∑ i:I×I×I, ∑ j:J×J×J,f i j)=∑ j:J×J×J,∑ i:I×I×I,f i j:= Finset.sum_comm
  simp_rw [Fintype.sum_prod_type] at hd; exact hd
lemma three_cost (B : Sky G (Per n)) (hl : ∀ x y z,B x y z=B y x z) (hr : ∀ x y z,B x y z=B x z y) (hp : ∀ x y : Pr G n,x.2=y.2 → ∀ z,B (snow x) (snow y) z=0) :
    charged p o h (fun A=> B A A A) = ∑ i:At G r d,∑ j:At G r d,∑ k:At G r d, (B (cloudK h o i) (cloudK h o j) (cloudK h o k):ℝ)*ZeroR o h (dict k (dict j (dict i p))) := by
  haveI := hall_G G n r d h
  let Y u := pick r d (bead (G:=G) (n:=n) u)
  let μ := hall G n r d h
  let f (u v w:Pr G n) (x : Ribs G n r d):ℂ := ↑(B (snow u) (snow v) (snow w))*(Y u x*(Y v x*(Y w x * spend (teams o h) (feed p) x)))
  have he (u v w:Pr G n) : Integrable (f u v w) μ := price_tame (hall G n r d h) (Orb.Tame.mul (Orb.Tame.constant _) (Orb.Tame.mul (Orb.Tame.clm _) (Orb.Tame.mul (Orb.Tame.clm _) (Orb.Tame.mul (Orb.Tame.clm _) (spend_A ..)))))
  have hi : charged p o h (fun A=>B A A A) = ∫ x,∑ u,∑ v,∑ w,f u v w x ∂μ := integral_congr_ae (Eventually.of_forall fun x=> by dsimp only; rw [funds3 B (spanT x.fst) _ _]; simp [f,Y,pick_roll,Finset.sum_mul,mul_assoc])
  have hp0 (u v w:Pr G n) : (↑(B (snow u) (snow v) (snow w)):ℂ)*(pool (bead u) (bead v):ℝ)=0 := by
    by_cases hv:u.2=v.2; · simp only [hp u v hv,Complex.ofReal_zero,zero_mul]
    rw [pool_eq0 u v hv,Complex.ofReal_zero,mul_zero]
  let R (u v w:Pr G n) i j k := (↑(B (snow u) (snow v) (snow w)):ℂ)* ↑(bead u (cloudK h o i))* ↑(bead v (cloudK h o j))* ↑(bead w (cloudK h o k))* ZeroR o h (dict k (dict j (dict i p)))
  have hh (u v w:Pr G n) : (∫ x,f u v w x ∂μ) = ∑ i,∑ j,∑ k,R u v w i j k := by
     rw [show (∫ x,f u v w x ∂μ) = ↑(B (snow u) (snow v) (snow w))* row3 h o p (bead u) (bead v) (bead w) from integral_const_mul .., row3_print]; simp only [mul_add];
     have h0 : (↑(B (snow u) (snow v) (snow w)):ℂ)*(pool (bead u) (bead w):ℝ)=0:= by rw [hr, hp0]
     have h1 : (↑(B (snow u) (snow v) (snow w)):ℂ)*(pool (bead v) (bead w):ℝ)=0 := by rw [hl,hr,hp0]
     simp only [← mul_assoc,hp0,h0,h1,zero_mul,zero_add, Finset.mul_sum,R,Complex.ofReal_mul]
  rw [hi,integral_finsetSum _ (fun u _=>integrable_finsetSum _ fun v _=>integrable_finsetSum _ fun w _=>he u v w)]
  simp_rw [integral_finsetSum _ (fun _ _=>integrable_finsetSum _ fun _ _=>he ..), integral_finsetSum _ fun _ _=>he ..,hh]; rw [abc_comm R]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; rw [funds3 B (cloudK h o i)]; simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul];rfl
end YM.RG11.FirstW.Deck
