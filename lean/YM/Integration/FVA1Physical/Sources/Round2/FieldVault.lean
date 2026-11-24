import YM.Integration.FVA1Physical.Sources.Round2.SchurWickRows
import YM.Integration.FVA1Physical.Wilson.DistributedScores

/-! A fixed polynomial in the literal physical stencil slots, placed anywhere on the
torus, has a rooted Whisk budget controlled only by its finite slot prices. Repeated
slots may coincide on the torus. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock
open scoped Classical Topology BigOperators

private theorem variable_vault {σ : Type} [Fintype σ] [DecidableEq σ] {side : Side}
    (l : σ→Site side) (a : ℝ) (s m : ℕ) (j : σ) :
    Vault l {l j} a s m 0 (MvPolynomial.X j) 1 := by
  refine ⟨zero_le_one,fun k _=>?_⟩
  cases k with
  | zero =>
    rw [lump,twillz,rate]
    change _ * |MvPolynomial.eval (0:View σ) (MvPolynomial.X j)| ≤ 1
    simp
  | succ k =>
    rw [Whisk.down,Finset.sum_eq_single j]
    · rw [MvPolynomial.pderiv_X_self,Finset.insert_eq_of_mem (mem_singleton_self _)]
      simpa only [MvPolynomial.C_1,abs_one] using
        (Bout.VaultC (j:=l) (z:=l j) (a:=a) (s:=s) (p:=k) (x:=0) (1:ℝ)).2 k le_rfl
    · intro i _ ne
      rw [MvPolynomial.pderiv_X_of_ne (by first | exact ne | exact ne.symm),lump.zeroL]
    · simp

/-- Bounds a fixed stencil before its map into a changing periodic coordinate
space is chosen. The exponent and constant depend on the fixed polynomial and
derivative depth; neither depends on the ambient number of variables. -/
theorem fixed_polynomial_vault {τ : Type} (pol : Pot τ) (m : ℕ) :
    ∃ (B:ℝ) (e:ℕ), 0≤B ∧ ∀ {σ : Type} [Fintype σ] [DecidableEq σ] {side : Side}
      (l : σ→Site side) (z : Site side) (i : τ→σ) (s : ℕ) (a w:ℝ), 0≤a → 1≤w →
      (∀ k,liftW a s (separation z (l (i k)))≤w) →
      Vault l {z} a s m 0 (MvPolynomial.rename i pol) (B*w^e) := by
  induction pol using MvPolynomial.induction_on with
  | C c =>
    refine ⟨|c|,0,abs_nonneg _,?_⟩
    intro σ fi de side l z i s a w ha hw near
    simpa using (Bout.VaultC (j:=l) (z:=z) (a:=a) (s:=s) (p:=m) (x:=0) c)
  | add f g hf hg =>
    obtain ⟨B,b,hB,fb⟩:=hf;obtain ⟨C,c,hC,gc⟩:=hg
    refine ⟨B+C,b+c,add_nonneg hB hC,?_⟩
    intro σ fi de side l z i s a w ha hw near
    rw [_root_.map_add,add_mul]
    exact Quote.widen (Quote.addN (fb l z i s a w ha hw near) (gc l z i s a w ha hw near))
      (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (by omega)) hB)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (by omega)) hC)) le_rfl
  | mul_X f u hf =>
    obtain ⟨B,e,hB,buy⟩:=hf
    refine ⟨2^m*B,e+1,mul_nonneg (by positivity) hB,?_⟩
    intro σ fi de side l z i s a w ha hw near
    rw [_root_.map_mul,MvPolynomial.rename_X]
    have vx:=Bout.tau (y:=z) ha (variable_vault l a s m (i u))
    rw [mul_one] at vx
    have both:=Bout.stock ha (buy l z i s a w ha hw near) (Quote.widen vx (near u) le_rfl)
    convert both using 1
    rw [pow_succ];ring

variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)
theorem lampRow_degree (part : Bool) (A : Finset (Slice J)) (j : ℕ) :
    (lampRow J part A j).totalDegree ≤ j := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [MvPolynomial.totalDegree_C,Nat.zero_add]
  simpa using MvPolynomial.totalDegree_finsetProd Finset.univ (fun k=> MvPolynomial.X (R:=ℝ) (i k))

end YM.Integration.FVA1Physical.Round2.Curvature
