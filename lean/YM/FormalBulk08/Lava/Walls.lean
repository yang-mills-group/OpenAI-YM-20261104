import YM.FormalBulk08.Lava.Tiles

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lava
open Series Wick Orb Function
open MvPolynomial
open scoped BigOperators Classical
variable {V : Type*}
-- permutation sending head fixed and permutes tail
private def sweep {r : ℕ} (s : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) where
   toFun := Fin.cases 0 (Fin.succ ∘ s)
   invFun := Fin.cases 0 (Fin.succ ∘ s.symm)
   left_inv i := by cases i using Fin.cases <;> simp
   right_inv i := by cases i using Fin.cases <;> simp
def shed {r : ℕ} (T : Tile V (r+1)) (a : V) : Tile V r := fun v => T (Fin.cons a v)
lemma Agate.shed {r : ℕ} {T : Tile V (r+1)} (h : Agate T) (a : V) : Agate (shed T a) := by
   intro v t; convert h (Fin.cons a v : chain V (r+1)) (sweep t) using 1
   rw [_root_.YM.FormalBulk08.Lava.shed]; congr 1; funext i; cases i using Fin.cases <;> simp [sweep]
   rfl
lemma shed_swap {r : ℕ} {T : Tile V ((r+1)+1)} (h : Agate T) (a b : V) : shed (shed T a) b=shed (shed T b) a := by
   funext v; let w : chain V ((r+1)+1) := Fin.cons b (Fin.cons a v)
   refine Eq.trans ?_ (h w (Equiv.swap 0 (Fin.succ 0)))
   change T (_)= T _; congr 1; funext i; refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=> ?_) j) i
   · simp [w]
   · simp [w]
   rw [comp_apply,Equiv.swap_apply_of_ne_of_ne (by simp) (fun hx=>Fin.succ_ne_zero _ (Fin.succ_injective _ hx))]; simp [w]

variable [Fintype V]
lemma facade_peels {r : ℕ} (T : Tile V (r+1)) : facade _ T = ∑ i,X i * facade _ (shed T i) := by
   simp_rw [facade_eq, Finset.mul_sum]; rw [← Fintype.sum_prod_type']; symm
   refine Fintype.sum_equiv (Fin.consEquiv (fun _:Fin (r+1) => V)) _ _ fun i=>?_
   change X _*(C _*_) = C _ * cards (Fin.cons i.1 i.2 : chain V (r+1)); rw [cards_cons]
   change X _*(C _*_) = C (shed T i.1 i.2)*(X _*_); ring
lemma facade_slope {r : ℕ} (i:V) {T : Tile V (r+1)} (h : Agate T) : pderiv i (facade _ T)= C ((r+1:ℕ):ℝ) * facade _ (shed T i) := by
   rw [facade_peels,map_sum]; simp only [pderiv_mul, pderiv_X,Pi.single_apply,ite_mul,one_mul,zero_mul, Finset.sum_add_distrib]
   simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
   induction r with
   | zero=>
      have hu (a:V) := homogeneousComponent_eq_self (facade_grade 0 (shed T a))
      simp_rw [homogeneousComponent_zero] at hu; have he (a:V) : pderiv i (facade _ (shed T a))=0:= by rw [←hu a,pderiv_C];
      simp_rw [he]; simp
   | succ r ih =>
      -- induction rewrote slope into sum form? goal
      have he (a : V) : pderiv i (facade _ (shed T a)) = C ((r+1:ℕ):ℝ)*facade _ (shed (shed T i) a) := by
         rw [shed_swap h i a]; specialize ih (h.shed a); nth_rw 1 [facade_peels]; simpa [pderiv_mul, map_sum,Pi.single_apply,ite_mul,Finset.sum_add_distrib,add_comm] using ih
      have hh : ∑ j,X j * pderiv i (facade _ (shed T j))= C ((r+1:ℕ):ℝ)*facade _ (shed T i) := by simp_rw [he]; nth_rw 1 [facade_peels (shed T i)]; simp_rw [Finset.mul_sum,mul_left_comm (X _)]
      rw [hh]; simp; ring

/-- Partial evaluation for factorial readout: no implicit `0^0`. -/
def climb : (r : ℕ) → TypeR V → Tile V r
    | 0, P => fun _ => coeff 0 P
    | _+1,P => fun v=>climb _ (pderiv (v 0) P) (Fin.tail v)
omit [Fintype V] in lemma climb_C_mul (r : ℕ) (a : ℝ) (P : TypeR V) : climb r (C a*P)= a • climb r P := by
    induction r generalizing P with
    | zero=> funext i; simp [climb]
    | succ r ih=> funext i; simp only [climb,pderiv_C_mul,ih,Pi.smul_apply]

lemma climb_read {r : ℕ} {T : Tile V r} (h : Agate T) : climb _ (facade _ T)=(Nat.factorial r:ℝ) • T := by
   induction r with
   | zero=> funext i; simp [facade_eq,cards,climb]; congr; exact Subsingleton.elim ..
   | succ r ih=> funext i; simp only [climb]; rw [facade_slope _ h,climb_C_mul,ih (h.shed _)]; simp [shed,Nat.factorial_succ,mul_assoc]
lemma facade_unique {r : ℕ} {T S : Tile V r} (h : Agate T) (g : Agate S) (e : facade _ T=facade _ S) : T=S :=
   (smul_right_injective _ (by positivity : (Nat.factorial r : ℝ)≠0)) <| by dsimp only; rw [←climb_read h,←climb_read g,e]
end YM.FormalBulk08.Lava
