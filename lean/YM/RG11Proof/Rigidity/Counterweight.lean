import YM.RG11Proof.Rigidity.Equator

/-!
# Saturated weights at the marked positions
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free palette Strip Crowd Function Filter Set
open scoped BigOperators Topology Classical

variable {G : Gauge} {P : Type*} [Fintype P]

def bank (Θ : P→Stream) (t : ℝ) : P→Stream := fun i x j => t⁻¹^(2+j) • Θ i x j
lemma deal (Θ : P→Stream) (t : ℝ) (a b : Pig G) : dial (bank Θ t) a b=t⁻¹^(weightF a + weightF b) * dial Θ a b := by
  unfold dial bank weightF conduit
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
  split_ifs <;> try simp
  rw [pow_add]; ring

/-- Undress everything already attached by poles; rate left only on the
unmarked primaries. -/
def unpaid (Θ:P→Stream) (t : ℝ) : ℕ→ Word G → ℝ
  | 0, L=> t^(cargo L) * meter L
  | k+1,L=> nick (dial Θ) (unpaid Θ t k) L

lemma banksOut (Θ:P→Stream) (t : ℝ) (ht : t≠0) (m : ℕ) (L : Word G) :
    t^(cargo L) * sensors (bank Θ t) m L=unpaid Θ t m L := by
  induction m generalizing L with
  | zero=>rfl
  | succ m h=>
    rw [sensors_step,unpaid]; unfold nick pulls; simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
    let q := L.eraseIdx i.val; let v := q.eraseIdx j.val
    rw [deal,cargo_pick _ i,cargo_pick q j,← add_assoc, pow_add, inv_pow]
    rw [mul_mul_mul_comm]; unfold q; rw [← mul_assoc (t^_) ((t^_)⁻¹), mul_inv_cancel₀ (pow_ne_zero _ ht),one_mul,h]

lemma unpaid_cont (Θ:P→Stream) (m : ℕ) (L : Word G) : Continuous (fun t=> unpaid Θ t m L) := by
  induction m generalizing L with
  | zero=> exact (continuous_pow _).mul continuous_const
  | succ m h=>
    unfold unpaid nick pulls; exact continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> continuous_const.mul (h _)

def payout : ℕ→ℝ
  | 0=> 1
  | m+1=> (2*(m+1:ℕ) : ℝ)* payout m
lemma payout_pos (m) : 0<payout m := by induction m with | zero=> exact zero_lt_one | succ m h=> unfold payout; positivity

-- an averaged first occurrence recursion.
lemma circuits {I:Type*}(E : I→I→ℝ) (h : ∀ i j,E i j=E j i) (L : List I) : Strip.nick E (pairCost E) L=
    (L.length:ℝ)*pairCost E L := by
  unfold Strip.nick
  have he (i : Fin L.length) : pulls (L.eraseIdx i.val) (fun b r=>E (L.get i) b*pairCost E r)=pairCost E L := by
    rw [← pair_step]; exact pair_perm E h (by simpa using List.getElem_cons_eraseIdx_perm (l:=L) i.isLt)
  unfold pulls at he ⊢; dsimp only at he ⊢; simp_rw [he]; simp

lemma cargo_tapped (L : Word G) (h : L≠[]) : 0<cargo L := by cases L <;> simp_all [cargo,weightF]
lemma receive (Θ:P→Stream) (m : ℕ) (L : Word G) : unpaid Θ 0 m L=
    payout m * if List.length L=2*m then pairCost (dial Θ) L else 0 := by
  induction m generalizing L with
  | zero=>
    by_cases h : L=[]
    · subst L; simp [unpaid,cargo,meter,pairCost,payout]
    simp [unpaid,zero_pow (cargo_tapped L h).ne',h]
  | succ m ih=>
    have he (i : Fin (List.length L)) (j : Fin (List.length (L.eraseIdx i.val))) :
        ((L.eraseIdx i.val).eraseIdx j.val).length+2=L.length := by
      have := List.length_eraseIdx_add_one i.isLt
      have := List.length_eraseIdx_add_one j.isLt
      omega
    unfold unpaid nick pulls; simp_rw [ih]
    split_ifs with h
    · have hk (i : Fin (List.length L)) (j : Fin (List.length (L.eraseIdx i.val))): ((L.eraseIdx i.val).eraseIdx j.val).length=2*m:=by have := he i j; omega
      simp_rw [hk,if_true, mul_left_comm _ (payout m),← Finset.mul_sum]
      change payout m * nick _ _ _= _
      rw [circuits (dial Θ) (dial_sym Θ) L,h,payout]; push_cast; ring
    rw [mul_zero]; apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _; rw [if_neg (by have:=he i j; omega)]; ring

end YM.RG11.Rigidity
