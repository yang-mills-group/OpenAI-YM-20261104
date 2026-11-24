import YM.Integration.WilsonReceivedCenteredGrade

/-! Only the two genuine singleton coefficients can overflow the total degree
when reconstructing an ordinary pair from the finite connected polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentOrdinaryPairGrade
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

def slot (s : R.Mode) (p : Truncated R) : Polynomial ℂ :=
  ∑ i∈p.support, Polynomial.monomial i ((p.coeff i).part s)

omit [Fintype V] in
theorem coeff_slot (s : R.Mode) (p : Truncated R) (j : ℕ) :
    (slot s p).coeff j = (p.coeff j).part s := by
  unfold slot
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  by_cases hj : j∈p.support
  · rw [sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · exact fun hn => (hn hj).elim
  · rw [Polynomial.notMem_support_iff.mp hj, Poly.part_nil]
    exact sum_eq_zero (fun b hb => if_neg (by intro he; subst b; exact hj hb))

omit [Fintype V] in
theorem read_slot (s : R.Mode) (p : Truncated R) (z : ℂ) :
    (slot s p).eval z = (formula z p).part s := by
  rw [slot,Polynomial.eval_finsetSum,formula_sum,Poly.part_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_monomial,Poly.part_smul,mul_comm]

private theorem room (s : R.Mode) : s.val.card≤Fintype.card V+r :=
  (Finset.card_le_univ s.val).trans (Nat.le_add_right ..)

theorem single (x : Grade R r) (unit : UnitLeading x) (a : V) :
    let P := render (ratio x)
    slot (R.fire a) (logSeries (Fintype.card V+r) P)=slot (R.fire a) P := by
  intro P
  apply Polynomial.funext
  intro z
  rw [read_slot,read_slot,formula_log]
  have quiet : (formula z P).part R.quiet=1 := (value_render z (ratio x)) ▸ leading_trunc_value (ratio_pure unit) z
  rw [←log_to (formula z P) quiet _ room]
  exact lamp a _ quiet

theorem pair (x : Grade R r) (unit : UnitLeading x) (a b : V) (s : R.Mode)
    (distinct : a≠b) (ab : s.val={a,b}) :
    let P := render (ratio x)
    slot s (logSeries (Fintype.card V+r) P) = slot s P - slot (R.fire a) P * slot (R.fire b) P := by
  intro P
  apply Polynomial.funext
  intro z
  rw [read_slot,Polynomial.eval_sub,Polynomial.eval_mul,read_slot,read_slot,read_slot,formula_log]
  have quiet : (formula z P).part R.quiet=1 := (value_render z (ratio x)) ▸ leading_trunc_value (ratio_pure unit) z
  rw [←log_to (formula z P) quiet _ room]
  exact twins a b s _ quiet distinct ab

def partialValue (d : ℕ) (z : ℂ) (p : Polynomial ℂ) :=
  ∑ j∈range (d+1), z^j*p.coeff j

private theorem sub_value (d : ℕ) (z : ℂ) (p q : Polynomial ℂ) :
    partialValue d z (p-q) = partialValue d z p-partialValue d z q := by
  simp [partialValue,mul_sub,sum_sub_distrib]

theorem stamped (s : R.Mode) (p : Truncated R) (z : ℂ) :
    (value z (stamp R r p)).part s = partialValue r z (slot s p) := by
  rw [vpart,partialValue]
  refine sum_congr rfl fun j hj => ?_
  rw [←series_poly R r p,observation R r _ (Nat.le_of_lt_succ (mem_range.mp hj)),
    Polynomial.coeff_coe,coeff_slot]

theorem overflow (x : Grade R r) (unit : UnitLeading x) (sym : Symmetric x) (g : ℂ)
    (a b c : V) (s : R.Mode) (diff : a≠b) (ab : s.val={a,b}) :
    let P := render (ratio x)
    let product := slot (R.fire a) P * slot (R.fire b) P
    let Z := value g (ratio x)
    let L := value g (logMarked x)
    (L.part s-L.part (R.fire c)+L.part (R.fire a)*L.part (R.fire b)) -
      (Z.part s-Z.part (R.fire c)) = product.eval g - partialValue r g product := by
  intro P product Z L
  let B := logSeries (Fintype.card V+r) P
  have restore : stamp R r P=ratio x := rerender (sym_ratio unit sym)
  have vacuum := ratio_quiet unit
  have filed : stamp R r B = logMarked x := by
    change stamp R r (logSeries (Fintype.card V+r) P) = logMarked x
    rw [stamp_log,restore,logMarked,log_to (ratio x) vacuum (Fintype.card V+r)
      (room_for (Fintype.card V) (fun t => Finset.card_le_univ t.val))]
  have original (t : R.Mode) : Z.part t = partialValue r g (slot t P) :=
    (congrArg (fun Q : Grade R r => (value g Q).part t) restore.symm).trans (stamped t P g)
  have logged (t : R.Mode) : L.part t = partialValue r g (slot t B) :=
    (congrArg (fun Q : Grade R r => (value g Q).part t) filed.symm).trans (stamped t B g)
  have one (i : V) : L.part (R.fire i)=Z.part (R.fire i) := by
    rw [logged,original]
    exact congrArg (partialValue r g) (single x unit i)
  have all : slot s B = slot s P-product := pair x unit a b s diff ab
  have two : L.part s=Z.part s-partialValue r g product := by
    rw [logged,original,all,sub_value]
  have full : product.eval g=Z.part (R.fire a)*Z.part (R.fire b) := by
    change (slot (R.fire a) P * slot (R.fire b) P).eval g=_
    rw [Polynomial.eval_mul,read_slot,read_slot]
    exact congrArg₂ (·*·)
      (congrArg (fun Q : Poly R => Q.part (R.fire a)) (value_render g (ratio x)).symm)
      (congrArg (fun Q : Poly R => Q.part (R.fire b)) (value_render g (ratio x)).symm)
  rw [two,one,one,one,full]
  ring

def mass (p : Polynomial ℂ) := ∑ i∈p.support, ‖p.coeff i‖

private def partialRead (r : ℕ) (z : ℂ) : Polynomial ℂ →+ ℂ where
  toFun := partialValue r z
  map_zero' := by simp [partialValue]
  map_add' p q := by simp [partialValue,mul_add,sum_add_distrib]

private theorem finite_monomial (r n : ℕ) (z c : ℂ) :
    partialRead r z (Polynomial.monomial n c) = if n≤r then z^n*c else 0 := by
  change ∑ i∈range (r+1), z^i*(Polynomial.monomial n c).coeff i = _
  simp only [Polynomial.coeff_monomial,mul_ite,mul_zero,sum_ite_eq,mem_range]
  simp only [Nat.lt_succ_iff]

private theorem multiply (A B : Polynomial ℂ) : A*B =
    ∑ i∈A.support, ∑ j∈B.support, Polynomial.monomial (i+j) (A.coeff i*B.coeff j) := by
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_mul,Polynomial.eval_finsetSum,Polynomial.eval_monomial,pow_add]
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  change (∑ i∈A.support, A.coeff i*z^i)*(∑ j∈B.support, B.coeff j*z^j) = _
  rw [sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  ring

theorem product_tail (r : ℕ) (A B : Polynomial ℂ) (z : ℂ) :
    (A*B).eval z-partialValue r z (A*B) =
      ∑ i∈A.support, ∑ j∈B.support, if r < i+j then z^(i+j)*(A.coeff i*B.coeff j) else 0 := by
  change (A*B).eval z-partialRead r z (A*B)=_
  rw [multiply A B]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial,map_sum,finite_monomial]
  rw [←sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [←sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases earlier : i+j≤r
  · rw [if_pos earlier,if_neg (Nat.not_lt.mpr earlier),mul_comm,sub_self]
  · rw [if_neg earlier,if_pos (Nat.lt_of_not_ge earlier),sub_zero,mul_comm]

theorem product_price (r : ℕ) (A B : Polynomial ℂ) (z : ℂ) (small : ‖z‖≤1) :
    ‖(A*B).eval z-partialValue r z (A*B)‖ ≤ ‖z‖^(r+1)*(mass A*mass B) := by
  rw [product_tail]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i∈A.support, ∑ j∈B.support, ‖z‖^(r+1)*(‖A.coeff i‖*‖B.coeff j‖) := by
      refine sum_le_sum fun i _ => (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
      by_cases later : r < i+j
      · rw [if_pos later,norm_mul,norm_pow,norm_mul]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt later)
        rw [hk,pow_add]
        exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg z) _) (pow_le_one₀ (norm_nonneg z) small)
      · rw [if_neg later,norm_zero]
        positivity
    _ = ∑ i∈A.support, ‖z‖^(r+1)*(‖A.coeff i‖*mass B) := by
      refine sum_congr rfl fun i _ => ?_
      simp only [mass,mul_sum]
    _ = _ := by rw [←mul_sum]; simp only [mass,sum_mul]

end YM.Integration.WilsonIndependentOrdinaryPairGrade

