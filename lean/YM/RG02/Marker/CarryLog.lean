import YM.RG02.Marker.Cost

/-!
# Log series after conditioning

Formal identity and eval estimate. After division the entire vacuum
*series* is 1, so now only the number of remaining marks limits the nil
Taylor formula. Price never treats the Pi norm on these evaluated tables
as the history norm. These estimates at one configuration are useful
coefficient algebra, not themselves the support-weighted derivative bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Evaluation
open Marker Extra.Trajectories Finset Grade PowerSeries Marks
open scoped BigOperators
variable {ι : Type} [DecidableEq ι] {B : Census ι} {w : ι→ℝ} {x : Script B}

lemma nil_down (hx : den x = 0) (n k : ℕ) (s : B.Mode) (hs : s.val.card<k) :
    (coeff n (x^k)).part s=0 := by
  induction k generalizing n s with
  | zero => omega
  | succ k ih =>
    rw [pow_succ,PowerSeries.coeff_mul,Poly.part_sum]; refine sum_eq_zero fun i _ => ?_
    rw [Poly.part_mul]; refine sum_eq_zero fun p _ => sum_eq_zero fun q _ => ?_
    split
    next h =>
      by_cases hq : q=B.quiet
      · rw [hq,show (coeff i.2 x).part B.quiet=0 by
          change blank B (coeff i.2 x)=0
          rw [← PowerSeries.coeff_map,← den,hx,map_zero],mul_zero]
      have he : 0<q.val.card := card_pos.mpr (nonempty_iff_ne_empty.mpr fun H => hq (Subtype.ext H))
      have hb : p.val.card+q.val.card=s.val.card := by rw [← card_union_of_disjoint h.1,h.2]
      rw [ih _ _ (by omega),zero_mul]
    rfl

section Fin
variable [Fintype ι]

lemma trunc_nil (hx : den x=0) (k : ℕ) (hk : Fintype.card ι<k) : x^k=0 := by
  ext i s; simp only [map_zero,Poly.part_nil]
  exact nil_down hx i k s (lt_of_le_of_lt (card_le_univ _) hk)

theorem only_marked (hx : den x=0) : exponential x =
    ∑ i∈range (Fintype.card ι+1),(i.factorial:ℂ)⁻¹ • x^i := by
  apply PowerSeries.ext; intro j
  rw [exponential,PowerSeries.coeff_mk,map_sum,map_sum]
  symm; refine sum_subset (range_mono (by omega)) ?_
  intro i _ he
  rw [trunc_nil hx i (by simpa [mem_range] using he),smul_zero,map_zero]

lemma source_log (hx : den x=1) : logarithm x =
    ∑ j∈range (Fintype.card ι), (((-1:ℂ)^j)/(j+1:ℂ)) • (x-1)^(j+1) := by
  apply PowerSeries.ext; intro k
  rw [logarithm,PowerSeries.coeff_mk,map_sum,map_sum]; symm
  refine sum_subset (range_mono (by omega)) ?_
  intro i _ he
  rw [trunc_nil (by rw [map_sub,hx,map_one,sub_self]) (i+1) (by simp only [mem_range,not_lt] at he; omega),smul_zero,map_zero]
end Fin

section Transmit
variable (w) -- price parameter in output

def chain (x : Script B) (r : ℕ) (t : ℂ) : ℕ → Poly B -- overflow by power
  | 0 => 0
  | n+1 => chain x r t n * hist x r t+overflow (x^n) x r t

lemma powers (x : Script B) (r : ℕ) (t : ℂ) (k : ℕ) : hist x r t ^ k = hist (x^k) r t+chain x r t k := by
  induction k with
  | zero => simp [chain]
  | succ k ih =>
    rw [pow_succ,pow_succ,ih,add_mul,multiply,chain]; abel

def chainCost (w : ι→ℝ) (x : Script B) (r : ℕ) (b : ℝ) : ℕ→ℝ
  | 0 => 0
  | n+1 => chainCost w x r b n * b+cost w (x^n) x r

variable {w}
variable (hw : ∀ i, 0<w i)
include hw

lemma overflow_powers (r : ℕ) {t : ℂ} (ht : ‖t‖≤1) (k : ℕ) (A : ℝ) (h : Poly.price w (hist x r t) ≤ A) :
    Poly.price w (chain x r t k) ≤ ‖t‖^(r+1)*chainCost w x r A k := by
  induction k with
  | zero => simp [chain,chainCost]
  | succ k ih =>
    rw [chain]
    apply (Poly.addition hw ..).trans
    have he := (mul_le_mul ih h (Poly.nonnegative hw _) ((Poly.nonnegative hw _).trans ih))
    refine le_trans (add_le_add ((Poly.multiplication hw ..).trans he) (overflow_cost hw ht ..)) (le_of_eq ?_)
    rw [chainCost]; ring

lemma powerCompare (U W : Poly B) (C : ℝ) (hU : Poly.price w U ≤ C) (hW : Poly.price w W ≤ C) (k : ℕ) :
    Poly.price w (U^(k+1)-W^(k+1)) ≤ (k+1:ℕ)*C^k * Poly.price w (U-W) := by
  have hC : 0≤C := le_trans (Poly.nonnegative hw _) hU
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show U^(k+1+1)-W^(k+1+1)=(U^(k+1)-W^(k+1))*U + (U-W)*W^(k+1) by ring]
    apply (Poly.addition hw ..).trans
    have hp : Poly.price w (W^(k+1)) ≤ C^(k+1) := (Poly.powers hw ..).trans
      (pow_le_pow_left₀ (Poly.nonnegative hw _) hW _)
    refine le_trans (add_le_add ((Poly.multiplication hw ..).trans <|
      mul_le_mul ih hU (Poly.nonnegative hw _) ((Poly.nonnegative hw _).trans ih))
      ((Poly.multiplication hw ..).trans (mul_le_mul_of_nonneg_left hp (Poly.nonnegative hw _)))) ?_
    exact le_of_eq (by push_cast; ring)

end Transmit

section Bound
variable {r : ℕ} {t : ℂ} [Fintype ι]

def nilError (x : Script B) (r : ℕ) (t : ℂ) :=
    ∑ i∈range (Fintype.card ι), (((-1:ℂ)^i)/(i+1:ℂ)) • chain (x-1) r t (i+1)

omit [Fintype ι] in
lemma hist_unit (hx : den x=1) : (hist x r t).part B.quiet=1 := by
  rw [hist_den,hx]
  unfold solo; rw [sum_eq_single 0]; simp
  · intro i _ hi; rw [coeff_one,if_neg hi,mul_zero]
  simp

lemma unit_log_difference (hx : den x=1) :
    connected (hist x r t) = hist (logarithm x) r t + nilError x r t := by
  rw [connected_eq_logTable (hist_unit hx),logTable,source_log hx,hist_sum]
  unfold nilError; rw [← Finset.sum_add_distrib]
  apply sum_congr rfl; intro i _; rw [show hist x r t-1=hist (x-1) r t from by rw [hist_sub,hist_one],Evaluation.powers]
  rw [smul_add,hist_smul]


lemma log_control {U V : Poly B} (hw : ∀ i,0<w i) (hU : U.part B.quiet=1) (hV : V.part B.quiet=1) (C : ℝ)
    (h : Poly.price w (U-1) ≤ C) (hh : Poly.price w (V-1) ≤ C) :
    Poly.price w (connected U-connected V) ≤
      (∑ i∈range (Fintype.card ι),C^i)*Poly.price w (U-V) := by
  rw [connected_eq_logTable hU, connected_eq_logTable hV]
  unfold logTable; rw [← Finset.sum_sub_distrib]
  apply (Poly.batch hw ..).trans
  rw [sum_mul]; apply sum_le_sum; intro i _
  rw [← smul_sub, Poly.adapted,norm_div,norm_pow,norm_neg,norm_one,one_pow,one_div,← Nat.cast_add_one,Complex.norm_natCast]
  have he := powerCompare (w:=w) hw (U-1) (V-1) C h hh i
  refine (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ?_
  rw [sub_sub_sub_cancel_right, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by positivity),one_mul]

def logCosts (w : ι → ℝ) (x : Script B) (r : ℕ) (C : ℝ) :=
    ∑ i∈range (Fintype.card ι), (((i+1:ℕ):ℝ)⁻¹) * chainCost w (x-1) r C (i+1)

lemma log_error_price (hw : ∀ i,0<w i) (x : Script B) (ht : ‖t‖≤1)
    (C : ℝ) (h : Poly.price w (hist x r t - 1) ≤ C) :
    Poly.price w (nilError x r t) ≤ ‖t‖^(r+1) * logCosts w x r C := by
  apply (Poly.batch hw ..).trans
  rw [logCosts,mul_sum]; apply sum_le_sum; intro i _
  rw [Poly.adapted,norm_div,norm_pow,norm_neg,norm_one,one_pow,one_div,← Nat.cast_add_one,Complex.norm_natCast,
    mul_left_comm (‖t‖^(r+1))]
  exact mul_le_mul_of_nonneg_left (overflow_powers hw r ht (i+1) C (by rw [hist_sub,hist_one]; exact h)) (by positivity)

/-- Price AFTER division budget on the actual field. -/
theorem after_division {v : Poly B} (hv : v.part B.quiet≠0) (hx : basepoint x ≠ 0)
    (hw : ∀ i,0<w i) (ht : ‖t‖≤1)
    (C b : ℝ) (hq : Poly.price w (hist (Grade.quotient x) r t-1) ≤ C)
    (hc : Poly.price w (divideAway v - 1) ≤ C)
    (hp : Poly.price w (divideAway v - hist (Grade.quotient x) r t) ≤ b) :
    let Q := Grade.quotient x
    Poly.price w (connected (divideAway v) - hist (logarithm Q) r t) ≤
      (∑ i∈ range (Fintype.card ι), C^i) * b + ‖t‖^(r+1) * logCosts w Q r C := by
  intro Q
  let Z := divideAway v
  let H := hist Q r t
  have hz := remains_one hv
  have hQ : den Q=1 := den_quotient hx
  have hh : H.part B.quiet = 1 := hist_unit hQ
  have hC : 0≤C := (Poly.nonnegative hw _).trans hc
  have he := unit_log_difference (r:=r) (t:=t) hQ
  rw [show connected Z - hist (logarithm Q) r t =
    connected Z - connected H + nilError Q r t by unfold H; rw [he]; abel]
  exact (Poly.addition hw ..).trans (add_le_add ((log_control hw hz hh C hc hq).trans <|
    mul_le_mul_of_nonneg_left hp (sum_nonneg fun i _ => pow_nonneg hC _)) (log_error_price hw Q ht C hq))
end Bound
end YM.RG02.Evaluation
