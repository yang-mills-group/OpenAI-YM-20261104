import YM.Next.FREE_KERNELS.Current
/-!
# Uniformity under iteration at virtual fixed factor: projection by spatial moments

Width paid on both sides. These estimates independent of block ratio even at repeated uses. Allows Schur identity to be used for comparing differential precisions whose last windows agree in their Steps, without full metric agreement. Using the PURE metric `pink` in all actual and virtual hierarchy uses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate
namespace Frequency
open Finset
lemma updated_size (x:Cover)(i:Axis)(b:ℤ): size (update x i b)+ (x i).natAbs = size x + b.natAbs:=by
    unfold size; rw [← add_sum_erase _ _ (mem_univ i),← add_sum_erase _ (fun j=> (x j).natAbs) (mem_univ i), update_self]
    have he(j)(hj:j∈univ.erase i) : (update x i b j).natAbs=(x j).natAbs:=by rw [update_of_ne (ne_of_mem_erase hj)]
    rw [sum_congr rfl he]; omega
lemma ret (s:ℝ) (x:Cover)(i:Axis)(b:ℤ) : envelopeW s (update x i b) = Real.exp (s*((b.natAbs:ℝ)-(x i).natAbs))*envelopeW s x:= by
    unfold envelopeW; rw [← Real.exp_add]; congr 1; have he : ((size (update x i b):ℕ):ℝ)+(x i).natAbs=size x+(b.natAbs:ℝ):=by exact_mod_cast updated_size x i b
    linarith only [mul_eq_mul_left_iff.mpr (show _=_ ∨ s=0 from Or.inl he)]
lemma interval_dense (k:Axis)(x:Cover)(b:ℤ)(n:ℕ)(η:ℝ): Width η (∑ i∈ Finset.range n,envelopeW η (update x k (b+i))) (intervalAxis k x b n):=by
   induction n with
   | zero=> simp [Width,intervalAxis,SumBudget]
   | succ n ih =>
     have hh : intervalAxis k x b (n+1)=fun i=> intervalAxis k x b n i + token (update x k (b+n)) i:= by funext i; unfold intervalAxis; rw [Finset.sum_range_succ]
     rw [hh,Finset.sum_range_succ]; exact Width.add_line ih (token_rate ..)
-- telescopes price bounds
lemma up_fare (k:Axis)(x:Cover)(s:ℝ)(t:ℕ):
    (∑ i∈ Finset.range t,envelopeW s (update x k i))*(Real.exp s-1)= envelopeW s (update x k t)-envelopeW s (update x k 0):=by
    induction t with
    | zero=>simp
    | succ n ih=>
      have he: envelopeW s (update x k ((n+1:ℕ):ℤ))=envelopeW s (update x k n)*Real.exp s:=by
         rw [ret,ret]; simp only [Int.natAbs_natCast];rw [mul_right_comm, ← Real.exp_add]; push_cast; ring_nf
      rw [Finset.sum_range_succ,add_mul,ih,he];ring
lemma down_fare (k:Axis)(x:Cover)(s:ℝ)(b n:ℕ)(hb:n ≤ b):
   (∑ i∈ Finset.range n,envelopeW s (update x k (-(b:ℤ)+i)))*(1-Real.exp (-s))=envelopeW s (update x k (-(b:ℤ)))-envelopeW s (update x k (-(b:ℤ)+n)):=by
    induction n with
    | zero=>simp
    | succ n ih=>
      have he: envelopeW s (update x k (-(b:ℤ)+((n+1:ℕ):ℤ)))=envelopeW s (update x k (-(b:ℤ)+n))*Real.exp (-s):=by
        rw [ret,ret,mul_right_comm,← Real.exp_add]; congr 2
        have hx : ((-(b:ℤ)+((n+1:ℕ):ℤ)).natAbs:ℝ)=((-(b:ℤ)+(n:ℤ)).natAbs:ℝ)-1:=by
           have hy: (-(b:ℤ)+((n+1:ℕ):ℤ)).natAbs+1= (-(b:ℤ)+(n:ℤ)).natAbs := by omega
           have hv:= congr_arg (fun i:ℕ=>(i:ℝ)) hy; push_cast at hv ⊢; linarith
        rw [hx]; ring
      rw [Finset.sum_range_succ,add_mul, ih (by omega), he];ring
lemma advance_tariff (η:ℝ)(he:0<η)(k:Axis): Tariff (partAxis k) η η ((Real.exp η-1)⁻¹+(1-Real.exp (-η))⁻¹) := by
    intro x
    unfold partAxis
    have hx : 0 < Real.exp η-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr he)
    have hy: 0 < 1-Real.exp (-η) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    let n:ℕ := (x k).natAbs
    have hp:0< envelopeW η x:= Real.exp_pos _
    by_cases h:0 ≤ x k; simp only [if_pos h]
    · apply (interval_dense _ _ _ _ _).mono le_rfl; simp only [zero_add]
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (inv_pos.mpr hy).le) hp.le)
      rw [inv_mul_eq_div]; apply (le_div_iff₀ hx).mpr; rw [up_fare]
      rw [show ((x k).natAbs:ℤ)= x k by omega, update_eq_self]; exact sub_le_self _ (Real.exp_nonneg _)
    simp only [if_neg h]; have hq := Width.scale_line (-1) (interval_dense k x (x k) n η); simp only [norm_neg,norm_one,neg_one_mul,one_mul] at hq; apply hq.mono le_rfl; apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (inv_pos.mpr hx).le) hp.le)
    rw [inv_mul_eq_div]; apply (le_div_iff₀ hy).mpr; rw [show x k=-(n:ℤ) by unfold n; omega,down_fare k x η n n le_rfl, show update x k (-(n:ℤ))= x by rw [show -(n:ℤ)=x k by unfold n; omega,update_eq_self]]; exact sub_le_self _ (Real.exp_nonneg _)
end Frequency
end YM.Next.Free
