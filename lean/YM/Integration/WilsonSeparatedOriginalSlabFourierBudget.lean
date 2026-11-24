import YM.Integration.WilsonSeparatedOriginalSlabFourierScore
import YM.Integration.WilsonSeparatedOriginalSlabFourierLattice

/-! A dimension-sharp reserve for all true angular directions, bought by one fixed spatial order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierBudget
open Finset Function UnitAddTorus WilsonSeparatedOriginalSlabFourierOrbit WilsonSeparatedOriginalSlabFourierLattice
open scoped Topology BigOperators Classical ContDiff
variable {J:Type*}[Fintype J]

theorem mode (F:C(UnitAddTorus J,ℂ))(regular:ContDiff ℝ ∞ (fun x:J→ℝ=>F (wrap x)))
    (n:ℕ){B:ℝ}(hB:0≤B)(lower:∀x,‖F x‖≤B)(upper:∀x,‖iteratedFDeriv ℝ n (fun y:J→ℝ=>F (wrap y)) x‖≤B)(k:J→ℤ):
    ‖mFourierCoeff F k‖*height k^n≤ B*(1+(Fintype.card J:ℝ))^n:=by
  by_cases hz:k=0
  · subst k; have c:=WilsonSeparatedOriginalSlabFourierScore.bounded F (0:J→ℤ) B lower
    have unit:height (0:J→ℤ)=1:=by simp [height]
    simp only [unit,one_pow,mul_one]
    exact c.trans (le_mul_of_one_le_right hB (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
  obtain ⟨v,hv⟩:=Function.ne_iff.mp hz
  change k v≠0 at hv
  have integer:(1:ℤ)≤|k v|:=by have amount:=abs_pos.mpr hv; omega
  have realunit:(1:ℝ)≤|(k v:ℝ)|:=by exact_mod_cast integer
  obtain ⟨i,_,high⟩:=Finset.exists_max_image Finset.univ (fun j:J=>|(k j:ℝ)|) ⟨v,Finset.mem_univ v⟩
  have large:1≤|(k i:ℝ)|:=realunit.trans (high v (Finset.mem_univ v))
  have ni:k i≠0:=by intro he;rw [he,Int.cast_zero,abs_zero] at large;norm_num at large
  have cost:=WilsonSeparatedOriginalSlabFourierScore.priced F regular n B hB upper k i ni
  have scale:height k≤(1+(Fintype.card J:ℝ))*|(k i:ℝ)|:=by
    unfold height
    have h:=Finset.sum_le_sum (s:=Finset.univ) high
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
    nlinarith
  calc
    ‖mFourierCoeff F k‖*height k^n ≤ ‖mFourierCoeff F k‖*((1+(Fintype.card J:ℝ))*|(k i:ℝ)|)^n:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (active k)) scale n) (norm_nonneg _)
    _=(‖mFourierCoeff F k‖*|(k i:ℝ)|^n)*(1+(Fintype.card J:ℝ))^n:=by rw [mul_pow]; ring
    _≤B*(1+(Fintype.card J:ℝ))^n:=mul_le_mul_of_nonneg_right cost (by positivity)

def order (J:Type*)[Fintype J](e:ℕ):ℕ:=e+(Fintype.card J+1)

def charge (J:Type*)[Fintype J](e:ℕ):ℝ:=
  (1+(Fintype.card J:ℝ))^(order J e)*(∑'k:J→ℤ,(height k^(Fintype.card J+1))⁻¹)

theorem original (F:C(UnitAddTorus J,ℂ))(regular:ContDiff ℝ ∞ (fun x:J→ℝ=>F (wrap x)))
    (e:ℕ){B:ℝ}(hB:0≤B)(lower:∀x,‖F x‖≤B)
    (upper:∀x,‖iteratedFDeriv ℝ (order J e) (fun y:J→ℝ=>F (wrap y)) x‖≤B):
    Summable (fun k:J→ℤ=>‖mFourierCoeff F k‖*height k^e) ∧
    ∑'k:J→ℤ,‖mFourierCoeff F k‖*height k^e≤B*charge J e:=by
  let c:=B*(1+(Fintype.card J:ℝ))^(order J e)
  have sized (k:J→ℤ):‖mFourierCoeff F k‖*height k^e≤c*(height k^(Fintype.card J+1))⁻¹:=by
    rw [←div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le (active k)) _)).mpr
    simpa only [mul_assoc,←pow_add,order,c] using mode F regular (order J e) hB lower upper k
  have cash:Summable (fun k:J→ℤ=>c*(height k^(Fintype.card J+1))⁻¹):=(reserve J).mul_left c
  have all:=cash.of_nonneg_of_le (fun k=>mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans (active k)) _)) sized
  refine ⟨all,(all.tsum_le_tsum sized cash).trans_eq ?_⟩
  rw [tsum_mul_left,charge,←mul_assoc]

end YM.Integration.WilsonSeparatedOriginalSlabFourierBudget
