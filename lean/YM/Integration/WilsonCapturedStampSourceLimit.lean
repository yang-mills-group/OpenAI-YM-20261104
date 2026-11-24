import YM.Integration.WilsonCapturedNativeClockFare

/-! The actual funded source on a finite angular stage, with one numerical roof
chosen before all trigonometric coefficients and both physical regulators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedStampSourceLimit
open Filter Finset Lattice RG WilsonCapturedSourceAngularRoof WilsonOriginalSuspendedTensor
open scoped Classical BigOperators
local notation "spend" => WilsonCapturedCoveredSourceWage.fare

def cap (G:Gauge)(s:ℕ):ℝ:=∑i∈range (s+1),∑r∈range (s+1),|roof G i r 1|
theorem positive (G:Gauge)(s:ℕ):0 ≤ cap G s:=by unfold cap;positivity

theorem paid (G:Gauge){s q:ℕ}(fit:q ≤ s)(r:ℕ){σ C B H:ℝ}(sp:0 < σ)(pc:0 ≤ C)(bill:C ≤ B)
    (income:Real.exp ((min 1 σ)⁻¹^2) ≤ H)(ramp:Real.exp (σ/4) ≤ (16*B)^2):
    (∑i∈range (q+1),spend G i r σ C) ≤ 256*B^3*H*cap G s:=by
  have hB:=pc.trans bill
  have hH:0 ≤ H:=(Real.exp_pos _).le.trans income
  have l:Real.exp (σ/4)*C ≤ 256*B^3:=by
    calc
      _ ≤ (16*B)^2*B:=mul_le_mul ramp bill pc (by positivity)
      _=_:=by ring
  have row (i:ℕ)(live:i∈range (q+1)):spend G i r σ C ≤ 256*B^3*H*(∑u∈range (s+1),|roof G i u 1|):=by
    by_cases rank:r ≤ i
    · have one:|roof G i r 1| ≤ ∑u∈range (s+1),|roof G i u 1|:=
        Finset.single_le_sum (f:=fun u=>|roof G i u 1|) (fun _ _=>abs_nonneg _)
          (mem_range_succ_iff.mpr (rank.trans ((mem_range_succ_iff.mp live).trans fit)))
      calc
        _ ≤ (Real.exp (σ/4)*C)*(roof G i r 1*H):=WilsonCapturedNativeClockFare.fare G i r sp pc income
        _ ≤ (Real.exp (σ/4)*C)*((∑u∈range (s+1),|roof G i u 1|)*H):=by gcongr;exact (le_abs_self _).trans one
        _ ≤ (256*B^3)*((∑u∈range (s+1),|roof G i u 1|)*H):=mul_le_mul_of_nonneg_right l (by positivity)
        _=_:=by ring
    · letI : IsEmpty (Fin r ↪ Fin i):=⟨fun u=>rank (by simpa using Fintype.card_le_of_injective u u.injective)⟩
      simp only [WilsonCapturedCoveredSourceWage.fare,Fintype.card_eq_zero,mul_zero,Nat.cast_zero,zero_mul];positivity
  calc
    _ ≤ ∑i∈range (q+1),256*B^3*H*(∑u∈range (s+1),|roof G i u 1|):=sum_le_sum row
    _=256*B^3*H*(∑i∈range (q+1),∑u∈range (s+1),|roof G i u 1|):=by rw [Finset.mul_sum]
    _ ≤ _:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _=>by positivity)

end YM.Integration.WilsonCapturedStampSourceLimit
